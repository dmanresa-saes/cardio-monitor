'use strict';

const HR_SERVICE = 'heart_rate';
const HR_MEASUREMENT = 'heart_rate_measurement';
const BATTERY_SERVICE = 'battery_service';
const BATTERY_LEVEL = 'battery_level';

const CHART_WINDOW_S = 300;   // last 5 min on screen
const HRV_WINDOW_S = 60;      // HRV over last 60 s of RR
const ALERT_HOLD_S = 10;      // out of range this long before alerting
const ALERT_COOLDOWN_S = 60;
const SESSIONS_KEY = 'cm.sessions';
const SETTINGS_KEY = 'cm.settings';

const $ = id => document.getElementById(id);

let device = null;
let session = null;        // { start, samples: [{t, bpm, rr: []}] }
let stopping = false;
let wakeLock = null;
let alertState = { since: null, last: 0 };
let timer = null;
let pendingReload = false;  // new app version waiting for the session to end

// ---------- storage ----------

function load(key, fallback) {
  try { return JSON.parse(localStorage.getItem(key)) ?? fallback; } catch { return fallback; }
}
function save(key, value) {
  try { localStorage.setItem(key, JSON.stringify(value)); return true; } catch { return false; }
}

const settings = Object.assign({ age: 52, hrmax: '', alertHigh: 150, alertLow: 40 }, load(SETTINGS_KEY, {}));

// ---------- parsing (Bluetooth SIG Heart Rate Measurement 0x2A37) ----------

function parseHeartRate(view) {
  const flags = view.getUint8(0);
  let i = 1;
  let bpm;
  if (flags & 0x01) { bpm = view.getUint16(i, true); i += 2; }
  else { bpm = view.getUint8(i); i += 1; }
  const contact = (flags & 0x04) ? Boolean(flags & 0x02) : null;
  if (flags & 0x08) i += 2;  // energy expended, unused
  const rr = [];
  if (flags & 0x10) {
    for (; i + 1 < view.byteLength; i += 2) rr.push(Math.round(view.getUint16(i, true) * 1000 / 1024));
  }
  return { bpm, contact, rr };
}

// ---------- metrics ----------

// Drop physiologically implausible RR, then values >20% off the window median
// (missed beats, ectopics, connection artifacts). Median, not previous value,
// so one bad first sample can't poison the rest.
function cleanRR(rr) {
  const valid = rr.filter(v => v >= 300 && v <= 2000);
  if (!valid.length) return valid;
  const sorted = [...valid].sort((a, b) => a - b);
  const median = sorted[Math.floor(sorted.length / 2)];
  return valid.filter(v => Math.abs(v - median) / median <= 0.2);
}

function hrv(rr) {
  const r = cleanRR(rr);
  if (r.length < 10) return null;
  let sumSq = 0;
  for (let i = 1; i < r.length; i++) sumSq += (r[i] - r[i - 1]) ** 2;
  const mean = r.reduce((a, b) => a + b, 0) / r.length;
  const variance = r.reduce((a, b) => a + (b - mean) ** 2, 0) / (r.length - 1);
  return { rmssd: Math.sqrt(sumSq / (r.length - 1)), sdnn: Math.sqrt(variance) };
}

// Full short-term HRV report for a resting measurement.
function hrvReport(rawRR) {
  const r = cleanRR(rawRR);
  if (r.length < 30) return null;
  const diffs = r.slice(1).map((v, i) => v - r[i]);
  const mean = r.reduce((a, b) => a + b, 0) / r.length;
  const sdnn = Math.sqrt(r.reduce((a, b) => a + (b - mean) ** 2, 0) / (r.length - 1));
  const rmssd = Math.sqrt(diffs.reduce((a, d) => a + d * d, 0) / diffs.length);
  const dMean = diffs.reduce((a, b) => a + b, 0) / diffs.length;
  const sdDiff = Math.sqrt(diffs.reduce((a, d) => a + (d - dMean) ** 2, 0) / (diffs.length - 1));
  const sd1 = sdDiff / Math.SQRT2;
  const sd2 = Math.sqrt(Math.max(0, 2 * sdnn ** 2 - sd1 ** 2));
  return {
    hr: Math.round(60000 / mean),
    rmssd, ln: Math.log(rmssd), sdnn,
    pnn50: diffs.filter(d => Math.abs(d) > 50).length / diffs.length * 100,
    sd1, sd2,
    n: r.length,
    artifacts: (rawRR.length - r.length) / Math.max(1, rawRR.length) * 100,
    rr: r,
  };
}

function summarize(samples) {
  const bpms = samples.map(s => s.bpm).filter(b => b > 0);
  if (!bpms.length) return null;
  const rr = samples.flatMap(s => s.rr);
  return {
    avg: Math.round(bpms.reduce((a, b) => a + b, 0) / bpms.length),
    max: Math.max(...bpms),
    min: Math.min(...bpms),
    hrv: hrv(rr),
  };
}

function hrMax() {
  return Number(settings.hrmax) || (220 - Number(settings.age || 40));
}

const ZONES = [
  { name: 'Reposo', pct: 0, color: '--z0' },
  { name: 'Z1 Muy suave', pct: 0.5, color: '--z1' },
  { name: 'Z2 Suave', pct: 0.6, color: '--z2' },
  { name: 'Z3 Moderada', pct: 0.7, color: '--z3' },
  { name: 'Z4 Intensa', pct: 0.8, color: '--z4' },
  { name: 'Z5 Máxima', pct: 0.9, color: '--z5' },
];

function zoneFor(bpm) {
  const p = bpm / hrMax();
  let z = ZONES[0];
  for (const zone of ZONES) if (p >= zone.pct) z = zone;
  return z;
}

// ---------- bluetooth ----------

// Android's GATT stack sometimes never resolves a connect; fail fast instead of hanging.
function withTimeout(promise, ms) {
  return Promise.race([
    promise,
    new Promise((_, reject) => setTimeout(() => reject(new Error('el sensor no responde')), ms)),
  ]);
}

async function connect() {
  try {
    setStatus('Elige el H6 en la lista…', false);
    device = await navigator.bluetooth.requestDevice({
      filters: [{ services: [HR_SERVICE] }],
      optionalServices: [BATTERY_SERVICE],
    });
    device.addEventListener('gattserverdisconnected', onDisconnected);
    await startStream();
    session = { start: Date.now(), samples: [] };
    stopping = false;
    timer = setInterval(tick, 1000);
    requestWakeLock();
    $('connect').hidden = true;
    $('disconnect').hidden = false;
  } catch (err) {
    if (device?.gatt.connected) device.gatt.disconnect();
    if (err.name === 'NotFoundError') { setStatus('Desconectado', false); return; }
    setStatus('No conecta', false);
    $('alert').hidden = false;
    $('alert').textContent = `No se pudo conectar (${err.message}). Comprueba que el H6 no está emparejado ` +
      'en Ajustes > Bluetooth del móvil ni conectado a otra app, y vuelve a pulsar Conectar.';
  }
}

async function startStream() {
  setStatus('Conectando…', false);
  const connectAll = async () => {
    const server = await device.gatt.connect();
    const svc = await server.getPrimaryService(HR_SERVICE);
    const ch = await svc.getCharacteristic(HR_MEASUREMENT);
    ch.addEventListener('characteristicvaluechanged', e => onMeasurement(parseHeartRate(e.target.value)));
    await ch.startNotifications();
    return server;
  };
  const server = await withTimeout(connectAll(), 20000);
  setStatus(device.name || 'Conectado', true);
  $('alert').hidden = true;
  readBattery(server);
}

async function readBattery(server) {
  try {
    const svc = await server.getPrimaryService(BATTERY_SERVICE);
    const ch = await svc.getCharacteristic(BATTERY_LEVEL);
    $('battery').textContent = (await ch.readValue()).getUint8(0);
  } catch { /* battery service optional */ }
}

async function onDisconnected() {
  if (stopping || !session) return;
  for (let attempt = 1; attempt <= 5; attempt++) {
    setStatus(`Reconectando (${attempt}/5)…`, false);
    await new Promise(r => setTimeout(r, attempt * 2000));
    if (stopping) return;
    try { await startStream(); return; } catch { /* retry */ }
  }
  setStatus('Conexión perdida', false);
  stop();
}

function stop() {
  stopping = true;
  clearInterval(timer);
  stopBeat();
  if (device?.gatt.connected) device.gatt.disconnect();
  releaseWakeLock();
  if (session && session.samples.length > 5) {
    const sessions = load(SESSIONS_KEY, []);
    sessions.unshift({ start: session.start, end: Date.now(), samples: session.samples });
    if (!save(SESSIONS_KEY, sessions)) {
      // storage full: drop oldest sessions until it fits
      while (sessions.length > 1) { sessions.pop(); if (save(SESSIONS_KEY, sessions)) break; }
    }
  }
  session = null;
  setStatus('Desconectado', false);
  $('connect').hidden = false;
  $('disconnect').hidden = true;
  renderHistory();
  if (pendingReload) location.reload();
}

// ---------- live data ----------

// ---------- beating heart ----------

let beatInterval = 0;  // ms between beats, from the latest RR (or BPM if no RR)
let beatTimer = null;

function beatLoop() {
  if (!session || !beatInterval) { beatTimer = null; return; }
  const heart = $('heart');
  heart.classList.remove('beat');
  void heart.offsetWidth;  // restart the CSS animation
  heart.classList.add('beat');
  beatTimer = setTimeout(beatLoop, beatInterval);
}

function stopBeat() {
  clearTimeout(beatTimer);
  beatTimer = null;
  beatInterval = 0;
  $('heart').classList.remove('on', 'beat');
}

function onMeasurement({ bpm, contact, rr }) {
  if (!session) return;
  session.samples.push({ t: Date.now(), bpm, rr });
  const validRR = rr.filter(v => v >= 300 && v <= 2000);
  beatInterval = validRR.length ? validRR[validRR.length - 1] : bpm ? 60000 / bpm : 0;
  $('heart').classList.add('on');
  if (!beatTimer) beatLoop();
  $('bpm').textContent = bpm || '--';
  $('contact').textContent = contact === null ? 'n/d' : contact ? 'Sí' : 'No';
  const z = zoneFor(bpm);
  $('zone').textContent = `${z.name} · ${Math.round(bpm / hrMax() * 100)}%`;
  $('zone').style.background = `var(${z.color})`;
  checkAlert(bpm);
}

function tick() {
  if (!session) return;
  const now = Date.now();
  const s = Math.floor((now - session.start) / 1000);
  $('elapsed').textContent = `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')}`;

  const stats = summarize(session.samples);
  if (stats) {
    $('avg').textContent = stats.avg;
    $('max').textContent = stats.max;
    $('min').textContent = stats.min;
  }
  const recent = session.samples.filter(x => now - x.t < HRV_WINDOW_S * 1000).flatMap(x => x.rr);
  const h = hrv(recent);
  $('rmssd').textContent = h ? Math.round(h.rmssd) : '--';
  $('sdnn').textContent = h ? Math.round(h.sdnn) : '--';
  drawChart();
  restTick();
}

// ---------- resting HRV measurement ----------

const REST_RELAX_S = 60;
const REST_MEASURE_S = 180;
const READINGS_KEY = 'cm.readings';
let rest = null;  // { start, measureStart }

async function restStart() {
  if (!session) {
    await connect();
    if (!session) return;
  }
  rest = { start: Date.now(), measureStart: Date.now() + REST_RELAX_S * 1000 };
  $('restIdle').hidden = true;
  $('restResult').hidden = true;
  $('restRun').hidden = false;
  $('breath').classList.add('on');
  restTick();
}

function restCancel() {
  rest = null;
  $('restRun').hidden = true;
  $('restIdle').hidden = false;
  $('breath').classList.remove('on');
}

function restTick() {
  if (!rest) return;
  if (!session) { restCancel(); return; }
  const now = Date.now();
  const total = REST_RELAX_S + REST_MEASURE_S;
  const elapsed = (now - rest.start) / 1000;
  $('restProgress').value = Math.min(1, elapsed / total);
  const left = Math.max(0, Math.ceil(total - elapsed));
  if (now < rest.measureStart) {
    // 6 breaths/min: 5 s in, 5 s out (matches the CSS animation)
    $('breathText').textContent = elapsed % 10 < 5 ? 'Inspira' : 'Espira';
    $('restPhase').textContent = `Relájate y sigue el círculo · ${left} s`;
  } else {
    $('breath').classList.remove('on');
    $('breathText').textContent = 'Quieto';
    $('restPhase').textContent = `Midiendo… respira normal, sin moverte ni hablar · ${left} s`;
  }
  if (elapsed >= total) restFinish();
}

function restFinish() {
  const rr = session.samples.filter(s => s.t >= rest.measureStart).flatMap(s => s.rr);
  restCancel();
  const rep = hrvReport(rr);
  if (!rep) {
    showRestResult(null);
    return;
  }
  const reading = { t: Date.now(), ...rep };
  const readings = load(READINGS_KEY, []);
  reading.baseline = baselineOf(readings, reading.t);
  readings.unshift(reading);
  save(READINGS_KEY, readings.slice(0, 365));
  showRestResult(reading);
  renderReadings();
}

// Baseline = previous readings in the last 30 days (up to 7), on ln(RMSSD).
function baselineOf(readings, before) {
  const prev = readings.filter(r => r.t < before && before - r.t < 30 * 86400000).slice(0, 7);
  if (prev.length < 3) return null;
  const lns = prev.map(r => r.ln);
  const mean = lns.reduce((a, b) => a + b, 0) / lns.length;
  const sd = Math.sqrt(lns.reduce((a, b) => a + (b - mean) ** 2, 0) / (lns.length - 1));
  const hr = prev.reduce((a, r) => a + r.hr, 0) / prev.length;
  return { mean, sd: Math.max(sd, 0.05), hr, n: prev.length };
}

function interpret(r) {
  const msgs = [];
  if (r.artifacts > 5) msgs.push(['warn', `Calidad baja (${r.artifacts.toFixed(0)} % de latidos descartados). Humedece los electrodos, no te muevas y repite.`]);
  const b = r.baseline;
  if (!b) {
    msgs.push(['info', 'Necesito al menos 3 mediciones para conocer tu rango habitual. Mide cada mañana en la misma postura.']);
  } else {
    const z = (r.ln - b.mean) / b.sd;
    const lo = Math.exp(b.mean - b.sd), hi = Math.exp(b.mean + b.sd);
    const range = `tu rango: ${Math.round(lo)}–${Math.round(hi)} ms`;
    if (z < -1) msgs.push(['low', `HRV por debajo de tu rango habitual (${range}). Suele reflejar cansancio, estrés, poco sueño, alcohol o el inicio de un resfriado. Considera un día más suave.`]);
    else if (z > 1) msgs.push(['ok', `HRV por encima de tu rango habitual (${range}). Buena recuperación.`]);
    else msgs.push(['ok', `HRV dentro de tu rango habitual (${range}).`]);
    if (r.hr - b.hr >= 5) msgs.push(['low', `Pulso en reposo ${Math.round(r.hr - b.hr)} BPM por encima de tu media (${Math.round(b.hr)}).`]);
  }
  if (r.hr < 40 || r.hr > 100) msgs.push(['warn', `Pulso en reposo de ${r.hr} BPM fuera de lo habitual. Si se repite, coméntalo con tu médico.`]);
  return msgs;
}

function showRestResult(r) {
  $('restResult').hidden = false;
  if (!r) {
    $('restStats').innerHTML = '';
    $('restMsgs').innerHTML = '<p class="msg warn">No hubo suficientes latidos válidos. Revisa el contacto de la banda y repite.</p>';
    return;
  }
  const cell = (label, val, unit = '') => `<div><label>${label}</label><span>${val}</span><small>${unit}</small></div>`;
  $('restStats').innerHTML =
    cell('FC reposo', r.hr, 'BPM') + cell('RMSSD', Math.round(r.rmssd), 'ms') +
    cell('ln RMSSD', r.ln.toFixed(2)) + cell('SDNN', Math.round(r.sdnn), 'ms') +
    cell('pNN50', r.pnn50.toFixed(0), '%') + cell('SD1', Math.round(r.sd1), 'ms') +
    cell('SD2', Math.round(r.sd2), 'ms') + cell('Latidos', r.n);
  $('restMsgs').innerHTML = interpret(r).map(([cls, m]) => `<p class="msg ${cls}">${m}</p>`).join('');
  drawPoincare(r.rr);
}

function drawPoincare(rr) {
  const canvas = $('poincare');
  const dpr = window.devicePixelRatio || 1;
  const size = canvas.clientWidth;
  canvas.width = canvas.height = size * dpr;
  canvas.style.height = `${size}px`;
  const ctx = canvas.getContext('2d');
  ctx.scale(dpr, dpr);
  const css = getComputedStyle(document.documentElement);
  const lo = Math.min(...rr) - 50, hi = Math.max(...rr) + 50;
  const pad = 32;
  const p = v => pad + (v - lo) / (hi - lo) * (size - pad - 8);
  ctx.strokeStyle = css.getPropertyValue('--border');
  ctx.strokeRect(pad, 8, size - pad - 8, size - pad - 8);
  ctx.beginPath(); ctx.moveTo(p(lo), size - p(lo)); ctx.lineTo(p(hi), size - p(hi)); ctx.stroke();
  ctx.fillStyle = css.getPropertyValue('--muted');
  ctx.font = '11px system-ui';
  ctx.fillText(`${Math.round(lo)}`, pad, size - 18);
  ctx.fillText(`${Math.round(hi)} ms`, size - 52, size - 18);
  ctx.fillText('RR(n) →', size / 2 - 20, size - 4);
  ctx.save(); ctx.translate(12, size / 2 + 20); ctx.rotate(-Math.PI / 2); ctx.fillText('RR(n+1) →', 0, 0); ctx.restore();
  ctx.fillStyle = css.getPropertyValue('--accent');
  ctx.globalAlpha = 0.6;
  for (let i = 1; i < rr.length; i++) {
    ctx.beginPath();
    ctx.arc(p(rr[i - 1]), size - p(rr[i]), 2.5, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha = 1;
}

function renderReadings() {
  const readings = load(READINGS_KEY, []);
  const el = $('readings');
  el.innerHTML = '';
  $('trendWrap').hidden = readings.length < 2;
  if (!readings.length) { el.innerHTML = '<p class="empty">Sin mediciones todavía.</p>'; return; }
  readings.slice(0, 30).forEach((r, idx) => {
    const row = document.createElement('div');
    row.className = 'session';
    row.innerHTML = `<div class="info"><strong>${fmtDate(r.t)}</strong><br>
      <small>RMSSD ${Math.round(r.rmssd)} ms · FC ${r.hr} BPM · SDNN ${Math.round(r.sdnn)} ms</small></div>`;
    const view = document.createElement('button');
    view.className = 'small'; view.textContent = 'Ver';
    view.onclick = () => { showRestResult(r); $('restCard').scrollIntoView({ behavior: 'smooth' }); };
    const del = document.createElement('button');
    del.className = 'small'; del.textContent = 'Borrar';
    del.onclick = () => {
      if (del.dataset.confirm) {
        readings.splice(idx, 1); save(READINGS_KEY, readings); renderReadings();
      } else { del.dataset.confirm = '1'; del.textContent = '¿Seguro?'; }
    };
    row.append(view, del);
    el.append(row);
  });
  drawTrend(readings.slice(0, 30).reverse());
}

// RMSSD per day with the rolling normal band (baseline mean ± 1 SD) behind it.
function drawTrend(rs) {
  if (rs.length < 2) return;
  const canvas = $('trend');
  const dpr = window.devicePixelRatio || 1;
  const w = canvas.clientWidth, h = canvas.clientHeight;
  canvas.width = w * dpr; canvas.height = h * dpr;
  const ctx = canvas.getContext('2d');
  ctx.scale(dpr, dpr);
  const css = getComputedStyle(document.documentElement);
  const vals = rs.flatMap(r => [r.rmssd, ...(r.baseline ? [Math.exp(r.baseline.mean - r.baseline.sd), Math.exp(r.baseline.mean + r.baseline.sd)] : [])]);
  const lo = Math.max(0, Math.min(...vals) - 5), hi = Math.max(...vals) + 5;
  const pad = 28;
  const x = i => pad + i / (rs.length - 1) * (w - pad - 8);
  const y = v => h - 16 - (v - lo) / (hi - lo) * (h - 24);

  ctx.fillStyle = css.getPropertyValue('--z2');
  ctx.globalAlpha = 0.15;
  rs.forEach((r, i) => {
    if (!r.baseline || i === rs.length - 1) return;
    const b = r.baseline, nb = rs[i + 1].baseline || b;
    ctx.beginPath();
    ctx.moveTo(x(i), y(Math.exp(b.mean + b.sd)));
    ctx.lineTo(x(i + 1), y(Math.exp(nb.mean + nb.sd)));
    ctx.lineTo(x(i + 1), y(Math.exp(nb.mean - nb.sd)));
    ctx.lineTo(x(i), y(Math.exp(b.mean - b.sd)));
    ctx.fill();
  });
  ctx.globalAlpha = 1;

  ctx.fillStyle = css.getPropertyValue('--muted');
  ctx.font = '11px system-ui';
  ctx.fillText(Math.round(hi), 2, y(hi) + 10);
  ctx.fillText(Math.round(lo), 2, y(lo));
  ctx.fillText('RMSSD (ms) · banda verde = tu rango normal', pad, h - 2);

  ctx.strokeStyle = css.getPropertyValue('--accent');
  ctx.fillStyle = css.getPropertyValue('--accent');
  ctx.lineWidth = 2;
  ctx.beginPath();
  rs.forEach((r, i) => i ? ctx.lineTo(x(i), y(r.rmssd)) : ctx.moveTo(x(i), y(r.rmssd)));
  ctx.stroke();
  rs.forEach((r, i) => { ctx.beginPath(); ctx.arc(x(i), y(r.rmssd), 3, 0, Math.PI * 2); ctx.fill(); });
}

// ---------- alerts ----------

function checkAlert(bpm) {
  const high = Number(settings.alertHigh), low = Number(settings.alertLow);
  const out = bpm > 0 && ((high && bpm > high) || (low && bpm < low));
  const now = Date.now();
  if (!out) { alertState.since = null; $('alert').hidden = true; return; }
  alertState.since ??= now;
  if (now - alertState.since < ALERT_HOLD_S * 1000) return;
  $('alert').hidden = false;
  $('alert').textContent = `⚠ Pulso ${bpm > high ? 'por encima de ' + high : 'por debajo de ' + low} BPM desde hace ${Math.round((now - alertState.since) / 1000)} s`;
  if (now - alertState.last < ALERT_COOLDOWN_S * 1000) return;
  alertState.last = now;
  navigator.vibrate?.([300, 150, 300]);
  beep();
}

function beep() {
  try {
    const ctx = new AudioContext();
    const osc = ctx.createOscillator();
    osc.frequency.value = 880;
    osc.connect(ctx.destination);
    osc.start();
    osc.stop(ctx.currentTime + 0.4);
  } catch { /* audio blocked */ }
}

// ---------- chart ----------

function drawChart() {
  const canvas = $('chart');
  const dpr = window.devicePixelRatio || 1;
  const w = canvas.clientWidth, h = canvas.clientHeight;
  canvas.width = w * dpr; canvas.height = h * dpr;
  const ctx = canvas.getContext('2d');
  ctx.scale(dpr, dpr);
  ctx.clearRect(0, 0, w, h);

  const css = getComputedStyle(document.documentElement);
  const now = Date.now();
  // window grows with the session (min 30 s) so early data isn't squeezed to the right edge
  const windowMs = session ? Math.min(CHART_WINDOW_S * 1000, Math.max(30000, now - session.start)) : CHART_WINDOW_S * 1000;
  const pts = (session?.samples || []).filter(s => now - s.t < windowMs && s.bpm > 0);
  if (pts.length < 2) return;

  const bpms = pts.map(p => p.bpm);
  const lo = Math.max(30, Math.min(...bpms) - 10);
  const hi = Math.max(...bpms) + 10;
  const pad = 28;
  const x = t => pad + (1 - (now - t) / windowMs) * (w - pad);
  const y = b => h - 4 - (b - lo) / (hi - lo) * (h - 8);

  ctx.font = '11px system-ui';
  ctx.fillStyle = css.getPropertyValue('--muted');
  ctx.strokeStyle = css.getPropertyValue('--border');
  ctx.lineWidth = 1;
  const step = hi - lo > 60 ? 20 : 10;
  for (let b = Math.ceil(lo / step) * step; b <= hi; b += step) {
    ctx.beginPath(); ctx.moveTo(pad, y(b)); ctx.lineTo(w, y(b)); ctx.stroke();
    ctx.fillText(b, 2, y(b) + 4);
  }

  // each segment takes the colour of the zone it ends in
  ctx.lineWidth = 3;
  ctx.lineCap = 'round';
  for (let i = 1; i < pts.length; i++) {
    ctx.strokeStyle = css.getPropertyValue(zoneFor(pts[i].bpm).color);
    ctx.beginPath();
    ctx.moveTo(x(pts[i - 1].t), y(pts[i - 1].bpm));
    ctx.lineTo(x(pts[i].t), y(pts[i].bpm));
    ctx.stroke();
  }
}

function renderLegend() {
  const max = hrMax();
  $('legend').innerHTML = ZONES.map((z, i) => {
    const from = Math.round(z.pct * max);
    const to = i < ZONES.length - 1 ? Math.round(ZONES[i + 1].pct * max) - 1 : null;
    const range = i === 0 ? `<${Math.round(ZONES[1].pct * max)}` : to ? `${from}–${to}` : `${from}+`;
    return `<span><i style="background:var(${z.color})"></i>${z.name.replace(/^Z\d /, '')} ${range}</span>`;
  }).join('');
}

// ---------- history ----------

function fmtDate(ms) {
  return new Date(ms).toLocaleString('es-ES', { dateStyle: 'short', timeStyle: 'short' });
}

function renderHistory() {
  const sessions = load(SESSIONS_KEY, []);
  const el = $('history');
  el.innerHTML = '';
  if (!sessions.length) { el.innerHTML = '<p class="empty">Sin sesiones guardadas.</p>'; return; }
  sessions.forEach((s, idx) => {
    const st = summarize(s.samples);
    const mins = Math.round((s.end - s.start) / 60000);
    const row = document.createElement('div');
    row.className = 'session';
    row.innerHTML = `
      <div class="info">
        <strong>${fmtDate(s.start)}</strong> · ${mins} min<br>
        <small>Media ${st?.avg ?? '--'} · Máx ${st?.max ?? '--'} · Mín ${st?.min ?? '--'} BPM
        · RMSSD ${st?.hrv ? Math.round(st.hrv.rmssd) : '--'} ms</small>
      </div>`;
    const csv = document.createElement('button');
    csv.className = 'small'; csv.textContent = 'CSV';
    csv.onclick = () => exportCSV(s);
    const del = document.createElement('button');
    del.className = 'small'; del.textContent = 'Borrar';
    del.onclick = () => {
      if (del.dataset.confirm) {
        sessions.splice(idx, 1); save(SESSIONS_KEY, sessions); renderHistory();
      } else { del.dataset.confirm = '1'; del.textContent = '¿Seguro?'; }
    };
    row.append(csv, del);
    el.append(row);
  });
}

function exportCSV(s) {
  const lines = ['timestamp_iso,bpm,rr_ms'];
  for (const x of s.samples) lines.push(`${new Date(x.t).toISOString()},${x.bpm},${x.rr.join(' ')}`);
  const blob = new Blob([lines.join('\n')], { type: 'text/csv' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `cardio-${new Date(s.start).toISOString().slice(0, 16).replace(':', '')}.csv`;
  a.click();
  URL.revokeObjectURL(a.href);
}

// ---------- misc ----------

function setStatus(text, on) {
  $('status').textContent = text;
  $('status').className = `status ${on ? 'on' : 'off'}`;
}

async function requestWakeLock() {
  try { wakeLock = await navigator.wakeLock?.request('screen'); } catch { /* not critical */ }
}
function releaseWakeLock() { wakeLock?.release(); wakeLock = null; }
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && session) requestWakeLock();
});

function initSettings() {
  for (const key of ['age', 'hrmax', 'alertHigh', 'alertLow']) {
    const input = $(key);
    input.value = settings[key];
    input.addEventListener('change', () => { settings[key] = input.value; save(SETTINGS_KEY, settings); renderLegend(); });
  }
  renderLegend();
}

function unsupportedReason() {
  const ua = navigator.userAgent;
  const fix = 'Abre la app Chrome y escribe la dirección en su barra.';
  if (!isSecureContext) return `La página no está en HTTPS. Abre https://${location.host}${location.pathname}`;
  if (/SamsungBrowser/.test(ua)) return `Samsung Internet no soporta Bluetooth web. ${fix}`;
  if (/Firefox|FxiOS/.test(ua)) return `Firefox no soporta Bluetooth web. ${fix}`;
  if (navigator.brave) return 'Brave trae Bluetooth web desactivado. Usa Chrome o actívalo en brave://flags/#brave-web-bluetooth-api';
  if (/iPhone|iPad/.test(ua)) return 'En iPhone ningún navegador soporta Bluetooth web.';
  if (/; wv\)|FBAN|FBAV|Instagram|WhatsApp|Line\//.test(ua)) return `Estás en el navegador interno de otra app (WhatsApp, Gmail…). Menú ⋮ → "Abrir en Chrome".`;
  return `Este navegador no soporta Bluetooth web. ${fix} Si ya es Chrome, actualízalo.`;
}

function init() {
  initSettings();
  renderHistory();
  renderReadings();
  if (!navigator.bluetooth) {
    $('unsupported').hidden = false;
    $('unsupported').textContent = unsupportedReason();
    $('connect').disabled = true;
    $('restStart').disabled = true;
  }
  $('connect').onclick = connect;
  $('disconnect').onclick = stop;
  $('restStart').onclick = restStart;
  $('restCancel').onclick = restCancel;
  window.addEventListener('resize', () => session && drawChart());
  if ('serviceWorker' in navigator) {
    // Reload into a new version as soon as it's installed, but never mid-session.
    const hadController = !!navigator.serviceWorker.controller;
    navigator.serviceWorker.addEventListener('controllerchange', () => {
      if (!hadController) return;
      if (session) pendingReload = true; else location.reload();
    });
    navigator.serviceWorker.register('sw.js').then(reg => reg.update()).catch(() => {});
  }
}

init();
