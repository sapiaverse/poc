import {DURATION,dayOf,clock,latestIndex,activeAt,positionAt,filterEvents,parseHash,activityGroup,activityName,modeName,groupAt} from './model.js';

// Small DOM helpers.
const $ = id => document.getElementById(id);
function el(tag, cls, text) {
  const node = document.createElement(tag);
  if (cls) node.className = cls;
  if (text !== undefined && text !== null) node.textContent = String(text);
  return node;
}
function icon(name) {
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg'), use = document.createElementNS(svg.namespaceURI, 'use');
  svg.setAttribute('class', 'i'); svg.setAttribute('aria-hidden', 'true'); use.setAttribute('href', `#${name}`); svg.append(use);
  return svg;
}
// Text formatting helpers.
const pretty = s => String(s ?? '').replaceAll('_', ' ');
const sentence = s => { const text = pretty(s); return text.charAt(0).toUpperCase() + text.slice(1); };
const plural = (n, one, many = `${one}s`) => `${Number(n).toLocaleString('en-GB')} ${Number(n) === 1 ? one : many}`;
const clockEnd = t => t > 0 && t % 1440 === 0 ? '24:00' : clock(t);
const km = v => Number.isFinite(Number(v)) && v !== '' && v !== null ? `${Number(v).toFixed(1)} km` : 'distance not logged';
function duration(minutes) {
  const m = Math.round(Number(minutes));
  if (!Number.isFinite(m)) return '';
  if (m < 60) return `${m} min`;
  return m % 60 ? `${Math.floor(m / 60)} h ${m % 60} min` : `${m / 60} h`;
}
// Wording for trips.
const tripPurpose = r => `${r.activity && r.activity !== 'other' ? `for ${activityName(r.activity).toLowerCase()} ` : ''}at ${atPlace(r.dest_category)}`;
const tripLabel = mode => ({walk: 'Walking', bicycle: 'Cycling'})[mode] ?? `Travelling ${modeName(mode).toLowerCase()}`;
// Calendar labels. Day 1 of the replay is Monday 1 April.
const WEEKDAYS = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'];
const dateLabel = day => `${WEEKDAYS[day % 7]} ${day + 1} April`;
const PLAN_NAMES = {mandatory: 'Fixed commitments', medium_1: 'Draft plan', final_initial: 'Day plan', replan: 'Revised plan'};
const NEEDS = ['hunger', 'energy', 'safety', 'social'];
const SANS = '"Segoe UI Variable Text","Segoe UI",system-ui,sans-serif', SERIF = '"Sitka Text",Charter,Georgia,serif';
// Binary search for the first time later than t.
function firstAfter(times, t) {
  let lo = 0, hi = times.length;
  while (lo < hi) { const mid = (lo + hi) >> 1; if (times[mid] <= t) lo = mid + 1; else hi = mid; }
  return lo;
}

// App state, starting from the URL bookmark.
const initial = parseHash(location.hash);
const state = {id: initial.id, t: initial.t, playing: false, speed: 60, follow: false, kind: 'all', query: '', allDays: false, pastOnly: false};
let manifest = null, overview = null, city = null, detail = null, lookup = null, loadVersion = 0;
const cache = new Map(), rosterRows = new Map(), dayButtons = [];
const metrics = {started: performance.now(), ready: 0, frames: [], base: []};
const residentName = id => manifest?.agents[Number(id)]?.name ?? `Resident ${Number(id) + 1}`;

/* Theme. A stored choice wins; otherwise the system preference applies. */
const root = document.documentElement, darkQuery = matchMedia('(prefers-color-scheme: dark)'), reduceMotion = matchMedia('(prefers-reduced-motion: reduce)');
const THEME_KEY = 'exp001-replay-theme';
try { const saved = localStorage.getItem(THEME_KEY); if (saved === 'light' || saved === 'dark') root.dataset.theme = saved; } catch {}
// Saved splitter widths; style.css clamps them to the current window.
const COLUMNS = {roster: {prop: '--roster-w', key: 'exp001-replay-roster-w', max: 360}, panel: {prop: '--panel-w', key: 'exp001-replay-panel-w', max: 900}};
for (const {prop, key, max} of Object.values(COLUMNS)) {
  try { const px = Number(localStorage.getItem(key)); if (px >= 180 && px <= max) root.style.setProperty(prop, `${Math.round(px)}px`); } catch {}
}
let colors = null;
const isDark = () => root.dataset.theme ? root.dataset.theme === 'dark' : darkQuery.matches;
// Read the theme colours from the CSS variables.
function readColors() {
  const css = getComputedStyle(root), v = name => css.getPropertyValue(name).trim();
  colors = {map: v('--map'), water: v('--water'), road: v('--road'), label: v('--label'), halo: v('--halo'), ring: v('--dot-ring'), edge: v('--dot-edge'),
    ink: v('--ink'), ink2: v('--ink-2'), ink3: v('--ink-3'), ink4: v('--ink-4'), wash: v('--wash-2'), panel: v('--panel'),
    group: {sleep: v('--g-sleep'), routine: v('--g-routine'), work: v('--g-work'), out: v('--g-out'), travel: v('--g-travel'), unknown: v('--g-unknown')}};
}
// Repaint everything after a theme change.
function syncTheme() {
  readColors();
  const dark = isDark();
  $('themeToggle').querySelector('use').setAttribute('href', dark ? '#i-sun' : '#i-moon');
  $('themeToggle').setAttribute('aria-label', dark ? 'Use light theme' : 'Use dark theme');
  baseStale = true; drawRibbons(); requestDraw();
}

/* Map. World units: x = (lon - LON0) * cos(lat0), y = LAT0 - lat, so one unit is one degree of latitude. */
const K = Math.cos(41.89 * Math.PI / 180), LON0 = -87.64, LAT0 = 41.89;
const toWorld = (lon, lat) => [(lon - LON0) * K, LAT0 - lat];
const canvas = $('map'), ctx = canvas.getContext('2d');
const base = document.createElement('canvas'), bctx = base.getContext('2d');
const view = {w: 0, h: 0, dpr: 1}, cam = {x: 0, y: 0, s: 1, fit: 1, ready: false};
let baseCam = null, baseStale = true, lastBase = 0, settleTimer = 0, anim = null, points = [], hoverId = null;
// Convert map coordinates to screen pixels.
const sx = x => (x - cam.x) * cam.s + view.w / 2, sy = y => (y - cam.y) * cam.s + view.h / 2;

// Convert the roads to map units and work out the city bounds and area labels.
function prepareCity(raw) {
  const n = raw.roads.length, xy = new Float32Array(n * 4);
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (let i = 0; i < n; i++) {
    const r = raw.roads[i], j = i * 4;
    xy[j] = (r[0] - LON0) * K; xy[j + 1] = LAT0 - r[1]; xy[j + 2] = (r[2] - LON0) * K; xy[j + 3] = LAT0 - r[3];
    x0 = Math.min(x0, xy[j], xy[j + 2]); x1 = Math.max(x1, xy[j], xy[j + 2]);
    y0 = Math.min(y0, xy[j + 1], xy[j + 3]); y1 = Math.max(y1, xy[j + 1], xy[j + 3]);
  }
  // Lake Michigan lies east of the road network. The shading follows the easternmost road
  // end in each latitude band, widened to its neighbours, so it is approximate by design.
  const bands = 64, step = (y1 - y0) / bands, east = new Array(bands).fill(-Infinity);
  for (let j = 0; j < xy.length; j += 2) {
    const b = Math.min(bands - 1, Math.floor((xy[j + 1] - y0) / step));
    if (xy[j] > east[b]) east[b] = xy[j];
  }
  const shore = [];
  let last = x1;
  for (let b = 0; b < bands; b++) {
    let x = -Infinity;
    for (let k = Math.max(0, b - 1); k <= Math.min(bands - 1, b + 1); k++) x = Math.max(x, east[k]);
    if (!Number.isFinite(x)) x = last;
    last = x; shore.push([x + .0008, y0 + (b + .5) * step]);
  }
  // Busier neighbourhoods win label collisions: weight by recorded minutes spent there.
  const minutes = new Map();
  for (const agent of overview.agents) for (const r of agent.activities) minutes.set(r[5], (minutes.get(r[5]) ?? 0) + r[1] - r[0]);
  const areas = raw.areas.map(a => ({name: a.name, x: (a.lon - LON0) * K, y: LAT0 - a.lat, weight: minutes.get(a.name) ?? 0})).sort((a, b) => b.weight - a.weight);
  return {xy, x0, x1, y0, y1, shore, areas};
}
// Space kept clear for the map buttons and legend.
function mapPadding() { return {t: 24, r: 66, b: view.w > 700 ? 92 : 24, l: 24}; }
// Camera view that fits the whole city.
function fitTarget() {
  const pad = mapPadding(), s = Math.min((view.w - pad.l - pad.r) / (city.x1 - city.x0), (view.h - pad.t - pad.b) / (city.y1 - city.y0));
  return {x: (city.x0 + city.x1) / 2 - (pad.l - pad.r) / 2 / s, y: (city.y0 + city.y1) / 2 - (pad.t - pad.b) / 2 / s, s};
}
// Limit zoom to between 0.7x and 28x the whole-city view.
const clampScale = s => Math.max(cam.fit * .7, Math.min(cam.fit * 28, s));
// Screen areas covered by the map buttons and legend.
function overlayRects() {
  const box = canvas.getBoundingClientRect();
  return ['mapTools', 'legend'].map(id => $(id).getBoundingClientRect()).filter(r => r.width)
    .map(r => [r.left - box.left - 6, r.top - box.top - 6, r.right - box.left + 6, r.bottom - box.top + 6]);
}
// Draw roads, water and labels into a cached background layer.
function renderBase() {
  const started = performance.now();
  const m = Math.round(Math.max(view.w, view.h) * .25), bw = view.w + 2 * m, bh = view.h + 2 * m, dpr = Math.min(view.dpr, 1.5);
  const pw = Math.round(bw * dpr), ph = Math.round(bh * dpr);
  if (base.width !== pw || base.height !== ph) { base.width = pw; base.height = ph; }
  const s = cam.s, ox = bw / 2 - cam.x * s, oy = bh / 2 - cam.y * s, g = bctx;
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  g.fillStyle = colors.map; g.fillRect(0, 0, bw, bh);
  const shore = city.shore, top = (city.y0 - .5) * s + oy, bottom = (city.y1 + .5) * s + oy;
  g.fillStyle = colors.water; g.beginPath(); g.moveTo(bw + 10, top); g.lineTo(shore[0][0] * s + ox, top);
  for (const [x, y] of shore) g.lineTo(x * s + ox, y * s + oy);
  g.lineTo(shore[shore.length - 1][0] * s + ox, bottom); g.lineTo(bw + 10, bottom); g.closePath(); g.fill();
  // 162k segments go into one path; segments wholly outside the layer are skipped.
  const xy = city.xy, minX = -ox / s, maxX = (bw - ox) / s, minY = -oy / s, maxY = (bh - oy) / s;
  // At city scale the 162k segments merge into a grey mass, so they start faint and firm up with zoom.
  const zoom = Math.log2(Math.max(1, s / cam.fit));
  g.strokeStyle = colors.road; g.lineWidth = Math.min(1.5, .5 + .3 * zoom); g.globalAlpha = Math.min(1, .55 + .2 * zoom);
  g.beginPath();
  for (let j = 0; j < xy.length; j += 4) {
    const ax = xy[j], ay = xy[j + 1], bx = xy[j + 2], by = xy[j + 3];
    if ((ax < minX && bx < minX) || (ax > maxX && bx > maxX) || (ay < minY && by < minY) || (ay > maxY && by > maxY)) continue;
    g.moveTo(ax * s + ox, ay * s + oy); g.lineTo(bx * s + ox, by * s + oy);
  }
  g.stroke(); g.globalAlpha = 1;
  drawLabels(g, s, ox, oy, m, bw, bh);
  baseCam = {x: cam.x, y: cam.y, s, bw, bh}; baseStale = false; lastBase = performance.now();
  metrics.base.push(lastBase - started); if (metrics.base.length > 60) metrics.base.shift();
}
// Draw text with an outline so it stays readable on the map.
function haloText(g, text, x, y, fill, width = 3.5) {
  g.lineJoin = 'round'; g.lineWidth = width; g.strokeStyle = colors.halo; g.strokeText(text, x, y);
  g.fillStyle = fill; g.fillText(text, x, y);
}
// Place area labels so they do not overlap each other or the controls.
function drawLabels(g, s, ox, oy, m, bw, bh) {
  const placed = overlayRects().map(r => [r[0] + m, r[1] + m, r[2] + m, r[3] + m]), size = s > cam.fit * 2.5 ? 13 : 12;
  const hits = box => placed.some(b => box[0] < b[2] && box[2] > b[0] && box[1] < b[3] && box[3] > b[1]);
  g.textAlign = 'center'; g.textBaseline = 'middle';
  // Lake label sits mid-water at 45% of the visible height when there is room for it.
  const midY = m + view.h * .45, band = city.shore[Math.max(0, Math.min(city.shore.length - 1, Math.round(((midY - oy) / s - city.y0) / (city.y1 - city.y0) * city.shore.length - .5)))];
  const shoreX = Math.max(m, band[0] * s + ox), right = m + view.w;
  if (right - shoreX > 140) {
    g.font = `italic 15px ${SERIF}`;
    const x = (shoreX + right) / 2, w = g.measureText('Lake Michigan').width, box = [x - w / 2 - 8, midY - 12, x + w / 2 + 8, midY + 12];
    if (!hits(box)) { g.fillStyle = colors.ink3; g.fillText('Lake Michigan', x, midY); placed.push(box); }
  }
  g.font = `italic ${size}px ${SERIF}`;
  for (const area of city.areas) {
    const x = area.x * s + ox, y = area.y * s + oy, w = g.measureText(area.name).width;
    const box = [x - w / 2 - 6, y - size * .7 - 3, x + w / 2 + 6, y + size * .7 + 3];
    if (box[0] < 4 || box[2] > bw - 4 || box[1] < 4 || box[3] > bh - 4 || hits(box)) continue;
    haloText(g, area.name, x, y, colors.label); placed.push(box);
  }
}
// Whether the cached background still covers the current view.
function covered() {
  const r = cam.s / baseCam.s, dx = view.w / 2 - baseCam.bw / 2 * r + (baseCam.x - cam.x) * cam.s, dy = view.h / 2 - baseCam.bh / 2 * r + (baseCam.y - cam.y) * cam.s;
  return r > .55 && r < 2.2 && dx <= .5 && dy <= .5 && dx + baseCam.bw * r >= view.w - .5 && dy + baseCam.bh * r >= view.h - .5;
}
// Draw one frame of the map.
function drawMap() {
  if (!city || !overview || !view.w || !cam.ready) return;
  const started = performance.now();
  if (!baseCam || baseStale || (!covered() && started - lastBase > 90)) renderBase();
  ctx.setTransform(view.dpr, 0, 0, view.dpr, 0, 0);
  ctx.fillStyle = colors.map; ctx.fillRect(0, 0, view.w, view.h);
  const r = cam.s / baseCam.s;
  ctx.drawImage(base, view.w / 2 - baseCam.bw / 2 * r + (baseCam.x - cam.x) * cam.s, view.h / 2 - baseCam.bh / 2 * r + (baseCam.y - cam.y) * cam.s, baseCam.bw * r, baseCam.bh * r);
  drawTrips(); drawDots();
  metrics.frames.push(performance.now() - started); if (metrics.frames.length > 300) metrics.frames.shift();
}
// Draw one straight line.
function segment(a, b, color, width, dash, alpha) {
  ctx.globalAlpha = alpha; ctx.strokeStyle = color; ctx.lineWidth = width; ctx.setLineDash(dash);
  ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke();
  ctx.globalAlpha = 1; ctx.setLineDash([]);
}
function drawTrips() {
  // The selected resident's trips today: done solid, under way partly drawn, still to come dashed.
  const agent = overview.agents[state.id], lo = dayOf(state.t) * 1440, t = state.t, ends = new Map();
  ctx.lineCap = 'round';
  for (const trip of agent.trips) {
    if (trip[0] < lo || trip[0] >= lo + 1440) continue;
    const [ax, ay] = toWorld(trip[2], trip[3]), [bx, by] = toWorld(trip[4], trip[5]), a = [sx(ax), sy(ay)], b = [sx(bx), sy(by)];
    ends.set(`${a[0].toFixed(1)},${a[1].toFixed(1)}`, a); ends.set(`${b[0].toFixed(1)},${b[1].toFixed(1)}`, b);
    if (trip[1] <= t) segment(a, b, colors.ink2, 2, [], .7);
    else if (trip[0] <= t) {
      const f = (t - trip[0]) / Math.max(.001, trip[1] - trip[0]), p = [a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f];
      segment(a, p, colors.ink, 2.4, [], 1); segment(p, b, colors.ink2, 1.6, [4, 4], .7);
    } else segment(a, b, colors.ink3, 1.4, [3, 5], .6);
  }
  for (const [x, y] of ends.values()) {
    ctx.beginPath(); ctx.arc(x, y, 3, 0, Math.PI * 2); ctx.fillStyle = colors.map; ctx.fill();
    ctx.lineWidth = 1.4; ctx.strokeStyle = colors.ink2; ctx.stroke();
  }
}
const placeLabel = p => !p ? 'No record yet' : p.kind === 'trip' ? tripLabel(p.trip[6]) : p.kind === 'activity' ? activityName(p.activity[4]) : 'No activity recorded';
const spanLabel = p => { const row = p?.trip ?? p?.activity; return row ? `${clock(row[0])}–${clockEnd(row[1])}` : ''; };
// Draw one resident dot. A hollow dot means no known activity.
function dot(d, r, ringed) {
  ctx.beginPath(); ctx.arc(d.x, d.y, r, 0, Math.PI * 2);
  if (d.g === 'unknown') { ctx.fillStyle = colors.map; ctx.fill(); ctx.lineWidth = 1.7; ctx.strokeStyle = colors.group.unknown; ctx.stroke(); }
  else {
    ctx.fillStyle = colors.group[d.g]; ctx.fill(); ctx.lineWidth = 1.5; ctx.strokeStyle = colors.ring; ctx.stroke();
    ctx.beginPath(); ctx.arc(d.x, d.y, r + 1.25, 0, Math.PI * 2); ctx.lineWidth = .9; ctx.strokeStyle = colors.edge; ctx.stroke();
  }
  if (ringed) { ctx.beginPath(); ctx.arc(d.x, d.y, r + 3.2, 0, Math.PI * 2); ctx.lineWidth = 1.8; ctx.strokeStyle = colors.ink; ctx.stroke(); }
}
// Draw all residents, with the selected one on top.
function drawDots() {
  const r = 4.2 + .8 * Math.min(2, Math.max(0, Math.log2(cam.s / cam.fit))), order = {unknown: 0, sleep: 1, routine: 2, work: 3, out: 3, travel: 4};
  const others = [];
  let selected = null;
  points = [];
  for (const agent of overview.agents) {
    const p = positionAt(agent, state.t);
    if (!p) continue;
    const [x, y] = toWorld(p.lon, p.lat), item = {id: agent.id, x: sx(x), y: sy(y), g: groupAt(p), p};
    points.push(item);
    if (agent.id === state.id) selected = item; else others.push(item);
  }
  others.sort((a, b) => order[a.g] - order[b.g]);
  for (const d of others) dot(d, r, d.id === hoverId);
  if (!selected) return;
  ctx.globalAlpha = .22; ctx.fillStyle = selected.g === 'unknown' ? colors.ink3 : colors.group[selected.g];
  ctx.beginPath(); ctx.arc(selected.x, selected.y, r + 11, 0, Math.PI * 2); ctx.fill(); ctx.globalAlpha = 1;
  dot(selected, r + 1.6, true);
  const name = residentName(state.id), doing = placeLabel(selected.p);
  ctx.font = `600 13px ${SANS}`; const w1 = ctx.measureText(name).width;
  ctx.font = `12px ${SANS}`; const w2 = ctx.measureText(doing).width;
  const right = selected.x + 16 + Math.max(w1, w2) < view.w - 64, x = right ? selected.x + 16 : selected.x - 16;
  ctx.textAlign = right ? 'left' : 'right'; ctx.textBaseline = 'alphabetic';
  ctx.font = `600 13px ${SANS}`; haloText(ctx, name, x, selected.y - 1, colors.ink, 4);
  ctx.font = `12px ${SANS}`; haloText(ctx, doing, x, selected.y + 13, colors.ink2, 4);
}

/* Camera: everything moves through cameraChanged so the road layer re-renders once it settles. */
// Redraw the background shortly after the camera stops moving.
function cameraChanged() { clearTimeout(settleTimer); settleTimer = setTimeout(settle, 180); requestDraw(); }
function settle() { if (baseCam && (baseCam.x !== cam.x || baseCam.y !== cam.y || baseCam.s !== cam.s)) { renderBase(); requestDraw(); } }
// Smoothly move the camera to a new view.
function animateTo(target, anchor = null, ms = 280) {
  if (reduceMotion.matches) { cam.s = target.s; if (!state.follow) { cam.x = target.x; cam.y = target.y; } anim = null; cameraChanged(); return; }
  anim = {from: {x: cam.x, y: cam.y, s: cam.s}, to: target, anchor, start: performance.now(), ms}; requestDraw();
}
// Advance the camera animation by one frame.
function stepAnim(now) {
  const f = Math.min(1, (now - anim.start) / anim.ms), e = 1 - Math.pow(1 - f, 3), {from, to, anchor} = anim;
  cam.s = from.s * Math.pow(to.s / from.s, e);
  if (!state.follow) {
    if (anchor) { cam.x = anchor.wx - (anchor.px - view.w / 2) / cam.s; cam.y = anchor.wy - (anchor.py - view.h / 2) / cam.s; }
    else { cam.x = from.x + (to.x - from.x) * e; cam.y = from.y + (to.y - from.y) * e; }
  }
  cameraChanged();
  if (f >= 1) { anim = null; return false; }
  return true;
}
// Zoom in or out around a screen point.
function zoomAt(factor, px = view.w / 2, py = view.h / 2, smooth = false) {
  if (state.follow) { px = view.w / 2; py = view.h / 2; }
  const from = anim && smooth ? anim.to : cam, s = clampScale(from.s * factor);
  const wx = from.x + (px - view.w / 2) / from.s, wy = from.y + (py - view.h / 2) / from.s;
  const target = {x: wx - (px - view.w / 2) / s, y: wy - (py - view.h / 2) / s, s};
  if (smooth) animateTo(target, {wx, wy, px, py});
  else { anim = null; cam.s = s; if (!state.follow) { cam.x = target.x; cam.y = target.y; } cameraChanged(); }
}
function setFollow(on) {
  state.follow = on; $('follow').setAttribute('aria-pressed', String(on));
  if (on) requestDraw();
}
// Follow mode: glide the camera towards the selected resident.
function followStep(dt) {
  const p = positionAt(overview.agents[state.id], state.t);
  if (!p) return false;
  const [tx, ty] = toWorld(p.lon, p.lat), dx = tx - cam.x, dy = ty - cam.y;
  if (Math.abs(dx) * cam.s < .3 && Math.abs(dy) * cam.s < .3) { if (dx || dy) { cam.x = tx; cam.y = ty; cameraChanged(); } return false; }
  const k = reduceMotion.matches ? 1 : 1 - Math.exp(-dt * 7);
  cam.x += dx * k; cam.y += dy * k; cameraChanged();
  return true;
}
// Pan only when the selected resident is near the edge or off screen.
function panToSelected() {
  if (!cam.ready) return;
  if (state.follow) { requestDraw(); return; }
  const p = positionAt(overview.agents[state.id], state.t);
  if (!p) return;
  const [x, y] = toWorld(p.lon, p.lat), X = sx(x), Y = sy(y), m = 70;
  if (X < m || X > view.w - m || Y < m || Y > view.h - m) animateTo({x, y, s: cam.s});
}
// Match the canvas size to its box and the screen's pixel density.
function resize() {
  const box = $('mapWrap').getBoundingClientRect(), w = Math.round(box.width), h = Math.round(box.height), dpr = Math.min(devicePixelRatio || 1, 2);
  if (!w || !h) return;
  if (w !== view.w || h !== view.h || dpr !== view.dpr) {
    Object.assign(view, {w, h, dpr});
    canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
    baseStale = true;
  }
  if (!city) return;
  const fit = fitTarget();
  cam.fit = fit.s;
  if (!cam.ready) { Object.assign(cam, {x: fit.x, y: fit.y, s: fit.s}); cam.ready = true; }
  requestDraw();
}

/* Pointer, wheel and keyboard on the map. Two pointers pinch-zoom. */
const pointers = new Map();
let gesture = null;
// Centre and spread of the active pointers, for dragging and pinching.
function gestureState() {
  const pts = [...pointers.values()], n = pts.length;
  return {n, cx: pts.reduce((a, p) => a + p[0], 0) / n, cy: pts.reduce((a, p) => a + p[1], 0) / n, spread: n > 1 ? Math.hypot(pts[0][0] - pts[1][0], pts[0][1] - pts[1][1]) : 0};
}
// Find the resident dot closest to a screen point.
function nearest(x, y, radius) {
  let best = null, dist = radius;
  for (const p of points) { const d = Math.hypot(x - p.x, y - p.y); if (d < dist || (p.id === state.id && d < dist + 2)) { best = p; dist = d; } }
  return best;
}
// Show the hover tooltip next to a dot.
function showMapTip(d) {
  const tip = $('mapTip'), span = spanLabel(d.p);
  tip.replaceChildren(el('b', '', residentName(d.id)), el('span', '', span ? `${placeLabel(d.p)} · ${span}` : placeLabel(d.p)));
  tip.hidden = false;
  const w = tip.offsetWidth, h = tip.offsetHeight;
  let left = d.x + 14, top = d.y - h - 10;
  if (left + w > view.w - 8) left = d.x - w - 14;
  if (top < 8) top = d.y + 14;
  tip.style.setProperty('--x', `${Math.round(left)}px`); tip.style.setProperty('--y', `${Math.round(top)}px`);
}
function setHover(d) {
  const id = d?.id ?? null;
  canvas.classList.toggle('over-dot', id !== null);
  if (d) showMapTip(d); else $('mapTip').hidden = true;
  if (id !== hoverId) { hoverId = id; requestDraw(); }
}
// Mouse, touch, wheel and keyboard controls for the map.
function bindMap() {
  canvas.addEventListener('pointerdown', e => {
    try { canvas.setPointerCapture(e.pointerId); } catch {}
    pointers.set(e.pointerId, [e.offsetX, e.offsetY]);
    gesture = {...gestureState(), moved: gesture?.moved ?? 0}; anim = null; setHover(null);
  });
  canvas.addEventListener('pointermove', e => {
    if (!pointers.has(e.pointerId)) { if (e.pointerType === 'mouse') setHover(nearest(e.offsetX, e.offsetY, 12)); return; }
    pointers.set(e.pointerId, [e.offsetX, e.offsetY]);
    const g = gestureState();
    if (g.n !== gesture.n) { gesture = {...g, moved: gesture.moved}; return; }
    const dx = g.cx - gesture.cx, dy = g.cy - gesture.cy;
    gesture.moved += Math.hypot(dx, dy);
    // Moving more than 4 pixels counts as a drag, not a click.
    if (gesture.moved > 4 || g.n > 1) {
      if (state.follow) setFollow(false);
      canvas.classList.add('dragging');
      if (g.n > 1 && gesture.spread > 0) {
        const s = clampScale(cam.s * g.spread / gesture.spread), wx = cam.x + (g.cx - view.w / 2) / cam.s, wy = cam.y + (g.cy - view.h / 2) / cam.s;
        cam.s = s; cam.x = wx - (g.cx - view.w / 2) / s; cam.y = wy - (g.cy - view.h / 2) / s;
      }
      cam.x -= dx / cam.s; cam.y -= dy / cam.s; cameraChanged();
    }
    Object.assign(gesture, {cx: g.cx, cy: g.cy, spread: g.spread});
  });
  const release = (e, click) => {
    if (!pointers.delete(e.pointerId)) return;
    if (pointers.size) { gesture = {...gestureState(), moved: gesture.moved}; return; }
    if (click && gesture && gesture.moved <= 4) {
      const hit = nearest(e.offsetX, e.offsetY, e.pointerType === 'mouse' ? 13 : 22);
      if (hit && hit.id !== state.id) selectAgent(hit.id);
    }
    gesture = null; canvas.classList.remove('dragging');
  };
  canvas.addEventListener('pointerup', e => release(e, true));
  canvas.addEventListener('pointercancel', e => release(e, false));
  canvas.addEventListener('pointerleave', e => { if (e.pointerType === 'mouse' && !pointers.size) setHover(null); });
  canvas.addEventListener('dblclick', e => { e.preventDefault(); zoomAt(2, e.offsetX, e.offsetY, true); });
  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    const unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? view.h : 1;
    zoomAt(Math.exp(-e.deltaY * unit * (e.ctrlKey ? .01 : .0018)), e.offsetX, e.offsetY);
  }, {passive: false});
  // Arrow keys pan while the map has focus; elsewhere they move the playhead.
  canvas.addEventListener('keydown', e => {
    const pan = {ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1]}[e.key];
    if (pan) { e.preventDefault(); e.stopPropagation(); setFollow(false); animateTo({x: cam.x + pan[0] * 90 / cam.s, y: cam.y + pan[1] * 90 / cam.s, s: cam.s}, null, 160); }
  });
  $('zoomIn').onclick = () => zoomAt(1.6, undefined, undefined, true);
  $('zoomOut').onclick = () => zoomAt(1 / 1.6, undefined, undefined, true);
  $('fitMap').onclick = () => { setFollow(false); animateTo(fitTarget(), null, 360); };
  $('follow').onclick = () => setFollow(!state.follow);
}

/* Day ribbon and the 21 mini ribbons share one block painter. */
// Paint one day of activities and trips as coloured blocks.
function paintDay(g, w, top, h, day, hatch) {
  const agent = overview.agents[state.id], lo = day * 1440, hi = lo + 1440, x = t => (Math.max(lo, Math.min(hi, t)) - lo) / 1440 * w;
  g.fillStyle = colors.wash; g.fillRect(0, top, w, h);
  if (hatch) {
    g.save(); g.beginPath(); g.rect(0, top, w, h); g.clip();
    g.strokeStyle = colors.ink4; g.globalAlpha = .45; g.lineWidth = 1; g.beginPath();
    for (let i = -h; i < w; i += 5) { g.moveTo(i, top + h); g.lineTo(i + h, top); }
    g.stroke(); g.restore();
  }
  const paint = (rows, colorOf) => {
    for (let i = Math.max(0, latestIndex(rows, lo)); i < rows.length && rows[i][0] < hi; i++) {
      const r = rows[i];
      if (r[1] <= lo) continue;
      const a = x(r[0]), b = x(r[1]), gap = b - a > 3 ? .5 : 0;
      g.fillStyle = colorOf(r); g.fillRect(a + gap, top, Math.max(.8, b - a - 2 * gap), h);
    }
  };
  paint(agent.activities, r => colors.group[activityGroup(r[4])]);
  paint(agent.trips, () => colors.group.travel);
}
// Size a canvas for the screen and return its drawing context.
function sizeCanvas(c) {
  const w = c.clientWidth, h = c.clientHeight, dpr = Math.min(devicePixelRatio || 1, 2);
  if (!w || !h) return null;
  if (c.width !== Math.round(w * dpr) || c.height !== Math.round(h * dpr)) { c.width = Math.round(w * dpr); c.height = Math.round(h * dpr); }
  const g = c.getContext('2d'); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
  return {g, w, h};
}
// Draw the day ribbon below the map.
function drawRibbon() {
  const c = sizeCanvas($('ribbonCanvas'));
  if (!c || !overview || !colors) return;
  const {g, w} = c, day = dayOf(state.t);
  g.save(); g.beginPath(); g.roundRect(0, 0, w, 26, 5); g.clip(); paintDay(g, w, 0, 26, day, true); g.restore();
  for (const e of lookup?.markers[day] ?? []) {
    const x = (e.t - day * 1440) / 1440 * w;
    g.fillStyle = e.kind === 'conversation' ? colors.ink : colors.ink2; g.beginPath();
    if (e.kind === 'conversation') g.arc(x, 33, 3.2, 0, Math.PI * 2);
    else { g.moveTo(x, 29.5); g.lineTo(x + 3.5, 33); g.lineTo(x, 36.5); g.lineTo(x - 3.5, 33); g.closePath(); }
    g.fill();
  }
}
function drawMiniRibbons() {
  if (!overview || !colors) return;
  dayButtons.forEach((button, day) => {
    const c = sizeCanvas(button.querySelector('canvas'));
    if (c) paintDay(c.g, c.w, 0, c.h, day, false);
  });
}
function drawRibbons() { drawRibbon(); drawMiniRibbons(); }
// Tooltip text for the point of the ribbon under the pointer.
function ribbonTip(e) {
  const ribbon = $('ribbon'), box = ribbon.getBoundingClientRect(), x = Math.max(0, Math.min(box.width, e.clientX - box.left));
  const day = dayOf(state.t), t = day * 1440 + Math.min(1439, Math.floor(x / box.width * 1440)), agent = overview.agents[state.id];
  const trip = activeAt(agent.trips, t), act = trip ? null : activeAt(agent.activities, t), row = trip ?? act;
  let text = trip ? tripLabel(trip[6]) : act ? activityName(act[4]) : 'No activity recorded';
  if (row) text += ` · ${clock(row[0])}–${clockEnd(row[1])}`;
  const marker = (lookup?.markers[day] ?? []).find(m => Math.abs((m.t - day * 1440) / 1440 * box.width - x) < 6);
  if (marker) text += marker.kind === 'conversation' ? ` · talked with ${residentName(Number(marker.record.a) === state.id ? marker.record.b : marker.record.a)}` : marker.kind === 'event' ? ` · event: ${marker.record.description}` : ' · set new goals';
  const tip = $('ribbonTip');
  tip.replaceChildren(el('b', '', clock(t)), document.createTextNode(text)); tip.hidden = false;
  tip.style.setProperty('--x', `${Math.round(Math.max(0, Math.min(box.width - tip.offsetWidth, x - tip.offsetWidth / 2)))}px`);
}

/* Roster */
// Build the resident list and its search box.
function buildRoster() {
  const list = $('agentList');
  for (const a of manifest.agents) {
    const row = el('button', 'agent-row'), text = el('span', 'agent-text'), doing = el('span', 'agent-doing', '');
    row.type = 'button'; row.setAttribute('aria-pressed', String(a.id === state.id));
    text.append(el('span', 'agent-name', a.name), doing);
    row.append(el('i', 'sw g-unknown'), text);
    if (a.counts.conversation) {
      const talk = el('span', 'agent-talk'); talk.title = plural(a.counts.conversation, 'conversation');
      talk.append(icon('i-talk'), document.createTextNode(a.counts.conversation)); row.append(talk);
    }
    row.onclick = () => selectAgent(a.id);
    list.append(row); rosterRows.set(a.id, {row, swatch: row.firstChild, doing, key: ''});
  }
  const empty = el('p', 'roster-empty', 'No resident matches.'); empty.hidden = true; list.append(empty);
  $('agentSearch').oninput = () => {
    const q = $('agentSearch').value.toLowerCase().trim();
    let shown = 0;
    for (const [id, r] of rosterRows) { r.row.hidden = !!q && !`${residentName(id)} agent ${id} ${r.doing.textContent}`.toLowerCase().includes(q); shown += !r.row.hidden; }
    empty.hidden = shown > 0;
  };
}
function revealRow(row) {
  // Scroll only the list (vertical on desktop, a horizontal strip on narrower screens), never the page.
  if (!row || row.hidden) return;
  const list = $('agentList'), r = row.getBoundingClientRect(), b = list.getBoundingClientRect();
  if (r.top < b.top) list.scrollTop += r.top - b.top - 6; else if (r.bottom > b.bottom) list.scrollTop += r.bottom - b.bottom + 6;
  if (r.left < b.left) list.scrollLeft += r.left - b.left - 6; else if (r.right > b.right) list.scrollLeft += r.right - b.right + 6;
}
// Refresh what each resident in the list is doing now.
function updateRoster() {
  for (const [id, r] of rosterRows) {
    const p = positionAt(overview.agents[id], state.t), g = groupAt(p), label = placeLabel(p), key = `${g}|${label}`;
    if (key === r.key) continue;
    r.key = key; r.swatch.className = `sw g-${g}`; r.doing.textContent = label;
  }
}

/* Inspector: who, what now, how they feel */
// Index the selected resident's records for quick lookup.
function buildLookup(data) {
  const activity = new Map(), trip = new Map(), needs = [], markers = Array.from({length: 21}, () => []), talkDays = new Set();
  for (const e of data.events) {
    if (e.kind === 'activity') activity.set(e.t, e.record);
    else if (e.kind === 'trip') trip.set(e.t, e.record);
    else if (e.kind === 'needs') needs.push(e);
    else if (e.kind === 'conversation' || e.kind === 'event' || e.kind === 'goal') {
      markers[dayOf(e.t)].push(e);
      if (e.kind === 'conversation') talkDays.add(dayOf(e.t));
    }
  }
  return {activity, trip, needs, needTimes: needs.map(e => e.t), markers, talkDays};
}
// Destination and venue categories are OpenStreetMap tags; a few read badly as bare words.
const PLACE_NAMES = {convenience: 'convenience store', clothes: 'clothes shop', jewelry: 'jeweller', fast_food: 'fast-food restaurant', confectionery: 'sweet shop', cafe: 'café', shop: 'shop'};
const placeName = cat => PLACE_NAMES[cat] ?? pretty(cat);
const atPlace = cat => cat === 'home' ? 'home' : `${/^[aeiou]/i.test(placeName(cat)) ? 'an' : 'a'} ${placeName(cat)}`;
const LOCATIONS = {home: 'Home', work: 'Work', school: 'School', online: 'Online', travel: 'On the move'};
// Readable place name for an activity record.
function placeText(r) {
  const where = r.location === 'poi' ? sentence(placeName(r.poi_category)) : LOCATIONS[r.location] ?? sentence(r.location);
  return r.location === 'online' ? where : [where, r.area].filter(Boolean).join(', ');
}
// The saved needs log keeps at most 40 characters of each emotion; mark the cut instead of hiding it.
const EMOTION_LIMIT = 40;
const emotionText = text => { const t = sentence(text); return String(text ?? '').length >= EMOTION_LIMIT ? `${t}…` : t; };
// Bars for the hunger, energy, safety and social needs.
function needBars(r, cls) {
  const box = el('div', cls);
  for (const key of NEEDS) {
    // Missing levels keep their slot (shown as a dash) so the grid never changes shape.
    const v = r[key] === '' || r[key] == null ? NaN : Number(r[key]), known = Number.isFinite(v);
    const need = el('div', 'need'), top = el('div', 'need-top'), track = el('div', 'bar-track'), fill = el('div', 'bar-fill');
    top.append(el('span', '', sentence(key)), el('b', '', known ? v.toFixed(2) : '—'));
    fill.style.setProperty('--v', known ? Math.max(0, Math.min(1, v)) : 0); track.append(fill); need.append(top, track); box.append(need);
  }
  return box;
}
let nowKey = '';
// Refresh the panel that shows what the resident is doing now.
function updateNow() {
  if (!overview) return;
  const p = positionAt(overview.agents[state.id], state.t), row = p?.trip ?? p?.activity;
  const ni = lookup ? firstAfter(lookup.needTimes, state.t) - 1 : -1, key = `${state.id}|${p?.kind}|${row?.[0]}|${ni}|${!!lookup}`;
  if (key === nowKey) return;
  nowKey = key;
  $('nowSwatch').className = `sw sw-lg g-${groupAt(p)}`;
  let place = '', detailText = '';
  if (p?.kind === 'trip') {
    const r = lookup?.trip.get(p.trip[0]);
    place = r ? `${km(r.distance_km)}, ${tripPurpose(r)}` : 'Between logged endpoints';
    detailText = r?.why ?? '';
  } else if (p?.kind === 'activity') {
    const r = lookup?.activity.get(p.activity[0]);
    place = r ? placeText(r) : p.area ?? '';
    detailText = r ? [r.description, r.companions ? `With ${r.companions}.` : ''].filter(Boolean).join(' ') : '';
  } else if (p) place = 'Shown at the last logged location';
  // Every slot below keeps its size whatever the record holds; long text is clamped and kept whole in the tooltip.
  const label = placeLabel(p), detail = $('nowDetail');
  Object.assign($('nowActivity'), {textContent: label, title: label});
  Object.assign($('nowPlace'), {textContent: place, title: place});
  $('nowSpan').textContent = spanLabel(p);
  const missing = !lookup || !p ? '' : p.kind === 'trip' ? 'No reason was logged for this trip.' : 'No description was logged.';
  Object.assign(detail, {textContent: detailText || missing, title: detailText});
  detail.classList.toggle('is-missing', !detailText);
  const e = ni < 0 ? null : lookup.needs[ni], line = $('feelingLine'), when = $('feelingWhen');
  $('feeling').classList.toggle('is-missing', !e);
  if (e) {
    const day = dayOf(e.t), cut = String(e.record.emotion ?? '').length >= EMOTION_LIMIT;
    Object.assign(line, {textContent: emotionText(e.record.emotion), title: cut ? 'The saved log keeps only the first 40 characters of each emotion' : ''});
    when.textContent = `Logged ${day === dayOf(state.t) ? '' : `${dateLabel(day)}, `}${clock(e.t)} · need levels on a 0–1 scale`;
  } else {
    Object.assign(line, {textContent: lookup ? 'No feeling logged yet' : 'Loading…', title: ''});
    when.textContent = lookup ? 'Need levels appear with the first needs record' : '';
  }
  when.title = when.textContent;
  $('needsBars').replaceWith(Object.assign(needBars(e?.record ?? {}, 'needs'), {id: 'needsBars'}));
}

/* Feed: one timeline per day (or a 200-record window across all days). */
// Line that marks the current time in the record list.
const nowLine = el('li', 'now-line');
nowLine.append(el('b'), el('i'), el('span'));
nowLine.setAttribute('aria-label', 'Playhead');
let feedItems = [], feedTimes = [], feedFuture = -1, feedFollow = true, suppressScroll = false, feedList = [], feedWindow = {lo: 0, hi: 0};
let userScrollAt = 0, programmaticAt = 0, programmaticUntil = 0;
// Small builders for the parts of a record card.
const title = (body, text, muted) => { const h = el('h4', 'rec-title', text); if (muted) h.append(el('span', 'muted', ` · ${muted}`)); body.append(h); };
const sub = (body, text) => { if (text) body.append(el('p', 'rec-sub', text)); };
const prose = (body, text) => { if (text) body.append(el('p', 'rec-text', text)); };
const quote = (body, text) => { if (text) body.append(el('p', 'rec-quote', text)); };
// Collapsible section that is only built when first opened.
function more(body, label, fill, open = false) {
  const box = el('details', 'rec-more');
  box.append(el('summary', '', label));
  const ensure = () => { if (box.open && box.childElementCount === 1) { const inner = el('div', 'rec-more-body'); fill(inner); box.append(inner); } };
  box.addEventListener('toggle', ensure);
  if (open) { box.open = true; ensure(); }
  body.append(box);
}
// List of time and text rows.
function schedule(rows) {
  const ul = el('ul', 'lines');
  for (const [time, text, gap] of rows) { const li = el('li', gap ? 'gap' : ''); li.append(el('time', '', time), el('span', '', text)); ul.append(li); }
  return ul;
}
// Logged plan strings look like "18:00-18:45 shopping @ grocery store: Pick up groceries (active)".
const planLine = line => {
  const m = /^(\d\d:\d\d)-(\d\d:\d\d)\s+(.*)$/.exec(line), text = m ? m[3] : String(line), gap = text.includes('[EMPTY]');
  const part = /^(\S+) @ ([^:]+):\s*(.*?)(\s*\(active\))?$/.exec(text);
  const shown = gap ? 'Unplanned' : part ? `${activityName(part[1])}: ${part[3]}${part[4] ? ' (under way)' : ''}` : text;
  return [m ? `${m[1]}–${m[2]}` : '', shown, gap];
};
// One renderer for each record type.
const RENDER = {
  activity(body, r, e, li) {
    li.classList.add(`g-${activityGroup(r.activity)}`);
    title(body, activityName(r.activity));
    sub(body, [`${clock(e.t)}–${clockEnd(e.end)}`, duration(r.minutes), placeText(r)].filter(Boolean).join(' · '));
    prose(body, r.description);
    if (r.companions) sub(body, `With ${r.companions}`);
  },
  trip(body, r, e, li) {
    li.classList.add('g-travel');
    title(body, `${tripLabel(r.mode)}, ${km(r.distance_km)}`);
    sub(body, `${clock(e.t)}–${clockEnd(e.end)} · ${duration(r.minutes)} · ${tripPurpose(r)}`);
    prose(body, r.why);
  },
  conversation(body, r, e) {
    const a = Number(r.a), other = a === state.id ? r.b : r.a;
    title(body, `${sentence(r.modality)} with ${residentName(other)}`);
    sub(body, `Started by ${a === state.id ? 'this resident' : residentName(a)}`);
    prose(body, r.intention);
    const convo = el('div', 'convo');
    for (const [speaker, text] of r.transcript ?? []) {
      const id = Number(speaker), turn = el('div', `turn${id === state.id ? ' mine' : ''}`), who = el('button', 'who-btn', residentName(id));
      who.type = 'button'; who.title = id === state.id ? 'Jump to this moment' : `Switch to ${residentName(id)} at this moment`;
      who.onclick = () => { setPlaying(false); setTime(e.t); if (id !== state.id) selectAgent(id); };
      turn.append(who, el('p', '', text)); convo.append(turn);
    }
    body.append(convo);
    sub(body, `Outcome: ${r.outcome_a} for ${residentName(r.a)}, ${r.outcome_b} for ${residentName(r.b)}`);
    if (r.follow_up) sub(body, `Follow-up: ${typeof r.follow_up === 'string' ? r.follow_up : JSON.stringify(r.follow_up)}`);
  },
  reflection(body, r) {
    title(body, 'Reflection');
    if (r.question) sub(body, `Asked: ${r.question}`);
    quote(body, r.text);
  },
  decision(body, r) {
    if (r.kind === 'value_plan') {
      const options = r.candidates ?? [], chosen = options[r.selected];
      title(body, chosen ? `Chose ${activityName(chosen.activity).toLowerCase()}` : 'Weighed options', plural(options.length, 'option'));
      if (Array.isArray(r.span)) sub(body, `For ${clock(r.span[0])}–${clockEnd(r.span[1])}`);
      prose(body, r.reason);
      if (options.length) more(body, `Compare the ${plural(options.length, 'option')}`, box => {
        const list = el('div', 'choices');
        options.forEach((c, i) => {
          const choice = el('div', `choice${i === r.selected ? ' chosen' : ''}`);
          choice.append(el('b', '', activityName(c.activity)), el('span', 'val', c.value !== undefined ? `value ${c.value}` : ''));
          if (c.description) choice.append(el('p', '', c.description));
          if (c.imagined_emotion) choice.append(el('p', 'muted', `Imagined feeling: ${c.imagined_emotion}`));
          list.append(choice);
        });
        box.append(list);
      });
    } else if (r.kind === 'place') {
      title(body, `Picked a place for ${activityName(r.activity).toLowerCase()}`);
      sub(body, [(r.categories ?? r.poi_types ?? []).map(pretty).join(', '), r.distance_km !== undefined ? `${km(r.distance_km)} away` : '', r.n_candidates !== undefined ? `${plural(r.n_candidates, 'candidate')} within ${r.max_km} km` : ''].filter(Boolean).join(' · '));
      prose(body, r.macro_reason);
    } else if (r.kind === 'dispatch') {
      title(body, r.react ? 'Responded to a prompt' : 'Let a prompt pass', r.react && r.module ? pretty(r.module) : '');
      for (const s of r.stimuli ?? []) sub(body, `“${s}”`);
      prose(body, r.explanation);
      if (r.params?.intention) sub(body, `Intention: ${r.params.intention}`);
    } else if (r.kind === 'event_reaction') {
      title(body, 'Reacted to an event');
      for (const s of r.events ?? []) sub(body, `“${s}”`);
      prose(body, r.reaction);
      if (r.plan_after?.length) more(body, 'Plan afterwards', box => box.append(schedule(r.plan_after.map(planLine))));
    } else if (r.kind === 'replan') {
      title(body, r.until ? `Revised the plan until ${r.until}` : 'Revised the plan');
      sub(body, r.stimulus ? `“${r.stimulus}”` : '');
      prose(body, r.reason);
      if (r.blocks?.length) more(body, 'Revised blocks', box => box.append(schedule(r.blocks.map(planLine))));
    } else RENDER.other(body, r);
  },
  needs(body, r) {
    title(body, 'Needs and feeling');
    quote(body, emotionText(r.emotion));
    body.append(needBars(r, 'mini-needs'));
  },
  appraisal(body, r) {
    title(body, `Rated the ${placeName(r.poi_category)}`, activityName(r.activity));
    prose(body, r.reasoning);
    const box = el('div', 'scores'), unit = v => Math.max(0, Math.min(1, v));
    for (const key of ['price', 'atmosphere', 'satisfaction', 'convenience']) {
      const obs = Number(r[`obs_${key}`]), prior = Number(r[`prior_${key}`]);
      if (!Number.isFinite(obs)) continue;
      const row = el('div', 'score'), track = el('div', 'score-track'), bar = el('span'), tick = el('i');
      bar.style.setProperty('--b', unit(obs)); track.append(bar);
      if (Number.isFinite(prior)) { tick.style.setProperty('--a', unit(prior)); track.append(tick); }
      row.append(el('span', '', sentence(key)), track, el('b', '', Number.isFinite(prior) ? `${obs.toFixed(2)} vs ${prior.toFixed(2)}` : obs.toFixed(2)));
      box.append(row);
    }
    body.append(box);
    sub(body, 'Bar: this visit. Tick: the expectation beforehand. Scale 0–1.');
  },
  plan(body, r) {
    const blocks = (r.blocks ?? []).map(b => [`${clock(b[0])}–${clockEnd(b[1])}`, b[2] === 'EMPTY' ? 'Unplanned' : [activityName(b[2]), b[5]].filter(Boolean).join(': '), b[2] === 'EMPTY']);
    title(body, PLAN_NAMES[r.label] ?? `${sentence(r.label)} plan`);
    sub(body, 'Intended schedule; the actions show what was actually done.');
    more(body, plural(blocks.filter(b => !b[2]).length, 'planned block'), box => box.append(schedule(blocks)), r.label === 'final_initial');
  },
  goal(body, r) {
    title(body, 'Set new goals');
    if (r.trigger) sub(body, sentence(r.trigger));
    for (const [key, label] of [['short_term', 'Short term'], ['long_term', 'Long term']]) {
      if (!r[key]?.length) continue;
      const ul = el('ul', 'lines plain');
      for (const text of r[key]) ul.append(el('li', '', text));
      body.append(el('p', 'rec-label', label), ul);
    }
    prose(body, r.reason);
  },
  event(body, r) {
    title(body, `${sentence(r.type)} event`, r.severity);
    prose(body, r.description);
    const effects = r.effects?.needs;
    if (effects) sub(body, `Effect on needs: ${Object.entries(effects).map(([k, v]) => `${k} ${v > 0 ? '+' : '−'}${Math.abs(v)}`).join(', ')}`);
  },
  other(body, r) {
    const dl = el('dl', 'facts');
    for (const [k, v] of Object.entries(r)) { if (k === 'agent' || k === 'time') continue; dl.append(el('dt', '', sentence(k)), el('dd', '', typeof v === 'object' ? JSON.stringify(v) : v)); }
    body.append(dl);
  }
};
const KIND_NAMES = {activity: 'Action', trip: 'Movement', conversation: 'Conversation', reflection: 'Reflection', decision: 'Decision', goal: 'Goal', plan: 'Plan', needs: 'Needs', appraisal: 'Appraisal', event: 'Event'};
// Build one card in the record list.
function renderRecord(e) {
  const r = e.record, li = el('li', `rec k-${e.kind}`), body = el('div', 'rec-body'), time = el('button', 'rec-time', e.kind === 'plan' ? 'day' : clock(e.t));
  time.type = 'button'; time.title = `Jump to ${dateLabel(dayOf(e.t))}, ${clock(e.t)}`;
  time.setAttribute('aria-label', `${KIND_NAMES[e.kind] ?? 'Record'} at ${clock(e.t)}, jump here`);
  time.onclick = () => { setPlaying(false); suppressScroll = true; setTime(e.t); };
  li.append(time, el('span', 'rec-mark'), body);
  (RENDER[e.kind] ?? RENDER.other)(body, r, e, li);
  const source = el('details', 'rec-src');
  source.append(el('summary', '', `${e.source} · row ${e.row}`));
  source.addEventListener('toggle', () => { if (source.open && !source.querySelector('pre')) source.append(el('pre', '', JSON.stringify(r, null, 2))); });
  body.append(source);
  return li;
}
// Load 200 more records before or after the ones shown.
function page(direction) {
  // Paging away from the playhead means the reader is browsing, so stop following.
  const feed = $('eventFeed'), fromBottom = feed.scrollHeight - feed.scrollTop;
  feedFollow = false;
  if (direction < 0) feedWindow.lo = Math.max(0, feedWindow.lo - 200); else feedWindow.hi = Math.min(feedList.length, feedWindow.hi + 200);
  renderFeed(false);
  programmaticAt = performance.now(); programmaticUntil = programmaticAt + 80;
  if (direction < 0) feed.scrollTop = feed.scrollHeight - fromBottom;
}
// Rebuild the record list for the current filters.
function renderFeed(reset = true) {
  const feed = $('eventFeed');
  if (!detail) return;
  const day = dayOf(state.t), previousTop = feed.scrollTop;
  if (reset) {
    feedList = filterEvents(detail.events, {day, kind: state.kind, query: state.query, allDays: state.allDays});
    if (state.allDays) { const lo = Math.max(0, firstAfter(feedList.map(e => e.t), state.t) - 40); feedWindow = {lo, hi: Math.min(feedList.length, lo + 200)}; }
    else feedWindow = {lo: 0, hi: feedList.length};
    feedFollow = true;
  }
  $('feedLabel').textContent = state.allDays ? 'All 21 days' : dateLabel(day);
  feed.classList.toggle('hide-future', state.pastOnly);
  const nodes = [];
  if (!feedList.length) {
    const box = el('div', 'empty');
    box.append(el('h3', '', 'No matching records'), el('p', '', state.query || state.kind !== 'all' ? 'Try another record type or search, or include all 21 days.' : 'Nothing was saved for this resident on this day.'));
    nodes.push(box);
  }
  if (feedWindow.lo > 0) { const earlier = el('button', 'more', `Show ${Math.min(200, feedWindow.lo)} earlier records`); earlier.type = 'button'; earlier.onclick = () => page(-1); nodes.push(earlier); }
  const list = el('ol', 'records');
  feedItems = []; feedTimes = []; feedFuture = -1;
  let lastDay = -1;
  for (const e of feedList.slice(feedWindow.lo, feedWindow.hi)) {
    if (state.allDays && dayOf(e.t) !== lastDay) { lastDay = dayOf(e.t); list.append(el('li', 'rec-day', dateLabel(lastDay))); }
    const li = renderRecord(e); feedItems.push(li); feedTimes.push(e.t); list.append(li);
  }
  if (feedItems.length) nodes.push(list);
  if (feedWindow.hi < feedList.length) { const later = el('button', 'more', `Show ${Math.min(200, feedList.length - feedWindow.hi)} later records`); later.type = 'button'; later.onclick = () => page(1); nodes.push(later); }
  feed.replaceChildren(...nodes);
  programmaticAt = performance.now(); programmaticUntil = programmaticAt + 80;
  feed.scrollTop = reset ? 0 : previousTop;
  updateFeedTime(reset);
}
// Fade future records and move the current time line.
function updateFeedTime(scroll = true) {
  if (!detail) return;
  const i = firstAfter(feedTimes, state.t);
  if (i !== feedFuture) {
    const from = feedFuture < 0 ? 0 : Math.min(i, feedFuture), to = feedFuture < 0 ? feedItems.length : Math.max(i, feedFuture);
    for (let k = from; k < to; k++) feedItems[k].classList.toggle('is-future', k >= i);
    feedFuture = i;
  }
  const inWindow = feedItems.length && !(i === 0 && feedWindow.lo > 0) && !(i === feedItems.length && feedWindow.hi < feedList.length);
  if (inWindow) {
    nowLine.firstChild.textContent = clock(state.t);
    const next = feedItems[i] ?? null, parent = feedItems[0].parentNode;
    if (nowLine.parentNode !== parent || nowLine.nextSibling !== (next?.previousSibling?.classList?.contains('rec-day') ? next.previousSibling : next)) {
      parent.insertBefore(nowLine, next?.previousSibling?.classList?.contains('rec-day') ? next.previousSibling : next);
    }
  } else nowLine.remove();
  const total = feedList.length;
  const count = state.pastOnly ? `${(feedWindow.lo + i).toLocaleString('en-GB')} of ${plural(total, 'record')} so far` : plural(total, 'record');
  Object.assign($('eventCount'), {textContent: count, title: count});
  if (scroll) followFeed(); else updateBackToNow();
}
// Scroll the record list to keep the current time in view.
function followFeed(smooth = false) {
  const feed = $('eventFeed');
  if (suppressScroll) { suppressScroll = false; updateBackToNow(); return; }
  if (feedFollow && nowLine.isConnected && feed.scrollHeight > feed.clientHeight + 2) {
    const top = Math.max(0, nowLine.offsetTop - feed.clientHeight * .3);
    if (Math.abs(feed.scrollTop - top) > 2) {
      const glide = smooth && !reduceMotion.matches;
      programmaticAt = performance.now(); programmaticUntil = programmaticAt + (glide ? 800 : 80);
      feed.scrollTo({top, behavior: glide ? 'smooth' : 'auto'});
    }
  }
  updateBackToNow();
}
function updateBackToNow() { $('backToNow').hidden = feedFollow || !nowLine.isConnected; }

/* Playback and time */
let raf = 0, lastTick = 0, lastDraw = 0, lastUi = 0, lastHash = 0;
// Schedule the next animation frame.
function requestDraw() { if (!raf) raf = requestAnimationFrame(tick); }
// One animation frame: advance time and camera, then redraw.
function tick(now) {
  raf = 0;
  const dt = Math.min(.25, Math.max(0, (now - lastTick) / 1000)), moving = !!anim || pointers.size > 0;
  lastTick = now;
  let again = false;
  if (state.playing) {
    const next = Math.min(DURATION - .01, state.t + dt * state.speed);
    setTime(next, {quiet: true});
    if (next >= DURATION - .01) setPlaying(false); else again = true;
  }
  if (anim) again = stepAnim(now) || again;
  if (state.follow && overview) again = followStep(dt) || again;
  // Playback alone redraws at about 30 frames a second; gestures get every frame.
  if (state.playing && !moving && !state.follow && now - lastDraw < 30) { requestDraw(); return; }
  drawMap(); lastDraw = now;
  if (again) requestDraw();
}
// Keep the URL bookmark in sync with the view.
function saveHash(throttle = false) {
  const now = performance.now();
  if (throttle && now - lastHash < 1000) return;
  lastHash = now;
  const hash = `#agent=${state.id}&t=${Math.floor(state.t)}`;
  if (location.hash !== hash) history.replaceState(null, '', hash);
}
function updateClock() {
  const day = dayOf(state.t);
  $('clock').textContent = clock(state.t); $('clockDate').textContent = dateLabel(day); $('clockDay').textContent = `Day ${day + 1} of 21`;
}
function updateDays() {
  const day = dayOf(state.t);
  dayButtons.forEach((b, i) => b.setAttribute('aria-pressed', String(i === day)));
  $('prevDay').disabled = day === 0; $('nextDay').disabled = day === 20;
}
// Move to a new time and refresh everything that depends on it.
function setTime(t, {quiet = false} = {}) {
  const previousDay = dayOf(state.t);
  state.t = Math.max(0, Math.min(DURATION - .01, t));
  const minute = state.t % 1440;
  $('ribbon').style.setProperty('--p', minute / 1440);
  if (document.activeElement !== $('timeline')) $('timeline').value = Math.floor(minute);
  if (dayOf(state.t) !== previousDay) { updateDays(); drawRibbon(); renderFeed(true); }
  const now = performance.now();
  if (!quiet || now - lastUi > 240) {
    lastUi = now; updateClock(); updateRoster(); updateNow(); updateFeedTime(true); saveHash(quiet);
  }
  if (!quiet) requestDraw();
}
// Start or pause playback.
function setPlaying(on) {
  if (on && state.t >= DURATION - 1) setTime(0);
  state.playing = on;
  $('play').querySelector('use').setAttribute('href', on ? '#i-pause' : '#i-play');
  $('play').setAttribute('aria-label', on ? 'Pause' : 'Play'); $('play').title = on ? 'Pause (Space)' : 'Play (Space)';
  if (on) { lastTick = performance.now(); requestDraw(); }
  else { updateClock(); updateRoster(); updateNow(); updateFeedTime(true); saveHash(); }
}
// Jump to the same time of day on another day.
const changeDay = day => setTime(Math.max(0, Math.min(20, day)) * 1440 + state.t % 1440);
function setSpeed(speed) {
  state.speed = speed;
  for (const b of document.querySelectorAll('.speed button')) b.setAttribute('aria-pressed', String(Number(b.dataset.speed) === speed));
}

/* Selecting a resident */
// Show a status message below the record list.
function setStatus(text, error = false) { Object.assign($('loadStatus'), {textContent: text, title: text}); $('loadStatus').classList.toggle('error', error); }
// Fetch a JSON file, trying up to 3 times.
async function getJSON(path, tries = 3) {
  let last = null;
  for (let attempt = 0; attempt < tries; attempt++) {
    try {
      const response = await fetch(path);
      if (!response.ok) throw new Error(`${path} returned ${response.status}`);
      return await response.json();
    } catch (error) { last = error; if (attempt < tries - 1) await new Promise(done => setTimeout(done, 400 * (attempt + 1))); }
  }
  throw new Error(`Could not load ${path} (${last.message}).`);
}
// Select a resident and load their records.
async function selectAgent(id, {pan = true} = {}) {
  const version = ++loadVersion, a = manifest.agents[id];
  state.id = id; detail = null; lookup = null; nowKey = '';
  $('residentTitle').textContent = a.name; $('agentId').textContent = `agent ${id}`;
  const summary = [plural(a.counts.activity, 'action'), plural(a.counts.trip, 'trip'), plural(a.counts.conversation, 'conversation'), plural(a.counts.reflection, 'reflection')].join(' · ');
  Object.assign($('residentSummary'), {textContent: summary, title: summary});
  for (const [agentId, r] of rosterRows) r.row.setAttribute('aria-pressed', String(agentId === id));
  revealRow(rosterRows.get(id)?.row);
  feedItems = []; feedTimes = []; feedList = []; nowLine.remove();
  $('eventFeed').replaceChildren(el('div', 'empty', 'Loading saved records…'));
  Object.assign($('eventCount'), {textContent: '', title: ''});
  for (const b of dayButtons) b.querySelector('.day-talk').hidden = true;
  drawRibbons(); updateNow(); updateBackToNow(); setHover(null); requestDraw(); saveHash();
  if (pan) panToSelected();
  try {
    const data = cache.get(id) ?? await getJSON(`data/agents/${id}.json`);
    cache.delete(id); cache.set(id, data);
    while (cache.size > 4) cache.delete(cache.keys().next().value);
    if (version !== loadVersion) return;
    detail = data; lookup = buildLookup(data);
    dayButtons.forEach((b, day) => { b.querySelector('.day-talk').hidden = !lookup.talkDays.has(day); });
    renderFeed(true); drawRibbon(); updateNow();
    setStatus(`${plural(data.events.length, 'saved record')} for ${a.name} · read from saved logs, no model calls`);
  } catch (error) {
    if (version !== loadVersion) return;
    setStatus(error.message, true);
    const box = el('div', 'empty'), retry = el('button', 'more', 'Try again');
    retry.type = 'button'; retry.onclick = () => selectAgent(id, {pan: false});
    box.append(el('h3', '', 'These records did not load'), el('p', '', error.message), retry);
    $('eventFeed').replaceChildren(box);
  }
}

/* Wiring */
// Build the 21 day buttons.
function buildDays() {
  const strip = $('dayStrip');
  for (let day = 0; day < 21; day++) {
    if (day === 7 || day === 14) strip.append(el('span', 'day-gap'));
    const b = el('button', 'day'), talk = el('i', 'day-talk');
    b.type = 'button'; b.title = dateLabel(day); b.setAttribute('aria-label', `Day ${day + 1}, ${dateLabel(day)}`);
    talk.hidden = true; talk.title = 'Has a conversation';
    b.append(el('span', 'day-wd', WEEKDAYS[day % 7].slice(0, 3)), el('span', 'day-num', day + 1), el('canvas'), talk);
    b.onclick = () => changeDay(day);
    strip.append(b); dayButtons.push(b);
  }
}
// Open the About dialog with this session's speed figures.
function openAbout() {
  setPlaying(false);
  const sorted = [...metrics.frames].sort((a, b) => a - b), p95 = sorted[Math.floor(sorted.length * .95)] ?? 0, layer = Math.max(0, ...metrics.base);
  const heap = performance.memory ? ` · JavaScript heap ${(performance.memory.usedJSHeapSize / 1048576).toFixed(0)} MB` : '';
  $('performanceNote').textContent = `This session: ready in ${(metrics.ready / 1000).toFixed(2)} s · map frame p95 ${p95.toFixed(1)} ms · slowest road-layer redraw ${layer.toFixed(0)} ms · ${plural(cache.size, 'resident')} cached${heap}.`;
  $('about').showModal();
}
// Connect all controls and keyboard shortcuts.
function bind() {
  bindMap();
  $('play').onclick = () => setPlaying(!state.playing);
  $('backStep').onclick = () => setTime(state.t - 15);
  $('forwardStep').onclick = () => setTime(state.t + 15);
  for (const b of document.querySelectorAll('.speed button')) b.onclick = () => setSpeed(Number(b.dataset.speed));
  $('timeline').addEventListener('input', () => { setPlaying(false); setTime(dayOf(state.t) * 1440 + Number($('timeline').value)); });
  $('prevDay').onclick = () => changeDay(dayOf(state.t) - 1);
  $('nextDay').onclick = () => changeDay(dayOf(state.t) + 1);
  const ribbon = $('ribbon');
  ribbon.addEventListener('pointermove', e => { if (overview) ribbonTip(e); });
  ribbon.addEventListener('pointerleave', () => { $('ribbonTip').hidden = true; });
  $('eventKind').onchange = () => { state.kind = $('eventKind').value; renderFeed(true); };
  $('allDays').onchange = () => { state.allDays = $('allDays').checked; renderFeed(true); };
  $('pastOnly').onchange = () => { state.pastOnly = $('pastOnly').checked; $('eventFeed').classList.toggle('hide-future', state.pastOnly); feedFollow = true; updateFeedTime(true); };
  let searchTimer = 0;
  $('eventSearch').oninput = () => { clearTimeout(searchTimer); searchTimer = setTimeout(() => { state.query = $('eventSearch').value; renderFeed(true); }, 180); };
  const feed = $('eventFeed');
  for (const type of ['wheel', 'touchstart', 'keydown']) feed.addEventListener(type, () => { userScrollAt = performance.now(); }, {passive: true});
  feed.addEventListener('pointerdown', e => { if (e.target === feed) userScrollAt = performance.now(); });
  feed.addEventListener('scroll', () => {
    const now = performance.now();
    // A scroll is the reader's when their input came after the latest automatic scroll began.
    if (feedFollow && now - userScrollAt < 1500 && (now > programmaticUntil || userScrollAt > programmaticAt)) { feedFollow = false; updateBackToNow(); }
  }, {passive: true});
  $('backToNow').onclick = () => { feedFollow = true; followFeed(true); };
  $('themeToggle').onclick = () => {
    const next = isDark() ? 'light' : 'dark';
    root.dataset.theme = next;
    try { localStorage.setItem(THEME_KEY, next); } catch {}
    syncTheme();
  };
  darkQuery.addEventListener('change', () => { if (!root.dataset.theme) syncTheme(); });
  $('aboutButton').onclick = openAbout;
  $('closeAbout').onclick = () => $('about').close();
  $('about').addEventListener('click', e => {
    const r = $('about').getBoundingClientRect();
    if (e.clientX < r.left || e.clientX > r.right || e.clientY < r.top || e.clientY > r.bottom) $('about').close();
  });
  // Keyboard shortcuts, ignored while typing in a field.
  document.addEventListener('keydown', e => {
    if ($('about').open || e.ctrlKey || e.metaKey || e.altKey || !overview) return;
    const target = e.target, tag = target.tagName, type = target.type;
    if ((tag === 'INPUT' && type !== 'range' && type !== 'checkbox') || tag === 'SELECT' || tag === 'TEXTAREA') return;
    if (e.code === 'Space') {
      if (tag === 'BUTTON' || tag === 'SUMMARY' || type === 'checkbox') return;
      e.preventDefault(); setPlaying(!state.playing);
    } else if ((e.key === 'ArrowLeft' || e.key === 'ArrowRight') && type !== 'range' && target !== canvas) {
      e.preventDefault(); setTime(state.t + (e.key === 'ArrowLeft' ? -1 : 1) * (e.shiftKey ? 60 : 15));
    } else if (e.key === '[') changeDay(dayOf(state.t) - 1);
    else if (e.key === ']') changeDay(dayOf(state.t) + 1);
    else if (e.key === 'f' || e.key === 'F') setFollow(!state.follow);
    else if (e.key === '+' || e.key === '=') { e.preventDefault(); zoomAt(1.5, undefined, undefined, true); }
    else if (e.key === '-' || e.key === '_') { e.preventDefault(); zoomAt(1 / 1.5, undefined, undefined, true); }
  });
  document.addEventListener('visibilitychange', () => { if (document.hidden && state.playing) setPlaying(false); });
  window.addEventListener('hashchange', () => {
    const next = parseHash(location.hash);
    setPlaying(false); setTime(next.t);
    if (next.id !== state.id) selectAgent(next.id);
  });
  bindSplitter($('rosterSplit'), 'roster');
  bindSplitter($('panelSplit'), 'panel');
  new ResizeObserver(resize).observe($('mapWrap'));
  new ResizeObserver(drawRibbons).observe($('ribbon'));
}
// Column widths chosen with the splitters. The grid itself keeps the stage at least 560px wide;
// these bounds only stop a drag from running far past what the grid will honour.
const twoColumn = matchMedia('(max-width:1180px)');
// Allowed width range for a resizable column.
function columnBounds(which) {
  if (which === 'roster') return [180, 360];
  const roster = twoColumn.matches ? 0 : $('rosterSplit').parentElement.getBoundingClientRect().width;
  return [360, Math.max(360, Math.min(900, Math.floor(innerWidth - roster - 560)))];
}
// Set a column width and optionally save it.
function setColumn(which, px, save) {
  const [lo, hi] = columnBounds(which);
  const value = Math.round(Math.min(hi, Math.max(lo, px)));
  root.style.setProperty(COLUMNS[which].prop, `${value}px`);
  if (save) try { localStorage.setItem(COLUMNS[which].key, String(value)); } catch {}
  syncSplitter(which);
}
// Reset a column to its default width.
function resetColumn(which) {
  root.style.removeProperty(COLUMNS[which].prop);
  try { localStorage.removeItem(COLUMNS[which].key); } catch {}
  syncSplitter(which);
}
function columnWidth(which) {
  return Math.round($(which === 'roster' ? 'rosterSplit' : 'panelSplit').parentElement.getBoundingClientRect().width);
}
// Keep the splitter's screen reader values current.
function syncSplitter(which) {
  const handle = $(which === 'roster' ? 'rosterSplit' : 'panelSplit'), [lo, hi] = columnBounds(which);
  handle.setAttribute('aria-valuemin', lo); handle.setAttribute('aria-valuemax', hi);
  handle.setAttribute('aria-valuenow', columnWidth(which));
}
// Drag and keyboard resizing for a column splitter.
function bindSplitter(handle, which) {
  // The roster handle sits on its right edge (drag right = wider); the panel handle on its left.
  const sign = which === 'roster' ? 1 : -1;
  let drag = null;
  handle.addEventListener('pointerdown', e => {
    if (e.button !== 0) return;
    e.preventDefault();
    handle.setPointerCapture(e.pointerId);
    drag = {x: e.clientX, width: columnWidth(which)};
    handle.classList.add('dragging'); document.body.classList.add('resizing');
  });
  handle.addEventListener('pointermove', e => { if (drag) setColumn(which, drag.width + sign * (e.clientX - drag.x), false); });
  const end = () => {
    if (!drag) return;
    drag = null;
    handle.classList.remove('dragging'); document.body.classList.remove('resizing');
    if (root.style.getPropertyValue(COLUMNS[which].prop)) setColumn(which, columnWidth(which), true);
  };
  handle.addEventListener('pointerup', end);
  handle.addEventListener('pointercancel', end);
  handle.addEventListener('lostpointercapture', end);
  handle.addEventListener('dblclick', () => resetColumn(which));
  handle.addEventListener('keydown', e => {
    const step = e.shiftKey ? 64 : 16, [lo, hi] = columnBounds(which);
    let next = null;
    if (e.key === 'ArrowLeft') next = columnWidth(which) - sign * step;
    else if (e.key === 'ArrowRight') next = columnWidth(which) + sign * step;
    else if (e.key === 'Home') next = lo;
    else if (e.key === 'End') next = hi;
    else if (e.key === 'Enter') { e.preventDefault(); e.stopPropagation(); resetColumn(which); return; }
    if (next === null) return;
    // Keep the arrow keys from also stepping the playhead.
    e.preventDefault(); e.stopPropagation();
    setColumn(which, next, true);
  });
  handle.addEventListener('focus', () => syncSplitter(which));
  syncSplitter(which);
}
// Replace the page with an error message.
function showError(error) {
  console.error(error);
  const banner = el('section', 'error-banner'), retry = el('button', 'text-btn', 'Try again');
  retry.type = 'button'; retry.onclick = () => location.reload();
  banner.append(el('h2', '', 'The replay could not load'), el('p', '', error.message), el('p', '', 'Start this viewer with Start Replay.cmd and keep the data folder beside it.'), retry);
  $('app').replaceChildren(banner); $('app').setAttribute('aria-busy', 'false');
}
// Load the data and start the app.
async function start() {
  try {
    readColors();
    const mapRequest = getJSON('data/map.json');
    mapRequest.catch(() => {});
    [manifest, overview] = await Promise.all([getJSON('data/manifest.json'), getJSON('data/overview.json')]);
    buildRoster(); buildDays(); bind(); syncTheme();
    $('provenance').textContent = `Exported ${manifest.generated_utc.slice(0, 10)} from the audited 21-day continuation: ${manifest.counts.activity.toLocaleString('en-GB')} activities, ${manifest.counts.trip.toLocaleString('en-GB')} trips, ${manifest.counts.conversation} conversations and ${manifest.counts.reflection.toLocaleString('en-GB')} reflections. Source file hashes are recorded in data/manifest.json.`;
    updateDays(); updateClock(); updateRoster();
    const first = selectAgent(state.id, {pan: false});
    city = prepareCity(await mapRequest);
    $('mapStatus').hidden = true;
    resize(); setTime(state.t);
    $('app').setAttribute('aria-busy', 'false');
    await first;
    metrics.ready = performance.now() - metrics.started;
  } catch (error) { showError(error); }
}
start();
