// Rigorous-in-the-model companion of shared3.js: parent bin split into KX x KU sub-boxes, each
// propagated as an interval box through D levels.  Pessimistic: kill whenever touching is possible,
// leaf contributes w * min V over every bin its box meets; u-threshold straddles are bisected.
// Box value = sum over leaves; bin value = min over sub-boxes (shared phase within each sub-box).
// usage: node shared3rig.js N M D IT C KX KU [no3]
// ADAPT=k env: additionally bisect a sub-box in x (up to k times) while some leaf box meets 2+ x-bins.
const fs = require('fs');
const a = process.argv.slice(2);
const [N, M, D, IT] = a.slice(0, 4).map(Number);
const C = Number(a[4]), KX = Number(a[5]), KU = Number(a[6]), NO3 = a[7] === 'no3';
const sft = JSON.parse(fs.readFileSync(__dirname + '/' + (process.env.SFT || 'sft45.json')));
const S = sft.T.length, T = sft.T, r = sft.r, lam = sft.lam;
const delta = Math.pow(3, -C) * 1.0001, eps = 1e-12, U = Math.log2(6), L3 = Math.log2(3);
const M2 = Math.max(1, Math.round(M * (U - 2) / (U - 1))), M1 = M - M2;
const edges = []; for (let t = 0; t <= M1; t++) edges.push(1 + t / M1); for (let t = 1; t <= M2; t++) edges.push(2 + (U - 2) * t / M2);
const binLo = v => { let j = 0; while (j < M - 1 && edges[j + 1] <= v + eps) j++; return j; };
const binHi = v => { let j = M - 1; while (j > 0 && edges[j] >= v - eps) j--; return j; };
const rhoOf = u => delta * Math.pow(2, u);
const P = []; for (let s = 0; s < S; s++) P.push([0, 1].map(d => T[s][d] < 0 ? 0 : r[T[s][d]] / (lam * r[s])));
const NB = N * M;
let splits = 0; const ADAPT = Number(process.env.ADAPT || 0);
// returns array of leaves [w, s, ia, ib, ja, jb] or null if a u-straddle needs bisection
function descend(s, xlo, xhi, ulo, uhi, depth, w, out) {
  if (depth === D) {
    const fl = Math.floor(xlo); xlo -= fl; xhi -= fl;
    out.push([w, s, Math.floor(xlo * N + eps), Math.ceil(xhi * N - eps) - 1, binLo(ulo), binHi(uhi)]); return -1;
  }
  const rlo = rhoOf(ulo), rhi = rhoOf(uhi);
  for (let d = 0; d < 2; d++) {
    const t = T[s][d]; if (t < 0) continue;
    let cxlo = xlo + d * rlo / 2, cxhi = xhi + d * rhi / 2, culo = ulo - 1, cuhi = uhi - 1;
    const res = cuhi <= 1 + eps, maybe = culo < 1 - eps && cuhi > 1 + eps;
    if (maybe) return 1 - culo; // u-offset (path shifts are additive) at which to split the top box
    if (res) {
      if (!NO3) { let touch = false; const chi = rhi / 2;
        for (let kk = Math.floor(cxlo) - 1; kk <= Math.ceil(cxhi + chi) + 1; kk++) if (cxlo <= kk + delta + eps && cxhi + chi >= kk - delta - eps) { touch = true; break; }
        if (touch) continue; }
      const fl = Math.floor(3 * cxlo); cxlo = 3 * cxlo - fl; cxhi = 3 * cxhi - fl; culo += L3; cuhi += L3;
    }
    const rr = descend(t, cxlo, cxhi, culo, cuhi, depth + 1, w * P[s][d], out); if (rr >= 0) return rr;
  }
  return -1;
}
function boxes(s, xlo, xhi, ulo, uhi, acc, lvl) {
  const out = [];
  const rr = descend(s, xlo, xhi, ulo, uhi, 0, 1, out);
  if (rr < 0) {
    if (lvl < ADAPT && out.some(l => l[3] > l[2])) { const xm = (xlo + xhi) / 2; boxes(s, xlo, xm, ulo, uhi, acc, lvl + 1); boxes(s, xm, xhi, ulo, uhi, acc, lvl + 1); return; }
    acc.push(out); return; }
  if (lvl > 60) throw new Error('split loop');
  splits++; const um = ulo + rr; boxes(s, xlo, xhi, ulo, um, acc, lvl + 1); boxes(s, xlo, xhi, um, uhi, acc, lvl + 1);
}
function binBoxes(s, i, j) {
  const acc = [];
  for (let px = 0; px < KX; px++) for (let pu = 0; pu < KU; pu++) {
    const du = (edges[j + 1] - edges[j]) / KU;
    boxes(s, (i + px / KX) / N, (i + (px + 1) / KX) / N, edges[j] + pu * du, edges[j] + (pu + 1) * du, acc, 0);
  }
  return acc;
}
let V = new Float64Array(S * NB).fill(1), lo = 0;
const minV = (s, ia, ib, ja, jb) => { let m = Infinity; for (let x = ia; x <= ib; x++) { const base = s * NB + (((x % N) + N) % N) * M; for (let y = ja; y <= jb; y++) if (V[base + y] < m) m = V[base + y]; } return m; };
for (let it = 0; it < IT; it++) {
  const W = new Float64Array(S * NB); lo = Infinity;
  for (let q = 0; q < S * NB; q++) {
    let val = Infinity;
    const s0 = Math.floor(q / NB), i0 = Math.floor((q % NB) / M), j0 = q % M;
    for (const out of binBoxes(s0, i0, j0)) { let sm = 0; for (const [w, s, ia, ib, ja, jb] of out) sm += w * minV(s, ia, ib, ja, jb); if (sm < val) val = sm; }
    W[q] = val; if (V[q] > 1e-12) { const rr = val / V[q]; if (rr < lo) lo = rr; }
  }
  let mx = 0; for (const v of W) if (v > mx) mx = v;
  if (mx === 0) { console.log(`rig C=${C} D=${D}: tree DEAD at iteration ${it}`); process.exit(0); }
  for (let q = 0; q < W.length; q++) W[q] /= mx; V = W;
}
let z = 0, mp = Infinity; for (const v of V) { if (v < 1e-9) z++; else if (v < mp) mp = v; }
console.log(`rig${NO3 ? ' no3' : ''} N=${N} M=${M} D=${D} C=${C} K=${KX}x${KU}: block ratio ${lo.toFixed(6)} per-level growth ${(lam * Math.pow(Math.max(lo, 0), 1 / D)).toFixed(6)} zeros ${z}/${V.length} minpos ${mp.toExponential(3)} rootV ${V[0].toExponential(3)} usplits ${splits}`);
