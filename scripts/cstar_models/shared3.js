// Shared-phase block version of abs3.js (operator gate 4).
// Same state (sigma, x-bin i, u-bin j) and same touching-kill model as abs3.js, but over a
// block of D binary levels ONE parent point (x,u) in the bin is propagated exactly to all
// 2^D descendants:  shared:   W(s,i,j) = min_{sample p} sum_{leaf} P(path) V(leaf(p))
//                   separate: W(s,i,j) = sum_{leaf} min_{sample p} P(path) V(leaf(p))
// Both use the same finite sample set, so both are OPTIMISTIC screens (>= true infimum).
// usage: node shared3.js N M D IT C KX KU MODE [no3]   MODE = shared | separate
const fs = require('fs');
const a = process.argv.slice(2);
const [N, M, D, IT] = a.slice(0, 4).map(Number);
const C = Number(a[4]), KX = Number(a[5]), KU = Number(a[6]), MODE = a[7], NO3 = a[8] === 'no3';
const sft = JSON.parse(fs.readFileSync(__dirname + '/sft45.json'));
const S = sft.T.length, T = sft.T, r = sft.r, lam = sft.lam;
const delta = Math.pow(3, -C) * 1.0001, eps = 1e-12, U = Math.log2(6), L3 = Math.log2(3);
const M2 = Math.max(1, Math.round(M * (U - 2) / (U - 1))), M1 = M - M2;
const edges = []; for (let t = 0; t <= M1; t++) edges.push(1 + t / M1); for (let t = 1; t <= M2; t++) edges.push(2 + (U - 2) * t / M2);
const ubin = v => { let j = 0; while (j < M - 1 && edges[j + 1] <= v) j++; return j; };
const rhoOf = u => delta * Math.pow(2, u);
const P = []; for (let s = 0; s < S; s++) P.push([0, 1].map(d => T[s][d] < 0 ? 0 : r[T[s][d]] / (lam * r[s])));
const NB = N * M;
// leaves[(s,i,j)] = array over samples of array of [weight, leafIndex] ; leaves keyed by path id
// enumerate: for each sample, a Map path->(w, idx); killed paths absent.
function descend(s, x, u, depth, path, w, out) {
  if (depth === D) { const xi = Math.min(N - 1, Math.floor((x - Math.floor(x)) * N)); out.push([path, w, s * NB + xi * M + ubin(u)]); return; }
  const rho = rhoOf(u);
  for (let d = 0; d < 2; d++) {
    const t = T[s][d]; if (t < 0) continue;
    let cx = x + d * rho / 2, cu = u - 1;
    if (cu <= 1 + eps) {
      if (!NO3) { const k = Math.round(cx + rho / 4); // nearest integer to child centre; check touch with all nearby
        let touch = false; for (let kk = Math.floor(cx) - 1; kk <= Math.ceil(cx + rho / 2) + 1; kk++) if (cx <= kk + delta && cx + rho / 2 >= kk - delta) { touch = true; break; }
        if (touch) continue; }
      cx = 3 * cx; cx -= Math.floor(cx); cu += L3;
    }
    descend(t, cx, cu, depth + 1, path * 2 + d, w * P[s][d], out);
  }
}
// precompute sample leaves
const pre = new Array(S * NB);
for (let s = 0; s < S; s++) for (let i = 0; i < N; i++) for (let j = 0; j < M; j++) {
  const samp = [];
  for (let px = 0; px < KX; px++) for (let pu = 0; pu < KU; pu++) {
    const x = (i + (px + 0.5) / KX) / N, u = edges[j] + (edges[j + 1] - edges[j]) * (pu + 0.5) / KU;
    const out = []; descend(s, x, u, 0, 0, 1, out); samp.push(out);
  }
  pre[s * NB + i * M + j] = samp;
}
let V = new Float64Array(S * NB).fill(1), lo = 0;
for (let it = 0; it < IT; it++) {
  const W = new Float64Array(S * NB); lo = Infinity;
  for (let q = 0; q < S * NB; q++) {
    const samp = pre[q]; let val;
    if (MODE === 'shared') { val = Infinity; for (const out of samp) { let sm = 0; for (const [, w, l] of out) sm += w * V[l]; if (sm < val) val = sm; } }
    else { const mn = new Map(); const cnt = new Map();
      for (const out of samp) for (const [p, w, l] of out) { const v = w * V[l]; mn.set(p, Math.min(mn.has(p) ? mn.get(p) : Infinity, v)); cnt.set(p, (cnt.get(p) || 0) + 1); }
      val = 0; for (const [p, v] of mn) if (cnt.get(p) === samp.length) val += v; }
    W[q] = val; if (V[q] > 1e-12) { const rr = val / V[q]; if (rr < lo) lo = rr; }
  }
  let mx = 0; for (const v of W) if (v > mx) mx = v; if (mx === 0) { console.log(`${MODE} C=${C}: tree DEAD (all values 0) at iteration ${it}`); process.exit(0); } for (let q = 0; q < W.length; q++) W[q] /= mx; V = W;
}
let z = 0, mp = Infinity; for (const v of V) { if (v < 1e-9) z++; else if (v < mp) mp = v; }
const g = lam * Math.pow(Math.max(lo, 0), 1 / D);
console.log(`${MODE}${NO3 ? ' no3' : ''} N=${N} M=${M} D=${D} C=${C} K=${KX}x${KU}: block ratio ${lo.toFixed(6)} per-level growth ${g.toFixed(6)} zeros ${z}/${V.length} minpos ${mp.toExponential(3)} rootV ${V[0].toExponential(3)}`);
