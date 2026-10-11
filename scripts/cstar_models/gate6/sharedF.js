// Operator gate 6 SCREEN: shared3.js generalised to a joint core over {2,3} ∪ F.
// Each base b in B = [3, ...F] carries its own phase (x_b mod 1 in units of the pending base-b stage,
// u_b = log2(rho_b/delta_b) in (1, 1+log2 b]), binned N_b x M_b; binary SFT as in shared3.js.
// Shared-phase block of D binary levels, sampled (OPTIMISTIC: an upper bound on any certificate).
// usage: node sharedF.js C D IT F spec3 [spec5 ...]   F = "" | 5 | 5,6 | 5,6,7 ; spec = N:M:KX:KU
// env CONT=1 containment pruning per base; env ZERO=b,..: those bases get radius 0 (control);
// env NOKEEP=1: delete every positive child (control: must die).
const fs = require('fs');
const a = process.argv.slice(2);
const C = +a[0], D = +a[1], IT = +a[2];
const F = a[3] ? a[3].split(',').map(Number) : [];
const B = [3, ...F];
const specs = B.map((b, k) => (a[4 + k] || a[a.length - 1]).split(':').map(Number));
const ZERO = (process.env.ZERO || '').split(',').filter(x => x).map(Number);
const CONT = process.env.CONT === '1', NOKEEP = process.env.NOKEEP === '1';
const sftPath = require('os').tmpdir() + `/sft_${C}_13.json`;
if (!fs.existsSync(sftPath)) require('child_process').execFileSync(process.execPath, [__dirname + '/../gen_sft.js', String(C), '13', sftPath]);
const sft = JSON.parse(fs.readFileSync(sftPath));
const S = sft.T.length, T = sft.T, r = sft.r, lam = sft.lam;
const P = []; for (let s = 0; s < S; s++) P.push([0, 1].map(d => T[s][d] < 0 ? 0 : r[T[s][d]] / (lam * r[s])));
const eps = 1e-12;
const nb = B.length;
const dl = B.map(b => ZERO.includes(b) ? 0 : Math.pow(b, -C) * 1.0001);
const Ub = B.map(b => 1 + Math.log2(b)), Lb = B.map(b => Math.log2(b));
const Nb = specs.map(s => s[0]), Mb = specs.map(s => s[1]), KXb = specs.map(s => s[2]), KUb = specs.map(s => s[3]);
const binSize = Nb.map((n, k) => n * Mb[k]);
let NB = 1; for (const z of binSize) NB *= z;
const NST = S * NB;
function binOf(xs, us) { let idx = 0; for (let k = 0; k < nb; k++) {
  const xi = Math.min(Nb[k] - 1, Math.floor((xs[k] - Math.floor(xs[k])) * Nb[k]));
  const uj = Math.max(0, Math.min(Mb[k] - 1, Math.floor((us[k] - 1) / (Ub[k] - 1) * Mb[k])));
  idx = idx * binSize[k] + xi * Mb[k] + uj; } return idx; }
// descend one sample; push [w, leafState]
function descend(s, xs, us, zl, zr, depth, w, out) {
  if (depth === D) { for (let k = 0; k < nb; k++) if (zl[k] > 0 || zr[k] > 0) return; out.push(w, s * NB + binOf(xs, us)); return; }
  for (let d = 0; d < 2; d++) {
    const t = T[s][d]; if (t < 0) continue;
    if (NOKEEP) continue;
    const cx = xs.slice(), cu = us.slice(), czl = zl.slice(), czr = zr.slice(); let dead = false;
    for (let k = 0; k < nb && !dead; k++) {
      const h = dl[k] > 0 ? dl[k] * Math.pow(2, us[k]) / 2 : Math.pow(2, us[k] - 30) / 2; // rho/2 (ZERO: arbitrary scale, no kills)
      cx[k] = xs[k] + d * h; cu[k] = us[k] - 1;
      czl[k] = d === 0 ? zl[k] : Math.max(0, zl[k] - h); czr[k] = d === 1 ? zr[k] : Math.max(0, zr[k] - h);
      if (czl[k] >= h || czr[k] >= h || czl[k] + czr[k] >= h) { dead = true; break; }
      if (cu[k] <= 1 + eps) {
        const del = dl[k], x = cx[k];
        if (del > 0) for (let kk = Math.floor(x) - 1; kk <= Math.ceil(x + h) + 1; kk++) {
          const lo = kk - del, hi = kk + del;
          if (!CONT) { if (x < hi && x + h > lo) { dead = true; break; } continue; }
          if (hi <= x || lo >= x + h) continue;
          if (lo <= x && hi >= x + h) { dead = true; break; }
          if (lo <= x) czl[k] = Math.max(czl[k], hi - x); else if (hi >= x + h) czr[k] = Math.max(czr[k], x + h - lo); else { dead = true; break; }
        }
        if (dead || czl[k] + czr[k] >= h) { dead = true; break; }
        cx[k] = B[k] * x - Math.floor(B[k] * x); cu[k] += Lb[k]; czl[k] *= B[k]; czr[k] *= B[k];
      }
    }
    if (dead) continue;
    descend(t, cx, cu, czl, czr, depth + 1, w * P[s][d], out);
  }
}
// sample grid per state: product over bases of KX*KU points
const t0 = Date.now();
const offs = [], W8 = [], L8 = []; // per state: list of samples, each list of (w,leaf)
const pre = new Array(NST);
let entries = 0;
for (let s = 0; s < S; s++) for (let q = 0; q < NB; q++) {
  // decode bins
  const ii = [], jj = []; let rem = q; for (let k = nb - 1; k >= 0; k--) { const c = rem % binSize[k]; rem = (rem - c) / binSize[k]; ii[k] = Math.floor(c / Mb[k]); jj[k] = c % Mb[k]; }
  const per = B.map((b, k) => { const pts = []; for (let px = 0; px < KXb[k]; px++) for (let pu = 0; pu < KUb[k]; pu++)
    pts.push([(ii[k] + (px + 0.5) / KXb[k]) / Nb[k], 1 + (Ub[k] - 1) * (jj[k] + (pu + 0.5) / KUb[k]) / Mb[k]]); return pts; });
  let combos = [[]]; for (const pts of per) { const nc = []; for (const c of combos) for (const p of pts) nc.push([...c, p]); combos = nc; }
  const samp = [];
  for (const c of combos) { const out = []; descend(s, c.map(p => p[0]), c.map(p => p[1]), new Array(nb).fill(0), new Array(nb).fill(0), 0, 1, out); samp.push(Float64Array.from(out)); entries += out.length / 2; }
  pre[s * NB + q] = samp;
}
const tPre = (Date.now() - t0) / 1000;
let V = new Float64Array(NST).fill(1), lo = 0;
for (let it = 0; it < IT; it++) {
  const W = new Float64Array(NST); lo = Infinity;
  for (let q = 0; q < NST; q++) { let val = Infinity;
    for (const out of pre[q]) { let sm = 0; for (let e = 0; e < out.length; e += 2) sm += out[e] * V[out[e + 1]]; if (sm < val) val = sm; }
    W[q] = val; if (V[q] > 1e-12) { const rr = val / V[q]; if (rr < lo) lo = rr; } }
  let mx = 0; for (const v of W) if (v > mx) mx = v;
  if (mx === 0) { console.log(`F={${F}} C=${C}: tree DEAD at iteration ${it}`); process.exit(0); }
  for (let q = 0; q < NST; q++) W[q] /= mx; V = W;
}
let z = 0; for (const v of V) if (v < 1e-9) z++;
const g = lam * Math.pow(Math.max(lo, 0), 1 / D);
{const _l=0;}
console.log(`F={${F}} C=${C} D=${D} specs=${specs.map(s => s.join(':')).join(' ')}${CONT ? ' CONT' : ''}${ZERO.length ? ' ZERO=' + ZERO : ''}: states ${NST} leaves ${entries} growth ${g.toFixed(6)} zeros ${z} pre ${tPre.toFixed(1)}s total ${((Date.now() - t0) / 1000).toFixed(1)}s`);

// ---- gate-6 stage 2: this core's own run sums f(R) and layer-cake e'(beta) on REAL cells (env CELLS=kmin:kmax) ----
// Real cell (k,a): sft walk from the MSB; per base b, pending stage p_b = least p with 2 delta_b 2^k < b^p,
// u_b = log2(b^p 2^-k / delta_b), x_b = frac(a b^p / 2^k).  Good = sft alive and touching no resolved window
// of any base in B (the Good449 convention).  Weight = V(state) (sampled screen V, max-normalised to 1).
if (process.env.CELLS) {
  const [kmin, kmax] = process.env.CELLS.split(':').map(Number);
  const pend = (k, kb) => { let p = 0; while (!(2 * dl[kb] * Math.pow(2, k) < Math.pow(B[kb], p))) p++; return p; };
  function stateOf(k, a, s) { const xs = [], us = [];
    for (let kb = 0; kb < nb; kb++) { const p = pend(k, kb), bp = Math.pow(B[kb], p);
      xs.push(((a * bp) % Math.pow(2, k)) / Math.pow(2, k)); us.push(Math.log2(bp / Math.pow(2, k) / dl[kb])); }
    return s * NB + binOf(xs, us); }
  // window test at stage n for base kb: mode 'touch' or 'inside'
  function hit(k, a, kb, n, mode) { const b = B[kb], w = Math.pow(2, -k), lo = a * w * Math.pow(b, n), hi = lo + w * Math.pow(b, n), d = dl[kb];
    for (let A = Math.floor(lo) - 1; A <= Math.ceil(hi) + 1; A++) {
      if (mode === 'touch' ? (lo <= A + d && hi >= A - d) : (lo >= A - d && hi <= A + d)) return true; }
    return false; }
  function good(k, a, k0) { for (let kb = 0; kb < nb; kb++) { const p0 = k0 < 0 ? 0 : pend(k0, kb), p1 = pend(k, kb);
      for (let n = p0; n < p1; n++) if (hit(k, a, kb, n, 'touch')) return false; } return true; }
  function inside(k, a) { for (let kb = 0; kb < nb; kb++) { const b = B[kb], w = Math.pow(2, -k);
      for (let n = 0; Math.pow(b, n) * w <= 2 * dl[kb]; n++) if (hit(k, a, kb, n, 'inside')) return true; } return false; }
  const BETAS = []; for (let n = 6; n < 16; n++) BETAS.push(n / 16); for (let n = 8; n < 49; n++) BETAS.push(n / 8);
  // level-by-level good cells with sft state
  let lev = [[0, 0]];
  const fTot = new Array(65).fill(0), eTot = BETAS.map(() => 0);
  for (let k = 1; k <= kmax; k++) {
    const nx = []; for (const [a, s] of lev) for (const d of [0, 1]) { const t = T[s][d]; if (t < 0) continue; const c = 2 * a + d; if (good(k, c, k - 1)) nx.push([c, t]); }
    lev = nx;
    if (k < kmin || k < 5) continue;
    let fb = new Array(65).fill(0), eb = BETAS.map(() => 0);
    for (const [a, s] of lev) {
      const W = new Array(64).fill(0), alive = new Array(64).fill(false);
      for (let j = 0; j < 64; j++) { let st = s, ok = true; for (let i = 5; i >= 0; i--) { st = T[st][(j >> i) & 1]; if (st < 0) { ok = false; break; } }
        if (!ok) continue; const c = 64 * a + j;
        if (good(k + 6, c, k)) { alive[j] = true; W[j] = V[stateOf(k + 6, c, st)]; } else if (!inside(k + 6, c)) alive[j] = true; }
      const pre = [0]; for (const x of W) pre.push(pre[pre.length - 1] + x);
      for (let R = 0; R <= 64; R++) { let m = 0; for (let i = 0; i + R <= 64; i++) m = Math.max(m, pre[i + R] - pre[i]); fb[R] = Math.max(fb[R], m); }
      BETAS.forEach((be, bi) => { let e = 0; for (let j = 0; j < 64; j++) if (alive[j]) e += Math.max(0, 1 - be * W[j]); eb[bi] = Math.max(eb[bi], e); });
    }
    for (let R = 0; R <= 64; R++) fTot[R] = Math.max(fTot[R], fb[R]); BETAS.forEach((_, bi) => eTot[bi] = Math.max(eTot[bi], eb[bi]));
    console.log(`k=${k}: good ${lev.length} f(8,16,32,64)=${[8, 16, 32, 64].map(R => fb[R].toFixed(3))} e'(1,2,4)=${[1, 2, 4].map(b => eb[BETAS.indexOf(b)].toFixed(3))}`);
  }
  const outp = process.env.KFOUT || `kf_F${F.join('')}.json`;
  fs.writeFileSync(outp, JSON.stringify({ F, f: fTot, betas: BETAS, e: eTot }));
  console.log('wrote', outp);
}
