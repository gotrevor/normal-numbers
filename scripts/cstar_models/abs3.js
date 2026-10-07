// nu-weighted joint {2,3} abstraction with base-3 touching kills at resolution R.
// state (sigma, x-bin i, u-bin j): x = left endpoint mod 1 in units of the pending ternary stage,
// rho = cell size in those units, u = log2(rho/(delta/R)) in (0, log2 6].
// V'(s,i,j) = sum_d P(s,d) * (killed ? 0 : min_{targets} V(s_d, i', j')).
// usage: node abs3.js N M R IT [C]
const fs = require('fs');
const [N, M, R, IT] = process.argv.slice(2, 6).map(Number);
const C = Number(process.argv[6] || 4.5);
const sft = JSON.parse(fs.readFileSync(process.argv[7] || 'sft45.json'));
const S = sft.T.length, T = sft.T, r = sft.r, lam = sft.lam;
const delta = Math.pow(3, -C) * 1.0001;
const eps = 1e-12;
const U = Math.log2(6);
// u in (1, log2 6]; edges: M1 bins on (1,2], M2 bins on (2,U]
const M2 = Math.max(1, Math.round(M * (U - 2) / (U - 1))), M1 = M - M2;
const edges = []; for (let t = 0; t <= M1; t++) edges.push(1 + t / M1); for (let t = 1; t <= M2; t++) edges.push(2 + (U - 2) * t / M2);
const binLo = v => { let j = 0; while (j < M - 1 && edges[j + 1] <= v + eps) j++; return j; };
const binHi = v => { let j = M - 1; while (j > 0 && edges[j] >= v - eps) j--; return j; };
const rhoOf = u => (delta / R) * Math.pow(2, u);
// per (i,j,d): kill flag, target i-range [a,b] (may wrap, b-a < N), j-range [ja,jb]
const NB = N * M;
const kill = new Uint8Array(NB * 2), ia = new Int32Array(NB * 2), ib = new Int32Array(NB * 2), ja = new Int32Array(NB * 2), jb = new Int32Array(NB * 2);
for (let i = 0; i < N; i++) for (let j = 0; j < M; j++) for (let d = 0; d < 2; d++) {
  const k = ((i * M) + j) * 2 + d;
  const ulo = edges[j], uhi = edges[j + 1];
  const rlo = rhoOf(ulo), rhi = rhoOf(uhi);
  // child
  let xlo = i / N + d * rlo / 2, xhi = (i + 1) / N + d * rhi / 2;
  const clo = rlo / 2, chi = rhi / 2;
  let nulo = ulo - 1, nuhi = uhi - 1;
  // resolve if possibly u-1 <= 1 ... u bins straddling the threshold: treat by splitting? use worst: if any part resolves, need both behaviours.
  // We require bins aligned so that threshold u=2 (before subtracting) is a bin edge: choose M so 2/du integer is approximately true; else conservative.
  const resolves = (nuhi <= 1 + eps), maybe = (nulo < 1 - eps && nuhi > 1 + eps);
  if (maybe) throw new Error('bin straddles resolve threshold; choose M with 2*M/log2(6) integer-ish');
  if (resolves) {
    // touch check with windows [k-delta, k+delta]: child interval [x, x+c] with x in [xlo,xhi), c in [clo,chi]
    // possibly touches if exists k: xlo <= k+delta and xhi + chi >= k-delta
    let touches = false;
    for (let kk = Math.floor(xlo - 1); kk <= Math.ceil(xhi + chi + 1); kk++) {
      if (xlo <= kk + delta + eps && xhi + chi >= kk - delta - eps) { touches = true; break; }
    }
    if (touches) { kill[k] = 1; continue; }
    xlo = 3 * xlo; xhi = 3 * xhi; nulo += Math.log2(3); nuhi += Math.log2(3);
  }
  // target x bins (mod 1)
  const a = Math.floor(xlo * N + eps), b = Math.ceil(xhi * N - eps) - 1;
  ia[k] = a; ib[k] = b;
  // target u bins
  ja[k] = binLo(nulo); jb[k] = binHi(nuhi);
}
let V = new Float64Array(S * NB).fill(1);
const P = []; for (let s = 0; s < S; s++) P.push([0, 1].map(d => T[s][d] < 0 ? 0 : r[T[s][d]] / (lam * r[s])));
let ratioLo = 0;
for (let it = 0; it < IT; it++) {
  const W = new Float64Array(S * NB);
  let lo = Infinity, hi = 0;
  for (let s = 0; s < S; s++) for (let i = 0; i < N; i++) for (let j = 0; j < M; j++) {
    let sum = 0;
    for (let d = 0; d < 2; d++) {
      const t = T[s][d]; if (t < 0) continue;
      const k = ((i * M) + j) * 2 + d;
      if (kill[k]) continue;
      let mn = Infinity;
      for (let x = ia[k]; x <= ib[k]; x++) { const xi = ((x % N) + N) % N; const base = t * NB + xi * M;
        for (let y = ja[k]; y <= jb[k]; y++) { const v = V[base + y]; if (v < mn) mn = v; } }
      sum += P[s][d] * mn;
    }
    const idx = s * NB + i * M + j; W[idx] = sum;
    const q = sum / V[idx]; if (q < lo) lo = q; if (q > hi) hi = q;
  }
  let mx = 0; for (let k = 0; k < W.length; k++) if (W[k] > mx) mx = W[k];
  for (let k = 0; k < W.length; k++) W[k] /= mx;
  V = W; ratioLo = lo;
  if (it % 10 === 9 || it === IT - 1) console.log(`it ${it} ratio min ${lo.toFixed(5)} max ${hi.toFixed(5)}`);
}
let z = 0, mn = Infinity; for (let k = 0; k < V.length; k++) { if (V[k] < 1e-9) z++; else if (V[k] < mn) mn = V[k]; }
console.log(`N=${N} M=${M} R=${R} C=${C}: eta_cert ~ ${(1 - ratioLo).toFixed(5)}  zeros ${z}/${V.length} minpos ${mn.toExponential(3)}`);
