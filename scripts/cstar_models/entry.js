// Entry states for CleanCertificate449: cells at levels k <= KE (cell size > 6 delta in stage-0 units)
// get their own weight w(k,a) = min(1, g^-D * sum over clean depth-D descendants of their weight),
// descendants at regular levels weighted by the certified bin weights V (dump of exactinf3.c ... dump).
// usage: node entry.js vdump N M D C G sft.json
const fs = require('fs');
const [vf, N, M, D, C, G, sf] = [process.argv[2], +process.argv[3], +process.argv[4], +process.argv[5], +process.argv[6], +process.argv[7], process.argv[8]];
const sft = JSON.parse(fs.readFileSync(sf)); const T = sft.T;
const V = new Float64Array(sft.T.length * N * M);
for (const line of fs.readFileSync(vf, 'utf8').split('\n')) if (line.startsWith('V ')) { const [, q, v] = line.split(' '); V[+q] = +v; }
const delta = Math.pow(3, -C), U = Math.log2(6);
const M2 = Math.max(1, Math.round(M * (U - 2) / (U - 1))), M1 = M - M2; const edges = [];
for (let t = 0; t <= M1; t++) edges.push(1 + t / M1); for (let t = 1; t <= M2; t++) edges.push(2 + (U - 2) * t / M2);
const ubin = u => { let j = 0; while (j < M - 1 && edges[j + 1] < u) j++; return j; }; // bins (e_j, e_{j+1}]
let amb = 0;
// sft state of the k-bit word of a (or -1 if dead)
const sftState = (k, a) => { let s = 0; for (let i = k - 1; i >= 0; i--) { s = T[s][(a >> i) & 1]; if (s < 0) return -1; } return s; };
const clean = (k, a) => { // base-3 resolved stages: 3^n <= 2 delta 2^k
  for (let n = 0; Math.pow(3, n) <= 2 * delta * Math.pow(2, k); n++) {
    const lo = Math.pow(3, n) * a / Math.pow(2, k), hi = Math.pow(3, n) * (a + 1) / Math.pow(2, k);
    const A = Math.round((lo + hi) / 2); // nearest centre candidates
    for (const c of [Math.floor(lo), Math.ceil(hi), A]) { const d = Math.max(c - delta - hi, lo - c - delta);
      if (Math.abs(d) < 1e-9) amb++; if (d <= 0) return false; }
  }
  return true;
};
const regular = k => { // pending stage n: least with 3^n > 2 delta 2^k; u = log2(3^n 2^-k / delta) in (1, log2 6]
  let n = 0; while (Math.pow(3, n) <= 2 * delta * Math.pow(2, k)) n++;
  const u = Math.log2(Math.pow(3, n) / Math.pow(2, k) / delta); return { n, u, ok: u > 1 && u <= U + 1e-12 };
};
const wReg = (k, a) => { const s = sftState(k, a); if (s < 0 || !clean(k, a)) return 0;
  const { n, u } = regular(k); const x = (Math.pow(3, n) * a / Math.pow(2, k)) % 1; // exact enough for k <= ~12
  const i = Math.min(N - 1, Math.floor(x * N)); return V[s * N * M + i * M + ubin(u)]; };
let KE = 0; while (!regular(KE + 1).ok || !regular(KE).ok && true) { if (regular(KE).ok) break; KE++; }
console.log(`first regular level ${KE}; levels:`, [0,1,2,3,4,5,6,7].map(k => `${k}:${regular(k).ok ? 'reg' : 'early'}(u=${regular(k).u.toFixed(3)})`).join(' '));
const gD = Math.pow(G, D); const W = {};
const weight = (k, a) => { if (regular(k).ok) return wReg(k, a); const key = k + ',' + a; if (key in W) return W[key];
  if (sftState(k, a) < 0 || !clean(k, a)) return W[key] = 0;
  let sm = 0; for (let j = 0; j < (1 << D); j++) sm += weight(k + D, (a << D) + j); return W[key] = Math.min(1, sm / gD); };
const root = weight(0, 0);
console.log(`root weight ${root}  (early cells: ${Object.keys(W).length}, positive ${Object.values(W).filter(v => v > 0).length}), ambiguous checks ${amb}`);
