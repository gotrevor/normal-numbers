// Finite-state abstraction of the joint {2,3} system at c=4 (containment kills).
// Box = (binary state (last digit, run 1..3), ternary side config, u-bin, rho-bin).
// y = 3^m xi, cell y-interval [Y, Y+rho], rho in [1/3,1); u = frac(Y); side runs signed (-:0-run,+:2-run), 4 = dead.
// Worst-case value iteration: V' = sum_children min_alternatives min_targets V.
const [N, M1, M2, IT, DEL, CC] = process.argv.slice(2).map(Number); const delta = DEL || 0; const C = CC || 4; const T = C - 1;
const D = C;
const edges = [];
for (let t = 0; t < M1; t++) edges.push((1/3) * Math.pow(2, t / M1));
for (let t = 0; t <= M2; t++) edges.push((2/3) * Math.pow(1.5, t / M2));
const M = M1 + M2;
// side configs: single s in -3..3 (sc 0..6); straddle a,b in 0..7 (value a-3, 7=dead), not both dead
const SC = []; for (let s = -T; s <= T; s++) SC.push([s]);
for (let a = -T; a <= D; a++) for (let b = -T; b <= D; b++) { if (a === D && b === D) continue; if (a===4) {} SC.push([a, b]); }
const scIdx = new Map(SC.map((x, k) => [x.join(','), k]));
const app = (s, d) => { if (s === D) return D; let r = d === 1 ? 0 : d === 0 ? (s < 0 ? s - 1 : -1) : (s > 0 ? s + 1 : 1); return Math.abs(r) >= C ? D : r; };
const binLo = x => Math.max(0, Math.min(N - 1, Math.floor(x * N + 1e-12)));
const binHi = x => Math.max(0, Math.min(N - 1, Math.ceil(x * N - 1e-12) - 1));
const rbins = (lo, hi) => { const r = []; for (let j = 0; j < M; j++) if (edges[j + 1] > lo + 1e-12 && edges[j] < hi - 1e-12) r.push(j); return r; };
const feasible = (sc, i, j) => { const ul = i / N, uh = (i + 1) / N, rl = edges[j], rh = edges[j + 1];
  return SC[sc].length === 1 ? ul + rl < 1 - 1e-12 : uh + rh > 1 + 1e-12; };
// alternatives for (sc,i,j,c): list of null (=kill) or [sc', i0, i1, [js]]
function alts(sc, i, j, c) {
  const ul = i / N, uh = (i + 1) / N, rl = edges[j], rh = edges[j + 1];
  const ll = rl / 2, lh = rh / 2;
  const vl = c ? ul + ll : ul, vh = c ? uh + lh : uh;
  const S = SC[sc]; const kids = []; // [kind, sides, fl, fh]
  if (S.length === 1) kids.push([1, [S[0]], vl, Math.min(vh, 1 - ll)]);
  else {
    if (vl + ll <= 1) kids.push([1, [S[0]], vl, Math.min(vh, 1 - ll)]);
    if (vh >= 1) kids.push([1, [S[1]], Math.max(vl, 1) - 1, vh - 1]);
    if (vl < 1 && vh + lh > 1) kids.push([2, [S[0], S[1]], Math.max(vl, 1 - lh), Math.min(vh, 1)]);
  }
  const out = [];
  const rescale = rh <= 2/3 + 1e-12;
  const nrl = rescale ? 3 * ll : ll, nrh = rescale ? 3 * lh : lh, js = rbins(nrl, nrh);
  const push = (sides, a, b) => {
    a = Math.max(0, a); b = Math.min(1, b); if (a > b + 1e-12) return;
    if (sides.length === 1) { if (sides[0] === D) { out.push(null); return; }
      if (sides[0] === -T && a + nrl < 1/3) { out.push(null); return; }
      if (sides[0] === T && b > 2/3 && a + nrl <= 1) { out.push(null); return; } }
    else { if (sides[0] === D || sides[1] === D) { out.push(null); return; }
      if (sides[0] === T && sides[1] === -T && b > 2/3 && a + nrl < 4/3) { out.push(null); return; } }
    out.push([scIdx.get(sides.join(',')), binLo(a), binHi(b), js]);
  };
  for (const [kind, sides, fl, fh] of kids) {
    if (fl > fh + 1e-12) continue;
    if (kind === 1 && sides[0] === D) { out.push(null); continue; }
    if (!rescale) {
      if (kind === 1) push(sides, fl, fh); else push(sides, fl, fh);
      continue;
    }
    if (kind === 2) { push([app(sides[0], 2), app(sides[1], 0)], 3 * fl - 2, 3 * fh - 2); continue; }
    for (let d = Math.floor(3 * fl); d <= Math.min(2, Math.floor(3 * fh)); d++) {
      const a = Math.max(3 * fl - d, 0), b = Math.min(3 * fh - d, 1);
      if (a + nrl <= 1) push([app(sides[0], d)], a, Math.min(b, 1 - nrl));
      if (d <= 1 && b + nrh > 1) push([app(sides[0], d), app(sides[0], d + 1)], Math.max(a, 1 - nrh), b);
    }
  }
  return out;
}
const NB = SC.length * N * M; const idx = (sc, i, j) => (sc * N + i) * M + j;
const feas = new Uint8Array(NB); const AL = new Array(NB);
for (let sc = 0; sc < SC.length; sc++) for (let i = 0; i < N; i++) for (let j = 0; j < M; j++) {
  const k = idx(sc, i, j); if (!feasible(sc, i, j)) continue; feas[k] = 1; AL[k] = [alts(sc, i, j, 0), alts(sc, i, j, 1)]; }
// binary states: bd = last*3 + (r-1)
const NBD = 2 * T; let V = new Float64Array(NBD * NB).fill(1);
const tmin = (W, bd, t) => { let m = Infinity; for (let i = t[1]; i <= t[2]; i++) for (const j of t[3]) { const k = idx(t[0], i, j); if (feas[k]) { const v = W[bd * NB + k]; if (v < m) m = v; } } return m === Infinity || m < delta ? 0 : m; };
for (let it = 0; it < IT; it++) {
  const W = new Float64Array(NBD * NB); let lo = Infinity, hi = 0;
  for (let bd = 0; bd < NBD; bd++) { const last = (bd / T) | 0, r = bd % T + 1;
    for (let k = 0; k < NB; k++) { if (!feas[k]) continue; let s = 0;
      for (let c = 0; c < 2; c++) { const nr = c === last ? r + 1 : 1; if (nr >= C) continue; const nbd = c * T + nr - 1;
        let m = Infinity; for (const a of AL[k][c]) { const v = a === null ? 0 : tmin(V, nbd, a); if (v < m) m = v; } s += m === Infinity ? 0 : m; }
      W[bd * NB + k] = s; const q = s / V[bd * NB + k]; if (q < lo) lo = q; if (q > hi) hi = q; } }
  let mx = 0; for (let k = 0; k < W.length; k++) if (W[k] > mx) mx = W[k]; for (let k = 0; k < W.length; k++) W[k] /= mx;
  V = W; if (it % 5 === 4 || it === IT - 1) console.log(`it ${it} ratio min ${lo.toFixed(4)} max ${hi.toFixed(4)}`);
}
{ let mn = Infinity, z = 0, n = 0; const hist = {}; for (let bd = 0; bd < NBD; bd++) for (let k = 0; k < NB; k++) if (feas[k]) { const v = V[bd*NB+k]; n++; if (v < 1e-9) z++; else if (v < mn) mn = v; const h = Math.floor(v*10); hist[h]=(hist[h]||0)+1; }
  console.log('boxes', n, 'zeros', z, 'min positive', mn, JSON.stringify(hist)); }

{ // regularity: H_l(box) = max over children/alternatives/targets of H_{l-1}
  const tmax=(H,bd,t)=>{let m=0;for(let i=t[1];i<=t[2];i++)for(const j of t[3]){const k=idx(t[0],i,j);if(feas[k]){const v=H[bd*NB+k];if(v>m)m=v;}}return m;};
  let H=Float64Array.from(V);
  for(let l=1;l<=12;l++){ const H2=new Float64Array(NBD*NB);
    for(let bd=0;bd<NBD;bd++){const last=(bd/T)|0,r=bd%T+1;
      for(let k=0;k<NB;k++){if(!feas[k])continue;let m=0;
        for(let c=0;c<2;c++){const nr=c===last?r+1:1;if(nr>=C)continue;const nbd=c*T+nr-1;
          for(const a of AL[k][c]){if(a===null)continue;const v=tmax(H,nbd,a);if(v>m)m=v;}}
        H2[bd*NB+k]=m;}}
    H=H2; let K=0,cnt=0; for(let x=0;x<H.length;x++) if(V[x]>1e-9){const q=H[x]/V[x]; if(q>K)K=q;}
    const qs=[]; for(let x=0;x<H.length;x++) if(V[x]>1e-9) qs.push(H[x]/V[x]); qs.sort((a,b)=>a-b);
    console.log('l',l,'K',K.toFixed(1),'p99',qs[Math.floor(qs.length*.99)].toFixed(2),'med',qs[qs.length>>1].toFixed(2));}
}
