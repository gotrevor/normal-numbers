// Exact check: the minimal forbidden words of Forb2 (Lean, delta2hi = 4451/100000) vs sft449.json's words.
// Forb2 L v: L<=13 and ((v+1)/2^L < d or 1-d < v/2^L or (L=13 and (v/2^13 < d or 1-d < (v+1)/2^13)))
const P = 4451n, Q = 100000n;
const forb = (L, v) => { const t = 1n << BigInt(L); v = BigInt(v);
  if ((v + 1n) * Q < P * t) return true; if ((Q - P) * t < v * Q) return true;
  if (L === 13 && (v * Q < P * t || (Q - P) * t < (v + 1n) * Q)) return true; return false; };
const words = [];
for (let L = 1; L <= 13; L++) for (let v = 0; v < (1 << L); v++) if (forb(L, v)) {
  const w = v.toString(2).padStart(L, '0');
  // minimal: no proper substring forbidden
  let min = true; for (let i = 0; i < L && min; i++) for (let j = i + 1; j <= L; j++) if (j - i < L && forb(j - i, parseInt(w.slice(i, j), 2))) { min = false; break; }
  if (min) words.push(w); }
console.log(JSON.stringify(words.sort()));
