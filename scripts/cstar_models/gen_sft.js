// Binary SFT for containment pruning at exponent C: forbid every word whose cylinder lies inside
// [0, 2^-C] or [1 - 2^-C, 1]; at depth L forbid conservatively every cylinder meeting the window
// (so the model kills MORE than the true containment rule).  Output format = sft45.json.
// usage: node gen_sft.js C L out.json
const fs = require('fs');
const C = Number(process.argv[2]), L = Number(process.argv[3]), out = process.argv[4];
const d2 = Math.pow(2, -C);
// forbidden words, as strings, via DFS from "0..." (the "1..." ones are complements)
const forb = [];
function dfs(w, v, len) { // cylinder [v, v + 2^-len]
  const hi = v + Math.pow(2, -len);
  if (hi <= d2) { forb.push(w); return; }
  if (v >= d2) return;
  if (len === L) { forb.push(w); return; }
  dfs(w + '0', v, len + 1); dfs(w + '1', v + Math.pow(2, -len - 1), len + 1);
}
dfs('', 0, 0);
const all = forb.concat(forb.map(w => w.replace(/./g, ch => ch === '0' ? '1' : '0')));
// Aho-Corasick trie on all forbidden words; states = proper prefixes not containing a forbidden word
const states = [''], idx = { '': 0 };
const isForb = s => all.some(f => s.endsWith(f));
for (const f of all) for (let k = 1; k < f.length; k++) { const p = f.slice(0, k); if (!(p in idx)) { idx[p] = states.length; states.push(p); } }
const longestState = s => { for (let k = 0; k <= s.length; k++) { const t = s.slice(k); if (t in idx) return idx[t]; } return 0; };
const T = states.map(s => [0, 1].map(b => { const n = s + b; return isForb(n) ? -1 : longestState(n); }));
// prune states with no infinite continuation
let alive = states.map(() => true), ch = true;
while (ch) { ch = false; for (let i = 0; i < states.length; i++) if (alive[i] && !T[i].some(t => t >= 0 && alive[t])) { alive[i] = false; ch = true; } }
for (let i = 0; i < states.length; i++) T[i] = T[i].map(t => t >= 0 && alive[t] ? t : -1);
// Perron eigenvector by power iteration: lam r_s = sum_d r_{T[s][d]}
let r = states.map(() => 1), lam = 0;
for (let it = 0; it < 20000; it++) { const n = T.map(t => (t[0] >= 0 ? r[t[0]] : 0) + (t[1] >= 0 ? r[t[1]] : 0)); lam = n[0] / r[0]; const m = Math.max(...n); r = n.map(x => x / m); }
// normalise r[0]=1
r = r.map(x => x / r[0]);
console.log(`C=${C} L=${L}: ${states.length} states, ${alive.filter(x => x).length} live, lam=${lam}`);
if (out) fs.writeFileSync(out, JSON.stringify({ T, r, lam, states, C, L }));
