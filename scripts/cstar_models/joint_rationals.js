// Rationals p/q (gcd(q,6)=1, gcd(p,q)=1) good for every base 2..Bm coprime to q at exponent c:
// p avoids W*<b> where W = window residues |w| <= q b^-c.  Prints q and survivor count.
// Usage: node joint_rationals.js c Qmax Bm
const [c, Q, Bm] = [parseFloat(process.argv[2]), parseInt(process.argv[3]), parseInt(process.argv[4])];
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
const bad = new Uint8Array(Q + 1), mark = new Uint8Array(Q + 1);
let tot = 0, nq = 0;
for (let q = 5; q <= Q; q++) {
  if (gcd(q, 6) !== 1) continue;
  bad.fill(0, 0, q);
  for (let b = 2; b <= Bm; b++) {
    if (gcd(b, q) !== 1) continue;
    const R = Math.floor(q * Math.pow(b, -c)); mark.fill(0, 0, q);
    for (let w = -R; w <= R; w++) {
      const x = ((w % q) + q) % q; if (mark[x]) continue;
      let y = x; do { mark[y] = 1; bad[y] = 1; y = (y * b) % q; } while (y !== x);
    }
  }
  let cnt = 0; for (let p = 1; p < q; p++) if (!bad[p] && gcd(p, q) === 1) cnt++;
  if (cnt) { tot += cnt; nq++; console.log(q, cnt); }
}
console.log('total', tot, 'denominators', nq);
