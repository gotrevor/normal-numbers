# Mahler 1973: digits of multiples 📌

**Pinned 2026-08-30.**  K. Mahler, “Arithmetical properties of the digits of
the multiples of an irrational number,” *Bulletin of the Australian Mathematical
Society* 8 (1973), 191-203.  DOI `10.1017/S000497270004243X`.

- Local PDF: `mahler-1973-digits-of-multiples.pdf` (13 pages, gitignored).
- SHA-256:
  `263facae776cfc081d99eafc3ab93e29ebc4b213482c0a9adc97342aa99b7288`.
- Source:
  `cambridge.org/core/services/aop-cambridge-core/content/view/90925FC7965783036BF2428FE1039065/S000497270004243Xa.pdf`.

## Results used in the tower audit

**Theorem 1.**  Given a positive irrational `alpha`, base `g`, and one
specified word of length `n`, there is a positive integer `X < g^(2n+1)`
for which that word occurs infinitely often in `X alpha`.

**Theorem 2.**  Mahler chooses a length `g^N+N-1` word containing every
length-`N` word, then applies Theorem 1.  Therefore one multiplier `X`
makes every possible length-`N` word occur infinitely often.  The resulting
bound is

    X < g^(2*g^N + 2*N - 1).

For base 3 and `N=1`, this gives `X < 3^7`.  Thus the qualitative statement
“some multiple of every irrational contains all three ternary digits infinitely
often” is already in Mahler.  C2's possible novelty is the fixed universal set
`{2,11}`, not simultaneous realization by an existential multiplier.

