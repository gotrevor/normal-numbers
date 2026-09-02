# Berend-Boshernitzan 1994: Mahler multiples 📌

**Pinned 2026-08-30.**  Daniel Berend and Michael D. Boshernitzan, “On a
result of Mahler on the decimal expansions of (n alpha),” *Acta Arithmetica*
66 (1994), 315-322.  DOI `10.4064/aa-66-4-315-322`.

- Local PDF: `berend-boshernitzan-1994-mahler-multiples.pdf` (8 pages,
  gitignored).
- SHA-256:
  `3a65a8516a6c9c064c9cd4371d1e3ce77225183772169481000be1d63f1fed37`.
- Source: `matwbn.icm.edu.pl/ksiazki/aa/aa66/aa6642.pdf`.

## Results used in the tower audit

Theorem 1.1 improves the universal upper bound for realizing one specified
length-`k` word to a multiplier below `2*g^(k+1)`.  Their polynomial
extension is Theorem 1.2.

The decisive sentence is on page 318.  They prove `M(g,k) >= g^k-1` and
state that equality holds for `g=2,k=1` and `g=3,k=1`.  Therefore
`M(3,1)=2`, exactly:

> for every irrational `x` and every ternary digit `d`, `d` occurs
> infinitely often in `x` or in `2x`.

Tower claim C1 is a rediscovery of this result.  The paper does not state the
fixed all-digits set `{2,11}`.


## §3 lower bounds (added 2026-09-02, full read)

The 2026-08-30 pin stopped at Proposition 3.1.  §3 goes much further:
**Theorem 3.1** `M(g,k) ≥ a(gᵏ−1)` for any proper divisor `a | g`;
**Theorem 3.2** `M(g,k) ≥ (1−ε)g^(k+1)` for `k ≥ K(ε)` when `g` is not a prime
power; **Example 3.1** `M(10,k) ≥ 8(10ᵏ−1)` for `k ≥ 1` (and `9.765(10ᵏ−1)` for
`k ≥ 7`); **Theorem 3.3** `M(g,1) ≥ (3/2)(g−1)` for odd `g ≥ 5`.  They state
`M(g,k) < g^(k+1)?` as OPEN.  Full transcription + repo implications →
`ON-LINE-FINDINGS-2026-09-02-berend-boshernitzan-1994.md`.
