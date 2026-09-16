# HANDOFF 2026-09-16 — campaign A: Mertens in arithmetic progressions is PROVED

Branch `wip/g5-prime-subset`.  `lake build` green (9043 jobs), `src/NormalNumbers/G4MertensAP.lean`
is **sorry-free**, every theorem `[propext, Classical.choice, Quot.sound]`.

## What landed

`NormalNumbers.G4.MertensAP.mertensRate_residueClass (ha : IsUnit a) :`
`∃ c C, MertensRate (fun p => (p : ZMod q) = a) c C`, i.e. for a unit class `a` mod `q` there is
`c > 0` with `∑_{p < N, p ≡ a (q)} 1/p ≥ c·log log N − C` for all `N ≥ 2`.  **Mertens' theorem in
arithmetic progressions is not in mathlib**; this is the campaign's crux, and it is now in-kernel.

Chain (all in `G4MertensAP.lean`):
1. `LSeries_residueClass_primes_ge` — mathlib's `LSeries_residueClass_lower_bound` minus the
   prime-power part (`summable_residueClass_non_primes_div`, compared termwise at `x ≥ 1`).
2. `dyadic_block_le` / `tail_finset_le` / `sumLog_tail_le` — the Dirichlet tail beyond `2^{k₀}` is
   `≤ 2 log 4 · 2^{−k₀δ}/(1 − 2^{−δ})`, from `Chebyshev.theta_le_log4_mul_x` on each dyadic block
   plus a geometric series.  No Abel summation, no integrals.
3. `sumLog_ge_of_LSeries_ge` — split at `2^{k₀}`, `x = 1 + λ/(k₀ log 2)`, `λ = max 1 log(17/c)`:
   the tail eats at most half the pole, giving `∑_{p∈S,p<N} log p/p ≥ c' log N − C'`.
4. `mertensRate_of_sumLog` — dyadic partial summation (`abel_parts` on `NN j = 2^(2^j)`), giving
   `c/(2 log 2)·log log N − C''`.  No Mertens *upper* bound needed.

## Why this is the right interface

`DESIGN-2026-09-16-prime-subset.md` (audit lap): the schedule's cutoff exponent `e` (`R = 2^{2^e}`)
is capped above by `Mc ≤ 2^{8K²}`, so bare divergence of `∑_{p∈S} 1/p` is NOT enough for the G4
route — a *rate* is, and any fixed `c > 0` suffices because the window for `e` is
`[exp(O(K log K)), exp(Θ(K²))]`.  `MertensRate S c C` is exactly that hypothesis.

## Resume at (A3, then A4)

* **A3** — `e`-parametrize `G4SchedB*`: replace `m₁ b K` by a free exponent `e` in
  `G4SchedBParams` (`R Y X Mc m`, `sum_inv_smallPrimes_ge/le`, `dyadic_factor_le`,
  `R_pow_two_Mc_le`), consuming `MertensRate` in place of `sum_inv_smallPrimes_ge`.  The
  generic-in-`e` harmonic bounds already exist: `G4EntropyMTowerHarmonic.sum_inv_smallPrimes_*_gen`.
  Constraint list with the exact declarations: `DESIGN-2026-09-16-prime-subset.md` §"The four
  constraints".
* **A4** — `G4SubsetWeight.lean` (override item 1): `omegaS`, `subsetLambert`, `omegaS_mul`,
  `overlapS_congr`, the `Frame` instance; then `isDisjunctive_residueClass`.
