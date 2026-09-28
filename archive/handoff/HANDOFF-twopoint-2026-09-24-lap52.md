# HANDOFF twopoint — lap 52, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Green, **no `sorry`**;
new theorems `#print axioms`-clean.

## THE SCALE EQUATION IS PROVED

    delange_scale_equation :  ‖z−1‖ ≤ 1  →
        ‖ S(N)·log N  −  z · Abel(N) ‖  ≤  19 · A(N)

with `A(N) = Σ_{n≤N} ‖h(n)‖/n`.  This is the engine of the new route (lap 51): a linear equation in
the *scale* variable whose multiplier `z` has modulus one, with an error measured against `A(N)`,
which is `O((log N)^u)` and hence `o(log N)` exactly in the repo's regime `u = ‖z−1‖ < 1`.

## Bricks landed
1. `log_natDiv_ge` — `log⌊N/n⌋ ≥ log N − log n − log 2` (from `N < n(⌊N/n⌋+1) ≤ 2n⌊N/n⌋`).
2. **`abs_mertens_sub_log_le`** — `|M(⌊N/n⌋) − (log N − log n)| ≤ 11`, the Mertens bracket
   (laps 40–41) plus 1.
3. `norm_delangeSrestr_le_delangeA` — `‖S^{(p)}(M)‖ ≤ A(M)`; no bootstrap anywhere.
4. `sum_log_div_sq_prime_le` — `Σ_{p≤N}(log p)/p² ≤ 8`.
5. **`delange_scale_equation`** — assembles: the two hyperbola identities of lap 51, the
   `S^{(p)} → S` replacement priced at `8A(N)` by (3)+(4), and the Mertens comparison priced at
   `11A(N)` by (2), against `delangeS_mul_log` and `delangeT_eq_prime_sum`.

Everything is an identity or a triangle inequality.  No `‖S‖` bound is assumed at any point.

## What remains of `DelangeKernelMean` (two bricks)
* **(i) `A(N) ≤ C_u·(log N)^u`.**  `delangeA_le_prod` (lap 36) gives `A(N) ≤ Π_{p≤N}(1+u/p)
  ≤ exp(u·Σ_{p≤N}1/p)`, so it needs an *upper* Mertens bound `Σ_{p≤N} 1/p ≤ log log N + C`.
  The tree has `sum_inv_prime_sdiff_le` (a dyadic block bound `≤ (log N + C − log K)/log K`);
  summing it over `⌈log₂ log N⌉` dyadic blocks `K = N^{2^{-j}}` gives exactly `log log N + O(1)`.
  Elementary, one lap.
* **(ii) the discrete integrating factor.**  `Z(N) := Abel(N)·(log N)^{-z}`; from the scale
  equation and `Abel(N+1) − Abel(N) = (log(N+1) − log N)·S(N)`,
  `‖Z(N+1) − Z(N)‖ ≲ A(N)·(log N)^{-1−Re z}·(log(N+1) − log N)`, whose sum converges (or grows
  like `(log N)^{u−Re z}`) by (i).  Then `‖Abel(N)‖ ≲ (log N)^{Re z} + (log N)^{u}` and the scale
  equation itself returns `‖S(N)‖ ≲ (log N)^{Re z−1} + (log N)^{u−1} → 0`.
  This is the discrete analogue of `norm_delangeSv_le`, already in this file — same shape, real
  exponent instead of an exponential.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 70% → **80%**.  The route's only genuinely analytic step (the scale
  equation) is now a theorem; the two remaining bricks are Mertens bookkeeping and a discrete
  Gronwall whose continuous analogue is already formalised in the same file.
