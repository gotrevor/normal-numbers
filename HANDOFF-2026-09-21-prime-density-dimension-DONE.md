# HANDOFF 2026-09-21: prime-density dimension DISCHARGED

Scope: `KICKOFF-prime-density-dimension.md` (attended override).  Both named targets proved,
`lake build` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on both.

## New module

`src/NormalNumbers/PrimeModelPrimeDimension.lean` (namespace
`NormalNumbers.PrimeModel.PrimeDensity`), imported from `src/NormalNumbers.lean`.  Zero `sorry`,
no new dependency, no pin change, no edit to any existing proof module.

### `prime_density_dimension`

    theorem prime_density_dimension {h y : ℕ} (hh : 1 ≤ h) (hy : 2 ≤ y) {U : Finset ℕ}
        (hU : ∀ p ∈ U, Nat.Prime p ∧ h < p ∧ p ≤ y) :
        Brun.Dimension U (fun p => (h : ℝ) / p) y ((4 : ℝ) ^ h * Real.exp (16 * h)) (24 * h)

`Brun.Dimension` is untouched.  Hypotheses are exactly: `h ≥ 1`, `y ≥ 2`, and every `p ∈ U`
prime with `h < p ≤ y`.  No analytic hypothesis.

### `prime_density_brun_lower`

`brun_lower_fundamental` instantiated at `K = 4^h exp(16h)`, `k = 24h`, `g p = h/p`.  Remaining
hypotheses: `h ≥ 1`, `exp 2 ≤ y`, `80*(24h) ≤ s`, `40 log(4^h exp(16h)) + 4 ≤ s`, and the same
elementary condition on `U`.  Conclusion carries **all three** weight properties verbatim
(coefficient/support bound, pointwise minorant, `(1 - 2 exp(-s/2)) ∏(1-h/p) ≤ ∑ λ ∏ g`), not an
existential wrapper.

## Proof route (as executed)

* `inv_one_sub_le_exp` : `(1-x)⁻¹ ≤ exp(2x)` for `0 ≤ x ≤ 1/2`, via `exp(-2x) ≤ (1+2x)⁻¹ ≤ 1-x`
  (the last step is `2x² ≤ x`).  Elementary; no Taylor machinery.
* `prod_Ioc_inv_eq_centralBinom` : `∏_{m=h+1}^{2h} (1-h/m)⁻¹ = C(2h,h)`, by reindexing
  `Ioc h (2h)` onto `range h` and `Nat.ascFactorial_eq_factorial_mul_choose`; then
  `Nat.centralBinom_le_four_pow` gives the small-prime cap `4^h`.  This is the concrete
  small-prime control the kickoff asked for: it is exact, not an estimate.
* `block_le_eight` : for real `v ≥ 2`, `∑_{v<p≤v²} 1/p ≤ 8`.  Termwise `1/p ≤ (log p/p)/log v`,
  then `Radical.mertens_crude ⌊v²⌋ ≤ 4 log ⌊v²⌋ ≤ 8 log v`.  **`v` is real throughout** — an
  earlier plan that floored `v` to a natural lost `log 2` per block and broke the constant.
* `primeRecipSum_le_blocks` : induction on `n`, `∑_{v<p≤N} 1/p ≤ 8n` when `N ≤ v^(2^n)`; the
  step splits at `v²` and recurses with base `v²`.
* `primeRecipSum_le` : with `L = log y / log v ≥ 1` and `n = ⌈logb 2 L⌉₊`, `Nat.ceil_lt_add_one`
  gives `8n ≤ 8 + (8/log 2) log L ≤ 8 + 12 log L` (needs `8 ≤ 12 log 2`, from
  `Real.log_two_gt_d9`).  Slack here is thin: `8/log 2 = 11.54`.
* Assembly: split `U.filter (t < ·)` at `p ≤ 2h`; small part `≤ 4^h`, large part
  `≤ exp(2h ∑ 1/p) ≤ exp(16h) L^(24h)`.  Constants come out exactly as the assessment predicted.

## Remaining application work (not in scope here)

The sieve's dimension input is now unconditional.  Still open downstream: the arithmetic and
probability assembly of `papers/prime-model-sieve-assessment.md` (turning the three weight
properties into the selected-prime counting estimate), and checking the size conditions
`exp 2 ≤ y`, `s ≥ max(1920 h, 40 log K + 4)` in the target regime `Y = ⌊x^ε⌋`,
`s = log R / log Y`.  Note `log K = h(log 4 + 16) ≈ 17.4 h`, so `hsA` reads `s ≳ 696 h`;
`hs80` (`s ≥ 1920 h`) is the binding one.

Lemma-name gotchas hit this lap (mathlib pin of this repo): `inv_le_inv_of_le` → `inv_anti₀`;
`div_le_div_iff` → `div_le_div_iff₀`; `Finset.prod_le_prod_of_subset_of_one_le'` has no ℝ
instance — use the `GroupWithZero` variant `Finset.prod_le_prod_of_subset_of_one_le` (takes an
extra nonnegativity argument); `Finset.filter` over ℕ with a real-cast predicate needs an
explicit `fun p : ℕ =>` binder or Lean elaborates the filter at `Finset ℝ`.
