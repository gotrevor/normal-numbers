# HANDOFF — retained-box tail and phase transfer COMPLETE

Branch: `proof/prime-model-complement`.  HEAD `644a757`.
Full `lake build` GREEN (pre-commit hook, 9106 jobs).  Scope of
`KICKOFF-radical-tail.md` is complete; nothing in it is left open.

## Delivered

`src/NormalNumbers/PrimeModelRadicalTail.lean` (new, imported from
`src/NormalNumbers.lean`), namespace `NormalNumbers.PrimeModel.Radical`.
No `sorry`, no `axiom`; `radical_box_tail`, `radical_box_phase_transfer`,
`radSize_rpow` all `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
No frozen statement touched (pure addition).

* `radSize p j s = ∏_i (if s i = some j then (p i : ℝ) else 1)` and
  `retainedBox k p T = {s : ∀ j, d_j(s) ≤ T}` (Classical-decidable filter).
* `radSize_rpow`: `d_j(s)^α = ∏_i (if s i = some j then (p i)^α else 1)` —
  **proved** via `Real.finsetProd_rpow`, as the kickoff required.
* `radical_radSize_moment_le_exp`: `E[d_j^α] ≤ exp A` from the budget
  `∑_i ((p i)^α - 1)/(p i) ≤ A`, on top of `radical_site_moment_le_exp`.
* `radical_shift_markov`, `sum_compl_retainedBox_le` (reusable union bound).
* `radical_box_tail`: `∑_{s ∉ B(T)} weight ≤ k · exp A / T^α` (`T ≥ 1`, `α > 0`).
* `radical_box_phase_transfer`: `≤ 2·(k exp A / T^α) + 2δ`, by composing the
  tail with `PrimeModel.probability_complement_phase` (reused, not reproved).
* Numeric anchors, state space expanded by hand: `k = 2`, primes `3,5`;
  `T = 1,2 ↦ 4/5`, `T = 3 ↦ 2/5`, `T = 5 ↦ 2/15`, `T = 15 ↦ 0`.
* `papers/prime-model-radical-tail.md` records the remaining obligations.

`A ≤ 20` and the retained `L¹` discrepancy `δ` remain explicit **hypotheses**;
neither is hidden in an axiom.

## Pin gotchas (mathlib @ lean4 v4.33.1)

- `Real.finset_prod_rpow` is deprecated → `Real.finsetProd_rpow`.
- `Finset.one_le_prod'` needs a multiplicative ordered monoid; for `ℝ` use
  `1 = ∏ 1 ≤ ∏ f` via `Finset.prod_le_prod`.
- Under `open scoped Classical`, the `reduceIte` simproc cannot fire (the
  instance is `Classical.propDecidable`).  Reduce constructor conditions with
  `simp only [reduceCtorEq, Option.some.injEq, Fin.reduceEq, if_false, if_true]`
  *before* `norm_num`; plain `norm_num` leaves `if none = some 0` untouched.
- Subtype tail sums: `tsum_fintype` then
  `(Finset.sum_subtype Bᶜ (by simp) f).symm` converts
  `∑' s : {s // s ∉ B}, f s` to `∑ s ∈ Bᶜ, f s`.

## Next steps

1. This scope is closed.  Downstream consumers use `radical_box_tail` /
   `radical_box_phase_transfer` directly.
2. To instantiate `A`: the two arithmetic inputs listed in
   `papers/prime-model-radical.md` (§`p^α - 1 ≤ √e α log p`, Mertens).
3. To instantiate `δ`: the two-sided sieve fundamental lemma — a separate
   campaign, deliberately not started here.
4. The repo's real crux (`RoughIndependenceAt h 2`, `ParityDiscrepancy`) is on
   other branches and untouched by this lap.
