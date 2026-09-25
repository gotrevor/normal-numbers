# HANDOFF c3-mrt lap 44 — lap 38's indexing debt is PAID; the `K`-point `pair_mass_le` is proved

**Branch** `wip/c3-mrt` · both targets green (`lake build` 9257; `lake build
NormalNumbers.C3MrtBudget` 8980).  Chain tip now
`… → C3MrtMultiMass → C3MrtMultiTrunc → C3MrtMultiTupleMass → C3MrtBudget`.

## What landed: `src/NormalNumbers/C3MrtMultiTupleMass.lean` (sorry-free, trust triple)

* `extendFin` + `range_lcm_extendFin` — the bridge between the two conventions
  (`Fin K`/`Fintype.piFinset`/`Finset.univ.lcm` from lap 36, versus `range K`/`ℕ → ℕ` from lap
  37).  The extension is by `1`, which is `lcm`- and product-neutral.
* `prod_div_univLcm_le` — `prod_div_lcm_le` restated in the `Fin K` convention.
* **`kfold_lcm_mass_le`** — the `K`-point `pair_mass_le`:

      ∑_{d ≤ Y, positive, jointly solvable} (∏_i ‖sqfW z_i (d_i)‖)/lcm(d_i)
          ≤ K^{K²} · ∏_i sqfWMass z_i ,

  uniformly in `Y`, with no `N` anywhere.  This is the total weight the bridge expansion puts on
  the `1/L`-sized inner sums, i.e. the inequality the whole `K`-fold assembly rests on.

## Scoreboard

| step | status |
|---|---|
| 1. `inner_sum_multi_forms` | DONE lap 41 |
| 2. `multi_truncation_bound` | DONE lap 43 |
| 3. indexing debt (`Fin K` vs `range K`) | **DONE lap 44** |
| 4. per-tuple rung bound + ε-chase | next — the only remaining step |
| 5. widen the budget | DONE lap 40 |

## NEXT — step 4, the last one

Mirror laps 29–33 (`inner_pair_bound` → `full_sum_bound` → `two_shift_bound_of_rung`) at `K`:

1. **Per-tuple**: for a positive, jointly solvable `d`, `inner_sum_multi_forms` writes the inner
   sum as a `K`-point correlation along the forms `(L/d_i)X + (a+i+1)/d_i` over an initial
   segment of length `≍ N/L`; feed `KPointLogElliott K` (nondegeneracy from `multi_forms_det`)
   to get `‖inner‖ ≤ η·(N/L) + O(1)`.
2. **Sum over tuples**: weight `∏_i ‖sqfW z_i (d_i)‖` and apply `kfold_lcm_mass_le` — total
   `≤ N·η·K^{K²}·∏_i sqfWMass z_i` plus the truncation error of `multi_truncation_bound`.
3. **ε-chase**: pick `Y` from `ε` using `truncB_tendsto` (the `α·truncA K` term is
   `N`-independent and dies under `1/log N` with no condition on `Y` at all), then `N → ∞`.
   Land in `weylLambertTwist_of_kfold_bound`'s shape.

## Addendum — lap 45: the `K`-fold `full_sum_bound`

`multi_full_sum_bound` (same file, sorry-free, trust triple): given `‖Inner d‖ ≤ 1 + R/lcm(d)`
on the contributing tuples (and `Inner d = 0` off them), the weighted tuple sum is
`≤ ∏_i sqfWPartial z_i Y + R·K^{K²}·∏_i sqfWMass z_i`.  This is the second of the three moves of
step 4; with `multi_truncation_bound` (lap 43) it reduces the whole `K`-fold correlation to the
**per-tuple** bound `‖Inner d‖ ≤ 1 + R/lcm(d)`, which is the only piece of step 4 still open.

Remaining for step 4: (i) the `K`-point `progression_sum_bound`/`inner_pair_bound` — turn
`inner_sum_multi_forms`'s linear-form shape plus `KPointLogElliott K` into that per-tuple bound;
(ii) the ε-chase (`truncB_tendsto`, `bridgeTail_tendsto`) into
`weylLambertTwist_of_kfold_bound`'s shape.

## Addendum — lap 46: step 4's generic analytic core

`src/NormalNumbers/C3MrtMultiInner.lean` (sorry-free, trust triple).  The three ingredients of
`inner_pair_bound` are blind to the number of shifts — they use only `‖G j‖ ≤ 1` — so they are
now stated generically and are available at every `K`:

* `inner_harmonic_le_generic` — peel `j = 0`, transfer `(Lj+a+1)^{-1} → L^{-1}j^{-1}`
  (`weight_transfer`); cost `(a+1)^{-1} + 2/L`.
* `window_gap_generic` — `(0, A^{⌊log_A J⌋}] → (0, J]` costs `1 + log A`.
* `progression_sum_bound_generic` — their composition: the generic `progression_sum_bound`.

What remains of step 4: `multi_rung_spelling` (identify `∑_{Icc 1 J} j^{-1} • ∏_i z_i^{Ω(c_i j +
b_i)}` with `kPointLogCorrelation`'s spelling via `zOmInt_integerAffine`), then `inner_multi_bound`
(feed `inner_sum_multi_forms` + `filter_linear_lt_eq_range` into the generic bound, giving
`‖Inner d‖ ≤ 1 + (3 + R + log A)/L`, exactly `multi_full_sum_bound`'s hypothesis), then the
ε-chase.
