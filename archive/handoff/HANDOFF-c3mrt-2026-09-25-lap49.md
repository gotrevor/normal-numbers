# HANDOFF c3-mrt lap 49 — the `K`-fold assembly is COMPLETE down to one named input

**Branch** `wip/c3-mrt` · both targets green (`lake build` 9257; `lake build
NormalNumbers.C3MrtBudget` 8982).  Chain:
`… → C3MrtMultiMass → C3MrtMultiTrunc → C3MrtMultiTupleMass → C3MrtMultiInner →
C3MrtMultiChase → C3MrtBudget`.

## What landed this session (laps 43–49), all sorry-free, all `[propext, Classical.choice, Quot.sound]`

| lap | file | declaration |
|---|---|---|
| 43 | `C3MrtMultiTrunc` | `truncA`/`truncB`, `multi_truncation_telescope`, `multi_truncation_bound`, `truncB_tendsto` |
| 44 | `C3MrtMultiTupleMass` | `extendFin`, `range_lcm_extendFin`, `prod_div_univLcm_le`, `kfold_lcm_mass_le` |
| 45 | `C3MrtMultiTupleMass` | `multi_full_sum_bound` |
| 46 | `C3MrtMultiInner` | `inner_harmonic_le_generic`, `window_gap_generic`, `progression_sum_bound_generic` |
| 47 | `C3MrtMultiInner` | `multi_rung_spelling`, `inner_multi_bound` |
| 48 | `C3MrtMultiInner` | `multi_bound_of_rung` |
| 49 | `C3MrtMultiChase` | `univLcm_le_prod`, `univLcm_le_pow`, **`multi_correlation_of_uniform_rung`** |

## The state of the route

**`multi_correlation_of_uniform_rung`**: for every `K ≥ 1`, granting the rung *uniformly over
the admissible tuples below each `Y`* — literally the shape `rung_two_uniform` delivers at
`K = 2` — the harmonically weighted `K`-point correlation of `z_i^ω` at the shifts
`n+1, …, n+K` satisfies `‖·‖ ≤ C + ε·log N` for every `ε > 0`.

So **all five steps of the `K`-fold assembly are done**, and the `D ≥ 3` route's remaining
obligation is exactly one hypothesis, `hrungU`:

> a `K`-point rung, uniform over the finitely many admissible tuples below `Y`, at the windows
> `(0, A^m]` with `m ≥ I`, of the form `(1 + log A^I) + m·εr·log A`.

At `K = 2` that is `rung_two_uniform`, proved in lap 32 from `NonasymptoticLogElliott` + the
archimedean certificate + `TwistedPrimeSumSavingAllLevels`.  At `K ≥ 3` it is
`KPointLogElliott K` (= Tao–Teräväinen's `ProductLogElliott`, per laps 35–39) plus the SAME
certificate — the non-pretentiousness hypothesis constrains only the first factor, which is
untouched by adding shifts.

## NEXT

`rung_multi_uniform`: the `K`-point `rung_two_uniform`.  Two moves, both modelled on lap 32:
1. `rung_multi_of_named_inputs` — feed `KPointLogElliott K` at the nondegenerate forms
   `(L/d_i)X + (a+i+1)/d_i` (nondegeneracy: `multi_forms_det`), with the archimedean
   certificate `nonPretentious_zOm` for the first factor, to get a per-tuple window bound;
2. `exists_common_threshold` over the finite set of admissible tuples (`Fin K → ℕ` with entries
   `≤ Y`, base points `< Y^K`) to make `A`, `I` uniform.

Then `multi_correlation_of_uniform_rung` + `weylLambertTwist_of_kfold_bound` closes the
`D ≥ 3` rung on `KPointLogElliott K` alone, and the crux's ledger is complete.

## Addendum — lap 50: `initial_segment_bound_of_kElliott`

`src/NormalNumbers/C3MrtMultiRung.lean` (sorry-free, trust triple).  The `K`-point
`initial_segment_bound_of_elliott`: `KPointLogElliott K` at nondegenerate forms
`(c_i, b_i)` gives, for every `A ≥ A₀` and every `i₀` at which the archimedean certificate
holds,

    ‖∑_{j ≤ A^m} harmonicWeight j · ∏_i zOmInt z_i (integerAffine c_i b_i j)‖
        ≤ (1 + log A^{i₀}) + m·ε·log A .

**The archimedean side does not grow with `K`.**  `KPointLogElliott` constrains only the FIRST
factor's pretentiousness, so the certificate `nonPretentious_zOm` (laps 18–21) is reused
verbatim at every `K` — no new archimedean work is needed for `D ≥ 3`.  That was the last
place where the `D ≥ 3` route could have demanded a genuinely new analytic input beyond the
`K`-point correlation itself; it does not.

Remaining: `rung_multi_of_named_inputs` (plug `nonPretentious_zOm` + `TwistedPrimeSumSavingAllLevels`
into the above, mirroring `rung_two_of_named_inputs` exactly) and then `rung_multi_uniform`
(`exists_common_threshold` over the finitely many admissible tuples), which is
`multi_correlation_of_uniform_rung`'s `hrungU`.

## Addendum — lap 51: `nondegenerateForms_of_tuple` + `rung_multi_of_named_inputs`

`C3MrtMultiRung.lean` (sorry-free, trust triple).

* `nondegenerateForms_of_tuple` — the `K` forms `(L/d_i)X + (a+i+1)/d_i` of ANY positive tuple
  with an admissible base point satisfy `NondegenerateForms`, via lap 39's `multi_forms_det`
  (`det = L(j−i)/(d_i d_j) ≠ 0`).  No coprimality, no side condition.
* `rung_multi_of_named_inputs` — the `K`-point `rung_two_of_named_inputs`: `KPointLogElliott K`
  + `TwistedPrimeSumSavingAllLevels` + `nonPretentious_zOm` give, for each `A ≥ A₀`, an `i₀`
  with the window bound `(1 + log A^{i₀}) + m·ε·log A` for all `m ≥ i₀`.

**Only `rung_multi_uniform` is left**: one `A` and one `I` for the finitely many admissible
`(d, a)` with `d_i ≤ Y`, `a < Y^K` — `exists_common_threshold` over
`Fintype.piFinset (range (Y+1)) ×ˢ range (Y^K + 1)`, exactly as lap 32 did over triples.  Feed
it `rung_multi_of_named_inputs` at `nondegenerateForms_of_tuple`, and
`multi_correlation_of_uniform_rung` then closes the `D ≥ 3` rung on `KPointLogElliott K` alone.
