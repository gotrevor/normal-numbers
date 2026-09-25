# HANDOFF c3-mrt 2026-09-25 — lap 38: the tuple mass

**Branch** `wip/c3-mrt`.  Both green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtTupleMass` (new chain tip).
Prior batons: `-lap37.md` (coprimality obstruction resolved), `-lap36.md` (`K`-fold expansion),
`-lap35.md` (the Tao–Teräväinen discovery).

## Advance

The inequality the whole `K`-shift assembly rests on — the `K`-fold `pair_mass_le` — is proved.
New module `src/NormalNumbers/C3MrtTupleMass.lean`, sorry-free, trust-triple:

| name | content |
|---|---|
| **`tuple_mass_le`** | `∑_{(d_i) ≤ Y} ∏_i ‖sqfW z_i (d_i)‖/d_i ≤ ∏_i sqfWMass z_i`, uniformly in `Y`.  With the product weight the tuple sum **factors completely** (`Finset.sum_prod_piFinset`), so this is one line of real content plus `Finset.prod_le_prod` |
| `finsetLcm_pos` | positivity of the joint modulus |
| **`prod_div_lcm_le`** | `(∏_{i<K} w_i)/lcm(d_i) ≤ K^{K²} · ∏_{i<K}(w_i/d_i)` for nonnegative `w` and any jointly-solvable positive tuple — the pointwise `1/lcm → 1/∏ d_i` exchange, with lap 37's constant |

Composing the two: over any set of positive, jointly-solvable tuples with `d_i ≤ Y`,

    ∑ (∏_i ‖sqfW z_i (d_i)‖) / lcm(d_i)  ≤  K^{K²} · ∏_i sqfWMass z_i ,

uniformly in `Y` — which is exactly what licenses truncating each modulus at `Y` in the `K`-fold
expansion, and is the `K ≥ 3` replacement for `pair_mass_le`.

## Indexing debt (flagged, not paid)

`tuple_mass_le` is over `Fin K` (forced by `Fintype.piFinset`, which is how lap 36's
`sum_pow_omega_multi_eq` indexes its tuple sum).  `prod_div_lcm_le` is over `range K` with
`ℕ → ℕ` tuples (forced by lap 37's `prod_le_lcm_mul_pow`).  The lap that composes them must fix
one convention: `Fin.prod_univ_eq_prod_range` bridges the products, and the `lcm` should be
`Finset.lcm (range K)` of the `ℕ → ℕ` extension of the `Fin K` tuple.  This is deliberate — the
conversion belongs in the lap that needs the CRT indexing, not before.

## Assembly scoreboard (depth-`K` rung, mirroring laps 23–33 at `K = 2`)

| step | `K = 2` | general `K` |
|---|---|---|
| bridge expansion | `sum_pow_omega_two_shift_eq_coprime` | ✅ `sum_pow_omega_multi_eq` (lap 36) |
| joint modulus / gain | automatic coprimality | ✅ `prod_le_lcm_mul_pow` (lap 37) |
| tuple mass finite | `pair_mass_le` | ✅ `tuple_mass_le` + `prod_div_lcm_le` (lap 38) |
| truncate moduli at `Y` | `two_shift_truncation_bound` | TODO |
| `K`-fold CRT to an initial segment | `inner_sum_linear_forms` + `filter_linear_lt_eq_range` | TODO |
| per-tuple rung bound | `progression_sum_bound` / `inner_pair_bound` | TODO |
| ε-chase | `rung_two_correlation` | TODO |
| named input | `KPointLogElliott 2` (= dependency) + VK | `ProductLogElliott K` (= Tao–Teräväinen) + VK |

## NEXT

1. **`K`-fold CRT**: the joint progression `{n : ∀ i, d_i ∣ n+i+1}`, when nonempty, is a single
   class mod `L = lcm(d_i)`.  Generalise `exists_joint_class`.  This needs only that the solution
   set is closed under `+L` and `−L` and contains at most one residue mod `L` — no `prod_le_lcm`.
   Then `filter_linear_lt_eq_range` applies verbatim with `L` in place of `de`.
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times; the error
   telescopes to `≤ ∑_{i<K} (∏_{j<i} sqfWMass z_j) · (1 + log(N+K)) · bridgeTail z_i Y`.
3. Then the per-tuple rung bound: `ProductLogElliott K` instantiated at the `K` linear forms
   `(L/d_i)·k + (a+i+1)/d_i`, whose pairwise nondegeneracy is the `K`-fold
   `linear_forms_nondegenerate` — note the determinant is no longer `1` but
   `(L/d_i)(a+j+1)/d_j − (L/d_j)(a+i+1)/d_i`, and nonvanishing needs `i ≠ j`; check this early,
   it is the next place a `K = 2` accident could be hiding.
4. Finally the ε-chase, and the `C(D)` widening of `QuantDepthElliott` recorded in lap 37.

## Still refuted — DO NOT RETRY

Unchanged, plus: the prime-valuation route to `prod_le_lcm_mul_pow` (lap 37 is exact and
factorisation-free); quantifying `F` outside the `K`-induction (lap 36).

## Confidence

* `K ≥ 3` assembly completable: ≈ 75% (unchanged; lap 38 was the step lap 37 predicted, and it
  landed first try).
* Next risk concentrates in item 3 above (nondegeneracy of the `K` linear forms).
* leaf TRUE ≈ 97%; leaf PROVABLE with known techniques ≈ 27%.
