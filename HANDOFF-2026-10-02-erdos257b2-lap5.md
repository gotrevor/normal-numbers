# HANDOFF — Erdős #257 base 2, lap 5 (2026-10-02) — DONE

Branch `proof/erdos257-base2`.  `#print axioms` for `isDisjunctive_subsetLambert_two`,
`erdos257_primeSubset`, `erdos257_residueClass`: `[propext, Classical.choice, Quot.sound]`
(conditional on the hypothesis argument `CastingOut.TTEquidistributedDyadic`).

## This lap (all five leaves closed)
- N3 `exists_bins`: greedy, invariant "≤ one bin of mass < θ".
- `abs_one_sub_binDelta_le`: original REFUTED (`not_abs_one_sub_binDelta_le`, N = 0); repaired
  with `1 ≤ 2N`; `abs_binDelta_le` covers all N.
- `sum_inv_vlPrimes_le`: `G4Base2Mertens` (explicit Mertens on log-blocks), Y₀ = ⌈e^13860⌉.
- N5 `binInd_ap_mean`: `G4Base2N5` + `G4Base2Rough` (inclusion–exclusion, CRT count,
  rough count via Chebyshev θ), C₅ = 10⁶.
- N4 `avg_binErr_le`: original REFUTED (`not_avg_binErr_le_rho_zero`, n+ρ = 0); repaired with
  `0 < ρ` (callers: `shiftAL_pos`); proved via `G4Base2Pairs` (pair counts, Σ1/(p log p) ≪ 1/log Y),
  C₆ = 250.
- No Maze row: both refutations were missing side-hypotheses on internal leaves, repaired in place;
  the refuting theorems sit next to the repaired leaves.
