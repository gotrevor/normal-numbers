# HANDOFF 2026-10-06 profile lap 2

Branch `proof/cantorexp-profile`. Kickoff: `KICKOFF-2026-10-06-profile.md`. Scope:
`src/NormalNumbers/CantorExactExponentProfile.lean`.

## Done this lap (all proved)
- `secondMoment_le_profile` (Baker-conditional crux) ⇒ `ae_isNormal_of_profileOK_of_baker` is
  sorry-free given `Literature.BakerLogDiscrepancy`.
- Kickoff step 3 (wiring): the family derandomizer needs a PRIMREC per-base constant and ONE weight
  `W`; `∃`-constants can't be extracted, and `pcB` (small-`m` constant) grows like `a_{k}` with
  `k ≍ log|h|` (super-polynomial in `|h|`).  Fix: effective hypothesis
  `Literature.BakerLogDiscrepancyEff` (one `K`, constant `t^K`, saving `1/(K t)`; implies the old one,
  `bakerLogDiscrepancy_of_eff`) + polylog weight `profW N = (log₂N+1)^{-16}`.
  Proved: `exists_computable_normal_avoid_profile`, `exists_computable_normalProfile_of_baker`
  (= the frozen headline's statement under `BakerLogDiscrepancyEff`), `profile_ev`,
  `primrecPred_profileOK` (`stepV`, `profileOK_iff`), `secondMoment_profile_uniform`
  (explicit constants: `pair_classify_expl`, `pair_bound_expl`, `sum_topProd_le_of`,
  `secondMoment_profile_core`, `margin_ge`, `pcA_le`, `pcB_le`, `small_case`, `profKappa`).

## Open in scope (2 sorries), both = the Baker wall
- `ae_isNormal_of_profileOK` needs `Literature.BakerLogDiscrepancy` proved.
- headline needs `Literature.BakerLogDiscrepancyEff` proved.
Analysis (this lap): an elementary rate (from `t^k ≠ 3^j` only) gives top-window saving
`(log N)^{-log₃(3/2)}`; summing over the run shadows (`log a_k ≍ k log k`) needs exponent > 1, so
the elementary rate is insufficient even with the Davenport–Erdős–LeVeque criterion.  A
sub-exponential lower bound `|k log t − j log 3| ≥ exp(−k^{0.4})` would suffice (Gelfond 1935
territory).  Next attack: decide between formalizing a Gelfond-type two-log bound (mathlib has
Siegel's lemma) vs. freezing this obstruction as a Maze row.
Gotchas: `positivity`/`ring` on goals containing big `set` nats or `Nat.factorial 32` time out at
whnf — use `clear_value`, `generalize`, explicit `mul_nonneg`; never `ring` a `(x+1)^32`.
Iterate in `scratch/ProfUni.lean` (`lake env lean`, ~1 min) instead of `lake build` (~10 min).
