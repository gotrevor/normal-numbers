# HANDOFF 2026-10-06 profile lap 1

Branch `proof/cantorexp-profile`, HEAD e476d9f0. Kickoff: `KICKOFF-2026-10-06-profile.md`
(supersedes DIRECTION.md's stretch directive, per operator). Scope: `src/NormalNumbers/CantorExactExponentProfile.lean`.

## Done (all proved, green)
- Step 1: `not_isNormal_of_not_profileOK` (+ `fract_lt_of_run_block`, `ne_rpow_of_not_dvd`).
- Crux finding: the elementary orbit port fails in run shadows (`shadow_card_ge`, `window_covered_imp`;
  Maze row "elementary orbit port to 3 | b", wall; reopen `LogDiscrepancy`).
- Conditional route: `ae_isNormal_of_profileOK_of_baker` PROVED from one leaf `secondMoment_le_profile`
  (sorry) via `summable_sched_rpow`. Hypothesis `Literature.BakerLogDiscrepancy` (Baker + Erdős–Turán).
- Leaves for that leaf, all proved: `bf_le_topProd`, `bf_le_topProd_of_dvd` (top digits of the lower
  term seen through the pair difference), `bf_mono`, `hf_true_eq`, `bf_le_hf_true`, `sum_hf_true_le`,
  `cantorProd_lip`, `sum_cantorProd_grid`, `cell_bounds`, `sum_topProd_le`, `pair_classify`,
  `profile_data`, `hf_neg`, `pair_bound`.

## Next (in order)
1. Prove `secondMoment_le_profile`: `CantorLiouvilleAll.secondMoment_expand_b` with M as in
   `pair_bound` (M depends on N, W — fine, expand holds for every M), `CantorLiouville.pair_sum_le`
   with G d m := Bf (expFree μ₀) M (h(bᵈ−1)bᵐ); apply `pair_bound`; Σ_m low term by
   `sum_hf_true_le` (W = j+1; c = h'(bᵈ−1), 3∤c since bᵈ−1 ≡ −1 mod 3 and 3∤h'); top terms by
   `sum_topProd_le` (β = log₃(|h|(bᵈ−1)), resp. log₃|h|); small-m term ≤ A·W+B. Choose
   W = ⌊ε log₃ N⌋ with ε = κ/4 so 9^W ≤ N^{κ/2}; result C N^{2−δ}. Watch: pair_bound's M has W.
2. Then the scoped file still needs unconditional `ae_isNormal_of_profileOK` = proving
   `LogDiscrepancy` (Baker-level; multi-year wall). Headline wiring also needs the derandomizer
   test family extended (kickoff step 3).
Gotchas: long real-arith proofs need `set_option maxHeartbeats N in` (per-declaration);
pre-commit build may hit "Too many open files" — `ulimit -n 65536` then recommit.
