# HANDOFF 2026-10-07: repetition lap 5 (branch proof/cantor-repetition)

Supersedes repetition-lap4.  DIRECTION.md CURRENT DIRECTIVE unchanged: prove `repPairArith_of_inputs`.

## Done this lap (all in CantorRepetition.lean, section "Per-class Riesz bounds")
- `bf_le_hf_true_add` (+ `hf_true_lip`, `sum_two_div_three_pow`): classes 1/3 pointwise bound.
- `repBound_some_le_cyc`: classes 5/6 pointwise bound.
- Analytic hypotheses for `pair_classify_rep`: `le_log_mul_pow` (v ≤ y), `log_mul_pow_lt` (y < ρv),
  `three_pow_le_pow_sub_pow`/`le_log_pair` (u ≤ T), `log_pair_le_log` (T ≤ top of H bⁿ), `hsep_of`.
- Still 3 sorries (unchanged set).

## Next
Item 3 of lap-4 handoff: per-class sums.  Define κ (argmin), bound each class via
`sum_hf_true_le`, `sum_topProd_le`, `copyRun_sum_le`; band / small-m counts O(NK); pick
W, K ≍ ε log N; summability via `summable_sched_rpow`.  Note: positions use v₃ h offsets; the
lemmas above take `H = |h|` naturals — glue Int→Nat via `Int.natAbs`.
