# HANDOFF cantorbad lap 9 (2026-10-06)

Branch `proof/cantor-bad-normal`.  Headline unchanged; build green.

## Done (all proved, in CantorBadNormal.lean)
- `deadCorr_eq_cylChar`: D = |A|⁻¹ Σ_dead (χ(vf) − χ(v)), χ = `cylChar`.
- `firstMix_le_obstMix` (exact 1/|A| weights; no 1/1024 error), `firstOrderObstacleMix_of_cyl`.
- C–S chain: `sq_integral_norm_comp_buildU_le`, `obstMix_sq_le`, `norm_obstSum_sq`,
  `secondMoment_obstSum_eq`, `norm_obstSum_sq_split` (diag + `obstOff`), `norm_obstSum_sq_le`,
  `sqrt_secondMoment_le`, `resLawObstSecondMoment_of_off`, `cylObstacleCancellation_of_secondMoment`.
- Diagonal leaf `diagSmall_of_two_le` (via `stageOf_gap`).
- `cExt_sub`, `cExt_aliveDefect`.

## Crux now
- First-order: `resLawObstOff_resLaw` (node `ResLawObstOff`: resLaw-averaged same-cylinder obstacle
  pair sums).  BarrierAudit link points here.
- Defect: `defectObstacleMix_resLaw` (docstring: norm-inside bound provably insufficient in shape;
  needs the same cylinder cancellation recursively).
- `PairCorrToCylinder`: open; change of measure μ_K→resLaw expected to cost e^{c s_n} (docstring
  of `ResLawObstSecondMoment`), so `ObstaclePairCorrelation` is the wrong (μ_K, global) form.

## Next
1. Probe `obstOff` at larger lags with b=3 control (Monte Carlo probe at lags 1–3 was at floor).
2. State one uniform cylinder-cancellation node covering the family generated from `deadCorr` by
   `aliveDefect`/`cExt`, and derive both `ResLawObstOff` and `DefectObstacleMix` from it.
