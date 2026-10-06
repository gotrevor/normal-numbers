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

## Crux now (rerouted late in lap 9)
- Single crux `aliveOffMix_resLaw` (node `AliveOffMix`): resLaw path-weighted off-diagonal pair sum of
  `deadCorr` over distinct completions of the coarse prefix.  Route: `deadMix_le_aliveMix`
  (`condMean_aliveExt`), `aliveExt_eq_sum` (pathW), `norm_aliveExt_sq_le` (diag ≤ 2048²/536^k via
  `pathW_le`, `sum_pathW`), `aliveObstacleMix_of_off` (diag by `geomNear_le`, c = 16),
  `nearObstaclePhaseMixing_of_alive`.  BarrierAudit link points here.
- The split route (first-order `ResLawObstOff` + `DefectObstacleMix`) is retired as a crux; its proved
  reductions stay.  Defect analysis in the `DefectObstacleMix` docstring.
- Probe t = 12: no base-3 coherence at the first-order level; base-3 barrier binds the Cantor main term.
- Other file sorries (`fourierPairRate_descent_of_deadRateDecay`, `midStages`) are off-path / forbidden
  drift per the branch directive.

## Next
1. Decompose `AliveOffMix` by divergence depth: pairs of completions agreeing for j blocks then
   splitting at an alive node u; the pair sum becomes Σ_j Σ_u pathW(u)² |A(u)|⁻² Σ_{f≠f'} X(uf) conj X(uf'),
   X = aliveExt D (k−j−1).  State the per-depth node; exact (non-Monte-Carlo) probe at k = 1, 2.
