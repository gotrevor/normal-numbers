# HANDOFF 2026-10-06 cantorbad lap 8 (branch proof/cantor-bad-normal)

Target unchanged: `exists_mem_cantorSet_bad_isNormal_coprime_three`.  Build green.
Operator resolution (2026-10-05 22:55) was already done in lap 4 (`resLaw`, node `FourierPairRateChoose`).

## Proved this lap (CantorBadNormal.lean)
- Stage telescope: `deadCorr`, `setIntegral_eq_of_atoms`, `condMean_contChar_succ`,
  `condMean_contChar_telescope`, `norm_one_sub_muK`, `norm_ee_sub_contChar`,
  `norm_condMean_localBias_add_le`; `deadMix`, `biasMix_le_deadMix`, `localBiasMixing_of_obstaclePhase`.
- Tail cut: `deadMix_le`, `obstaclePhaseMixing_of_near`.
- Generic re-telescope against the uniform continuation: `unifAvg`, `aliveAvg`, `aliveDefect`, `cExt`,
  `condMean_succ_alive`, `condMean_cExt_telescope`.
- `summable_sched_log_rpow` ((log N)^{−δ}, δ>2, is an admissible rate).
- Periodic obstacles: `perNum`, `riesz`, `periodic_phase_sum`, `ee_add_int`, `riesz_three_shift`.

- Bootstrap tools: `norm_aliveDefect_le`, `catB`/`pathW`/`real_buildU_catB` (path likelihood),
  `gMix`/`gMix_le` (generic recursion); crux split `deadMix_le_first_add_defect`,
  `nearObstaclePhaseMixing_of_split`.

- `cExt_unifAvg`, `cExt_eq_sum` (first-order term = explicit uniform average over completions).

## Open
- On-path crux: `firstOrderObstacleMix_resLaw` (50%) + `defectObstacleMix_resLaw` (45%), split proved.
- Nodes (not wired): `AvgDeadDensity` (70%).
- New conjecture node (not wired): `ObstaclePairCorrelation` (45%), twisted pair correlation of the
  obstacle rationals near K; evidence L=12 square-root cancellation for b=2,5,7, b=3 coherent (.16).
- Off-path: `midStages`, `fourierPairRate_descent_of_deadRateDecay`.

## Next
0. HEAD at handoff: see `git log -1`; no uncommitted edits.  Immediate next step: write `cExt (deadCorr ξ) k w`
   via `cExt_eq_sum` as a sum over obstacles (each dead child at stage t ≈ e(hbᵐ p/q)), bounding the errors,
   to connect `FirstOrderObstacleMix` to `ObstaclePairCorrelation`.  Then the weighted `AvgDeadDensity` for
   the bootstrap (`gMix_le`).
1. (done) L=16 paircorr recorded in the node docstring: same separation.
2. Implication `ObstaclePairCorrelation → NearObstaclePhaseMixing`: needs (a) 1/|A| vs 1/1024 error,
   (b) the second-order defect terms of `condMean_cExt_telescope`, (c) μ_K weights of obstacles in a cylinder.
   State (b) as its own node; decide by numerics whether it is genuinely lower order.
