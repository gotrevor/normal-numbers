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

## Open
- On-path crux: `nearObstaclePhaseMixing_resLaw` (node `NearObstaclePhaseMixing`, 50%).
- New conjecture node (not wired): `ObstaclePairCorrelation` (45%), twisted pair correlation of the
  obstacle rationals near K; evidence L=12 square-root cancellation for b=2,5,7, b=3 coherent (.16).
- Off-path: `midStages`, `fourierPairRate_descent_of_deadRateDecay`.

## Next
1. (done) L=16 paircorr recorded in the node docstring: same separation.
2. Implication `ObstaclePairCorrelation → NearObstaclePhaseMixing`: needs (a) 1/|A| vs 1/1024 error,
   (b) the second-order defect terms of `condMean_cExt_telescope`, (c) μ_K weights of obstacles in a cylinder.
   State (b) as its own node; decide by numerics whether it is genuinely lower order.
