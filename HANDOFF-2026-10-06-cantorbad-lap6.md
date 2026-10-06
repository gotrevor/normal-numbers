# HANDOFF 2026-10-06 cantorbad lap 6 (branch proof/cantor-bad-normal)

Target unchanged: `exists_mem_cantorSet_bad_isNormal_coprime_three`.  The operator resolution (resLaw, uniform
resampling) was already in place (b17cc398).  This lap changed the route on top of it.

## Done
- Review finding: `midStages` needs a Cassels rate; stage-by-stage bounds hit Cantor factors at middle/leading
  ternary digits of `bⁿ`, so a rate needs Baker-type equidistribution of `n log₃ b` even granting decorrelation.
  `midStages` stays in the file, off-path (docstring says why).
- Local route (32682ed0): `stageOf`, `condChar`, `contChar`, `localBias`, node `LocalDeadBias`, crux
  `localDeadBias_resLaw` (sorry), leaves `ae_cesaro_condDiff`, `cesaro_contChar_small` (sorry, standard),
  proved wiring `ae_isNormal_resLaw_of_localDeadBias`, `isNormal_of_weylMeans`, `exists_of_law_ae`; headline
  rewired.  BarrierAudit: crux linked, two leaves waived.
- Probe `scripts/cantorbad_localbias.py`: no coherent dead bias for resLaw; dyadic control 0.96 (numbers in the
  `LocalDeadBias` docstring).

## Next
1. Prove `ae_cesaro_condDiff` (plan in PENDING_WORK, cantorbad lap 6).
2. Prove `cesaro_contChar_small`.
3. Crux: second split of `localBias` at a coarser prefix; state the obstacle-phase equidistribution node.

## State at wind-down
Branch `proof/cantor-bad-normal`, HEAD after this commit (code at 32682ed0, docs 05cfc5bf).  No uncommitted edits.
Build green.  Headline `#print axioms`: trust base + `sorryAx` + `J_lt`/`J_inj` native_decide artifacts.
Open sorries in CantorBadNormal.lean: on-path `localDeadBias_resLaw` (crux), `ae_cesaro_condDiff`,
`cesaro_contChar_small`; off-path `midStages`, `fourierPairRate_descent_of_deadRateDecay`.
