# HANDOFF 2026-10-07: repetition lap 7 (review lap; branch proof/cantor-repetition)

Supersedes repetition-lap6 and its STUCK claim: the operator directive (prove the frozen
`liouvilleCantorFullProfile`) is answered by a new route that avoids the open walls.

## Route change (DIRECTION.md CURRENT DIRECTIVE, lap 7)
The assembly needs only a copy-zone saving summable along `sched`.  Sparse orbit points pair up:
`SparseIdentity.cyclic_pair_identity` (PROVED, trust base) turns `y, tᵟy` both cyclically sparse mod
`3^A − 1` into an exact identity `tᵟU = V`; Matveev bounds `δ`; sparse points cluster.

## Built this lap
- New file `src/NormalNumbers/SparseIdentity.lean`: `IsSparse3`, `CycSparse`,
  `Literature.MatveevThreeLogs` (cited Prop), `SparseIdentityBound`, guards
  `not_sparseIdentityBound_nine`, `not_sparseIdentityBound_one`, degenerate case
  `pow_le_two_of_sparse_one` (all proved), `cyclic_pair_identity` (proved),
  `sparseIdentityBound_of_matveev` (sorry, 90%).
- `CantorRepetition.lean` section "The copy zone through sparse pairs": `cycSparse_of_cycProd_ge`,
  `card_cluster_le`, `RunOrbitDecay`, `runOrbitDecay_of_sparse`, `card_degRows_le`, `copyRun_psi`,
  `repPairArith_of_runDecay` (sorry leaves with English proofs), `repPairArith_of_literature`
  (proved from them), cited `Literature.bakerLogDiscrepancy_cited`, `Literature.matveevThreeLogs_cited`.
  `repPairArith_of_three_dvd` rewired (no direct sorry).  `liouvilleCantorFullProfile_of_literature`.
- BarrierAudit updated (crux link for `sparseIdentityBound_of_matveev` with barrier
  `cantor_not_normal_three_pow`; waivers for the leaves).  Root import updated.  Full build green.

## Next (in order)
1. `sparseIdentityBound_of_matveev` — state the gap-step lemma first (docstring plan).
2. `cycSparse_of_cycProd_ge`, `card_cluster_le`, `runOrbitDecay_of_sparse`.
3. `card_degRows_le`, `copyRun_psi`.  4. `repPairArith_of_runDecay`.

## Checkpoint
Branch `proof/cantor-repetition`, route commit `72ac4834`; tree clean apart from this note.
Full default build green (10797 jobs).  `#print axioms`: `cyclic_pair_identity`,
`pow_le_two_of_sparse_one`, `not_sparseIdentityBound_nine` = trust base; both headlines show sorryAx
only through the leaves listed in DIRECTION.md CURRENT DIRECTIVE.  No new proof work in flight.
