# HANDOFF 2026-10-08: repetition lap 9 (branch proof/cantor-repetition)

Supersedes repetition-lap8.

## Proved this lap
- `repPairArith_of_runDecay` (last route leaf), via `repPairPos_copy`, `summable_copy_sched`
  (sched sum swap), `run_tail_weight`, `runStart_le_pow`, `log_runStart_le`.
- Consequence: `liouvilleCantorFullProfile_of_literature (hB) (hM)` has `#print axioms` =
  [propext, Classical.choice, Quot.sound].  The sparse-pair route of DIRECTION.md is complete.

## Open
- `repPairArith_of_three_dvd`: designated waived direct sorry; the unconditional form needs proofs of
  the cited Baker/Matveev results themselves (multi-year wall; DIRECTION lists it last).
- Other sorries in src/ (88 sorry lines repo-wide) belong to other nodes, outside this branch's directive.

## Checkpoint
Build green.  Scratch: scratch/RD.lean (development copy), scratch/AxRD.lean (axiom check).
