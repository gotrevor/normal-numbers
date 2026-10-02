# HANDOFF — master conjectures, lap 1 (2026-10-02)

Campaign `KICKOFF-2026-10-02-master-conjectures.md`: all three phases landed in one lap.

* Phase 1: `hypA_lnTwo`, `hypA_pi_base16`, `borel_sqrt_two` (frozen statements byte-identical;
  only `sorry` lines removed).
* Phase 2 (≥ 4 required; ~16 proved): `MasterConsequences.lean`, `MasterKicked.lean`
  (`hypA_isNormal_of_kicked`), `MasterPiSq.lean`, `MasterLnTwoBase3.lean`, `EquidistTransfer.lean`
  (`isNormal_of_isNormal_pow`, `equidistributed_of_fract_perturb_abs`).
* Phase 3: `MasterMaze.lean`; Maze audit 34 linked / 107 legacy.

All headline axioms = [propext, Classical.choice, Quot.sound].  STATUS / OVERVIEW / HEADLINES bet 3
rows written.  Next: see PENDING_WORK top section (optional follow-ups).

## Checkpoint (treadmill stop)
Branch `proof/master-conjectures`, HEAD 46c3efcc before this note.  Stop signalled via
`box done --green`.  Exact next steps if reopened: (1) prove `Irrational (π²)` (adapt mathlib's
Cartwright integrals, which are private) to drop the hypothesis from `hypA_piSq_base16/base2`;
(2) more `hypA_isNormal_of_kicked` instances (other BBP-type constants); (3) state obstructions for
the legacy Maze rows listed in `mazeTestImplied` and link them in `MazeAudit.lean`.
