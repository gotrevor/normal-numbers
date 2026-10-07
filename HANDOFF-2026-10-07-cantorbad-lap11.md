# HANDOFF cantorbad lap 11 (2026-10-07)

Branch `proof/cantor-bad-normal`.  Build green.  The headline is unchanged.

## Done (run directive, 2026-10-06 evening)
1. Moved the off-path nodes `midStages` and `fourierPairRate_descent_of_deadRateDecay` verbatim to
   `CantorBadNormalRetired.lean`.  Their dependants and exclusive helpers went with them:
   `hybridCassels`, `deadCharSigned(_core)`, `casselsRate_resLaw`, `stage_telescope`, ….
   `CantorBadNormal.lean` now has exactly one `sorry`, the crux `aliveOffMix_resLaw`.
2. Probe `scripts/cantorbad_numdisp.py`.  Bases 2, 5, 7 separate from the controls (b = 3 and
   dyadic, both exactly 1) by a constant factor (~.09), but nothing decays in L:
   - the full-residue numerator collision ratio is .157 at L = 12 and .144 at L = 14;
   - the mean over a = b^m is .09 at L = 12 and .08 at L = 14.
   So numerator averaging gives a constant saving, not a summable rate.
3. Route recorded as closed:
   - node `PreperiodicNumeratorDispersion` (believed false, 10%) and `numCollPairs`;
   - Maze row "numerator averaging for the preperiodic obstacle families" (linked in MazeAudit);
   - BarrierAudit string for `aliveOffMix_resLaw` updated.

## Caveats
- L = 16 did not finish in this lap.  Groups at L ≤ 14 are all shallow (3^j ≲ N|G|).
- The crux is unchanged.  Its preperiodic part now rests on `ThreeAdicWindowAvg` at middle depth
  (digits of powers, open).
