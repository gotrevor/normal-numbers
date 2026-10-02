# HANDOFF — Erdős #257 all-primes lane, lap 1 (2026-10-02)

Branch `proof/257-allprimes`, HEAD `e34ed96c`; no uncommitted edits. Stop signalled via `box done --green`.

**Scope met.** `#print axioms NormalNumbers.Erdos257.erdos257_allPrimes_of_cases`
= `[propext, Classical.choice, Quot.sound]`.  Conditional on the two cited Props
(`Literature.Erdos1968CoprimeSummable`, `CastingOut.TTEquidistributedDyadic`).

## What landed
- Case (i): `isDisjunctive_subsetLambert_two_of_weakRate` (G4Base2WeakSched, `moment_cap_weak`).
- Obstruction: `G4.SchedB.hypE_frame_excludes_logRate` — HypE frame caps e ≤ 2^{8K²} via BOTH
  the moment order (term_b/c) and the far tail (farC ≈ log log X vs 2^N). Maze row (now "reopened
  and realized").
- Decoupling (the crux):
  - `G4FarTailS`: `sum_omegaS_add_le`, `farCS`, `farAvgS_leS` — far tail sees only F_S.
  - `G4SchedBE2`: `HypE2 b K e s`, moment order 10⁵·T·s with Σ_sm 1/p ≤ 3s+5.
  - `G4SubsetWitnessCovS`: `ScheduleWitnessSCS` (hfar via farCS) + headline.
  - `G4Base2DecSched`: `scheduleWitnessSCS2`, `hfar_of_C`, `hfar_twoS`.
  - `G4Base2DecAssembly`: `towerF_succ_le` (+7 per tower step), `exists_first_crossing`,
    `exists_scheduleWitnessSCS_two_of_divergent`.
  - `Erdos257Divergent.isDisjunctive_subsetLambert_two_of_divergent`: every divergent prime set.
- `isDisjunctive_subsetLambert_two_of_gapSet` proved from it.

## Still open (out of this run's done-criterion)
- `towerGapPrimes_gapSet`, `squareBlockPrimes_weakRate`, `squareBlockPrimes_not_mertensRate`
  (example lemmas, need per-block two-sided Mertens).
- `erdos257_allPrimes` (unconditional) needs both citations discharged.
- Note: case (i) is now subsumed by the divergent theorem; the case split could collapse to
  convergent/divergent.
- Faithfulness risk unchanged: everything rests on `TTEquidistributedDyadic` (85%, see
  Erdos257Base2 docstring); an expert check of that transcription is the top item.
