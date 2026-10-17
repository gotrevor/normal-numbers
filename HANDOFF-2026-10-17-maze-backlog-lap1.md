# Maze backlog lap 1 — closed joint-orbit routes (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  This lap completed Part 1's four
prose-only routes.  Parts 2 and 3 remain and are the next binding work; the kickoff's terminal
condition has therefore not yet been reached.

## Concrete advance

- Persisted the source report as `docs/joint-bc-orbits-2026-10-16.md`.
- Added `NormalNumbers.BBPSpan`, with a sorry-free polynomial-ratio model of a BBP-type series,
  closure under rational scaling and addition, and the proved headline
  `MasterConjectures.isBBPTypeSeries_nonzero_rat_linear`.  This is the kernel witness for R1;
  `NormalBBPSeed` records the precise reopen condition.
- Added `NormalNumbers.JointOrbitBarriers`.  It records R2 as the exact frozen universal
  lower-density statement `StonehamUniversalDisagreement`, and R4 as the exact frozen
  `{0,1}`-Cantor-pair statement `CantorPairNoDisjunctiveChannel`, linked to the existing
  exponent-two node `QSpan.exists_pair_exponentTwo_qSpan_not_normal`.
- In the same module, proved the R6 projection theorem
  `JointOrbitBarriers.isNormal_coordinates_of_jointNormal`: joint normality of the encoded
  digit pair implies normality of both coordinates.  `LnTwoNormalSeed` records its reopen
  condition.
- Added all four Maze rows at honest tiers (`R1 .restatement/.kernel`,
  `R2 .vacuous/.frozen`, `R4 .refuted/.frozen`, `R6 .wall/.kernel`), declaration links, and
  root imports.  `#maze_audit` now reports 195 rows, 88 declaration-backed links, and 107
  legacy prose rows.

No new `sorry` was introduced.  The two proved headline theorems depend only on Lean's standard
trust baseline: `propext`, `Classical.choice`, and `Quot.sound`.

## Verification

Final gate (green):

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --axioms NormalNumbers.MasterConjectures.isBBPTypeSeries_nonzero_rat_linear \
  --axioms NormalNumbers.JointOrbitBarriers.isNormal_coordinates_of_jointNormal \
  --import NormalNumbers.Maze
```

Verdict: `FORMALIZE-TIER GREEN`; `NormalNumbers.MazeAudit` completed at 10464 jobs, and both
axiom reports were exactly `[Classical.choice, Quot.sound, propext]`.

Concurrent Lake fan-outs repeatedly encountered the shared box's OS-level `Too many open files`
condition near their final jobs.  The affected leaves were built serially, after which the
unchanged gate above completed successfully.  The repository's enforced pre-commit build then
also completed successfully with `taskset -c 0-5`: 10856 jobs.  The transient failures were
resource exhaustion, not Lean source errors.

## Current crux and next attack

Part 2 is next.  Introduce the frozen node `IsDensityProductBlock` and prove
`not_forall_isDensityProductBlock` using `Mahler.bgLiouville 3 0 1`, following the witness and
digit-zero mechanism already used by `exists_counterexample_on_line`.  The load-bearing point is
to turn the Liouville-sparse ternary expansion into a zero lower density for at least one digit of
every multiplier in the finite set `S`, while keeping the theorem universal in `S`.  Then add the
`.wall` Maze row and `MazeAudit` declaration link before moving to Part 3's two Stoneham boundary
theorems.
