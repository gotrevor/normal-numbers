# Disjunction Lean lap 5 (2026-10-16): Stoneham Maze routes R3/R5 promoted

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Concrete advance

- Proved `NormalNumbers.not_isNormal_stoneham_sum`, the direct normality-level consequence of the
  already-proved zero-window/simple-normality obstruction for
  `stonehamAlpha 2 3 + stonehamAlpha 4 3`.
- Promoted the joint-orbit report's closed routes R3 and R5 into `Maze.lean` as the kernel-tier
  rows "Stoneham decomposition of ln 2 into normal summands" and "normal Stoneham constants are
  closed under addition".  Each has a named Hall alias and a `MazeAudit` declaration link.
- The Maze audit advances from 189 rows / 82 linked rows to 191 rows / 84 linked rows, with the
  legacy count unchanged at 107.
- Did not add prose-only versions of R1, R2, R4, or R6.  Their report mechanisms do not yet have
  faithful Lean statements: R1 needs a BBP-span closure/entropy formulation, R2 needs the universal
  Stoneham relative-dimension theorem T-D, R4 needs the Cantor-channel dimension/exponent witness,
  and R6 needs a formal joint-normality notion and its projection theorem.

The binding kickoff done condition was already met in lap 3 and remains met.

## Exact verification

```text
lake env lean src/NormalNumbers/StonehamSums.lean
```

Succeeded (pre-existing linter warnings only).

```text
lake build NormalNumbers.Maze NormalNumbers.MazeAudit
```

Succeeded: `Build completed successfully (10461 jobs)`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSums \
  --axioms NormalNumbers.not_isNormal_stoneham_sum
```

Verdict: `FORMALIZE-TIER GREEN`; axioms exactly
`[Classical.choice, Quot.sound, propext]`.

## Current blocker / next highest-value attack

There is no blocker on the binding objective.  Remaining work is optional stretch.  The next
highest-value mathematical attack remains `isNormal_two_stonehamAlpha_four_three`: generalize the
base-2 Stoneham visit count to the base-4 orbit's index-two residue class, first proving
`IsNormal 4 (stonehamAlpha 4 3)`, then descend with `isNormal_of_isNormal_pow`.  This would make the
R5 counterexample fully self-contained as a pair of separately binary-normal summands.  If that
balloons, formalize R2/T-D's universal relative-dimension theorem before adding its Maze row.

## Completion marker

The kickoff-scoped done condition remains satisfied; invoke `box done` after committing this green
stretch checkpoint.
