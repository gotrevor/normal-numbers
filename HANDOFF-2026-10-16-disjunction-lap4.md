# Disjunction Lean lap 4 (2026-10-16): Rauzy stretch landed

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Concrete advance

- Added the cited proposition `NormalNumbers.Literature.BergelsonDownarowicz.Rauzy1976`: adding
  a deterministic real to a normal real preserves normality.
- Proved `NormalNumbers.Literature.BergelsonDownarowicz.rauzy_disjunction_universal`: for every
  real `y`, either `c + y` is normal or `y` is not deterministic.  The proof is the decisive case
  split on determinism and uses no cited axiom unless a caller supplies the cited proposition.
- Added the exact ratified Maze row "Rauzy disjunction as information about pi" at tier `.kernel`,
  its alias `hall_rauzy_disjunction_universal`, and its `MazeAudit` link.  The audit now reports
  189 rows, 82 linked rows, and 107 legacy rows.
- Assessed stretch item 1 before skipping it under the kickoff's "skip any that balloons" rule:
  `stonehamAlpha 4 3` has no existing reduction to `stoneham23`.  The specialized proof in
  `Stoneham.lean` uses the full multiplication-by-2 orbit modulo `3^M`; replacing it by 4 changes
  the orbit to an index-two subgroup, so this needs a real generalization of the visit-count
  argument rather than a base-change corollary.

The binding kickoff done condition was already met in lap 3 and remains met.

## Exact verification

```text
lake env lean src/NormalNumbers/DeterministicBD.lean
```

Succeeded (pre-existing warnings only).

```text
lake build NormalNumbers.DeterministicBD NormalNumbers.MazeAudit
```

Succeeded: `Build completed successfully (10460 jobs)`; the updated Maze audit compiled.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.DeterministicBD \
  --axioms NormalNumbers.Literature.BergelsonDownarowicz.rauzy_disjunction_universal
```

Verdict: `FORMALIZE-TIER GREEN`; axioms exactly
`[Classical.choice, Quot.sound, propext]`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --import NormalNumbers.DeterministicBD \
  --axioms NormalNumbers.Literature.BergelsonDownarowicz.rauzy_disjunction_universal
```

Verdict: `FORMALIZE-TIER GREEN`; the full build completed successfully (10,852 jobs), and the
theorem's axioms were exactly `[Classical.choice, Quot.sound, propext]`.

## Current blocker / next highest-value attack

There is no blocker on the binding objective.  Remaining work is optional stretch only.  The next
mathematical attack is a base-4 Stoneham visit theorem for `stonehamAlpha 4 3`: replace the
`stonehamState` full-unit-cycle count by a count for the `4`-orbit's index-two residue class and
then descend normality from base 4 to base 2 with `isNormal_of_isNormal_pow`.  If that is not
resumed, the cheaper remaining documentation stretch is to formalize report rows R1--R6, beginning
with R3 and R5 linked to `not_isSimplyNormal_stoneham_sum`.

## Completion marker

`box done "disjunction kickoff complete; Rauzy universal-disjunction stretch is kernel-checked
and full gate green"` was invoked successfully.  Its generic repository-wide self-stop gate warned
that 105 unrelated source sorries remain and may relaunch the box.  This is a bounded kickoff: its
declared done condition is met, so a relaunch should use the kickoff-scoped done condition rather
than reopening the finished objectives.
