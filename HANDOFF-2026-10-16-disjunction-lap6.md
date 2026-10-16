# Disjunction Lean lap 6 (2026-10-16): the second Stoneham summand is binary normal

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Reflection verdict and concrete advance

The prior handoff identified exact counting in the index-two unit coset of
`4 mod 3^M` as the likely crux for `isNormal_two_stonehamAlpha_four_three`.
That was stronger than the proof actually needs.  The Bailey--Misiurewicz
hot-spot input is one-sided: an upper visit bound with any absolute constant
is enough.  During one period the multiplication-by-four orbit is injective
into the whole residue interval `[0,3^M)`.  Since its period is
`3^(M-1)`, this crude ambient injection loses only the fixed factor three.
It completely avoids classifying or exactly counting the occupied coset.

Formalized that simplification end to end:

- `StonehamArith.lean` now defines `fourUnit` and proves
  `orderOf_fourUnit : orderOf (fourUnit M) = 3^(M-1)`.
- `StonehamSums.lean` now contains the base-four state recursion, unit seed,
  analytic state approximation, ambient-residue segment bound, window bound,
  and hot-spot summation.
- `isNormal_four_stonehamAlpha_four_three` proves
  `IsNormal 4 (stonehamAlpha 4 3)`; the requested stretch theorem
  `isNormal_two_stonehamAlpha_four_three` descends it along `4 = 2^2`.
- `stoneham_pair_normal_not_isSimplyNormal_sum` packages the exact punchline:
  `alpha_{2,3}` and `alpha_{4,3}` are both binary normal, while their sum is
  not even simply normal.
- The R3/R5 Maze aliases and audit links now point to that full semantic
  witness rather than merely to the negative conclusion about the sum.

This also records the reusable reflection lesson: the failed route was
cargo-culting the full-generator proof of `alpha_{2,3}`.  For a strong
one-sided hot-spot criterion, bounded-index orbits need only inject into an
ambient interval; exact orbit equidistribution is unnecessary.

The binding kickoff done condition was already met in lap 3 and remains met.
The kickoff's first optional stretch is now complete; its mandatory Rauzy
row and the faithful R3/R5 rows were completed in laps 4--5.

## Exact verification

```text
lake build NormalNumbers.StonehamArith
```

Succeeded: `Build completed successfully (8706 jobs)`.

```text
lake env lean src/NormalNumbers/StonehamSums.lean
```

Succeeded (FORMALIZE-tier linter warnings only).

```text
lake build NormalNumbers.MazeAudit
```

Succeeded: `Build completed successfully (10461 jobs)`.  An earlier cold,
highly parallel attempt reached 10455/10461 and hit the host file-descriptor
limit (`Too many open files`); the warm rerun completed and exposed no Lean
failure.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSums \
  --axioms NormalNumbers.isNormal_two_stonehamAlpha_four_three \
  --axioms NormalNumbers.stoneham_pair_normal_not_isSimplyNormal_sum
```

Verdict: `FORMALIZE-TIER GREEN`; both declarations have exactly
`[Classical.choice, Quot.sound, propext]`.

## Current blocker / next highest-value attack

There is no blocker on the binding objective or the completed Stoneham
stretch.  The next item in kickoff order is conditional stretch T-C.  Its
condition is satisfied: `MasterKicked.lean` already supplies the generic
`bcOrbit_eq_kicked` / `hypA_isNormal_of_kicked` bridge.

The next highest-value attack is therefore the T-C base-four family theorem:
under `BaileyCrandallHypA`, every nonzero rational combination of `log 2` and
`log 3` is base-4 normal.  Start by packaging the base-four kicked-series
identity

```text
log 3 = 2 * log 2 - sum' n>=1 1 / (n * 4^n)
```

and the grouped base-four series for `log 2`, clear rational coefficients to
one polynomial quotient `p(n)/q(n)`, and feed it to
`hypA_isNormal_of_kicked`.  The likely new crux is the uniform irrationality
lemma for every nonzero rational linear combination of `log 2` and `log 3`;
the repo has multiplicative-independence irrationality of `log 2 / log 3`
but not yet this stronger affine irrationality statement.

## Completion marker

The kickoff-scoped done condition remains satisfied; invoke `box done` after
committing this green stretch checkpoint.
