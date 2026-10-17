# Maze backlog reflection lap 7 — L2 pairwise premise reopened (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order and apply the reflection audit to the
claimed terminal state at commit `82adf11a`.  Parts 1, 2, and 3/L1 remain complete.  This lap
reopened Part 3/L2 because its advertised counterexample had only one of its two required
halves.

## Route-decisive reflection finding

The kickoff's L2 statement says that three constants are pairwise jointly normal while their
triple is not.  The former Maze alias `hall_pairwise_joint_normality` pointed only to
`not_isSimplyNormal_three_seven_triple`, which proves that

```text
α₃,₇ − α₉,₇ + α₂₇,₇
```

is not simply normal.  That proves the non-joint conclusion, but it says nothing about the
three pairwise hypotheses.  No declaration in the repository proved that every nonzero
rational combination of each pair is normal.  The prior green builds and axiom reports were
therefore valid proof audits of a weaker theorem, not evidence for the advertised Maze
refutation.  This was a statement-faithfulness failure rather than an axiom or elaboration
failure.

The row `joint normality is pairwise` is now `.parked/.frozen`, and its old misleading alias is
gone.  It must not return to `.refuted/.kernel` until the pairwise premise below is proved.

## Concrete advance

`StonehamSumsBoundary.lean` now makes the logical boundary exact:

- `IsRationallyJointNormal` and `IsPairwiseRationallyJointNormal` state the full rational-linear
  combination obligations;
- `stonehamThreeSevenFamily` names the three coordinates, and the open Prop
  `StonehamThreeSevenPairwiseNormal` names exactly the missing premise;
- `not_isRationallyJointNormal_stonehamThreeSeven` upgrades the existing zero-window theorem to
  the explicit non-joint formulation by selecting the coefficient vector `(1, -1, 1)`;
- `stonehamThreeSeven_pairwise_not_joint` packages the intended counterexample, conditional on
  the honestly exposed pairwise premise;
- `MazeAudit.lean` now audits both the proved links and that open Prop for the frozen row.

The same-prime route also gained a load-bearing arithmetic prerequisite.  For integer
coefficients `(a,c)`, the new resultant identities prove

```text
7^n ∣ a + c·3^(7^n)       ⇒  7^n ∣ a² + ac + c²,
7^n ∣ a + c·(3^(7^n))²  ⇒  7^n ∣ a² − ac + c².
```

Both quadratic norms are nonzero for a nonzero coefficient pair.  Consequently
`stoneham_pair_cancellationDepth_le_one` and
`stoneham_pair_cancellationDepth_le_two` bound leading-phase 7-adic cancellation by the fixed
7-adic valuation of the corresponding norm.  These two cases cover the exponent gaps among
`1, 2, 3`; they are the finite arithmetic input that the unformalized same-prime argument was
missing.

## Verification

The narrow edited module check succeeded:

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

The repository's real scoped gate was then run exactly as follows:

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSumsBoundary \
  --axioms NormalNumbers.not_isRationallyJointNormal_stonehamThreeSeven \
  --axioms NormalNumbers.stoneham_pair_cancellationDepth_le_one \
  --axioms NormalNumbers.stoneham_pair_cancellationDepth_le_two
```

It built 10,470 jobs and ended `FORMALIZE-TIER GREEN`.  Each of the three audited declarations
has exactly `[Classical.choice, Quot.sound, propext]` as its axiom list.  Reported `sorry`s are
pre-existing proof debt outside the edited module and do not affect this checkpoint.

After the final claim-language edit, `lake build NormalNumbers.MazeAudit` again completed all
10,470 jobs successfully.

## Current blocker

The remaining kickoff obligation is `StonehamThreeSevenPairwiseNormal`.  This is hard but
in-scope mathematics, not an operator or external-condition blocker, so neither `box done` nor
`box stuck` is warranted.

The arithmetic lemmas control cancellation between the two newest same-`c` phases.  They do not
yet prove that the reduced denominator of the *full* two-family Stoneham orbit state grows: the
older terms and rational coefficient denominators still have to be threaded through the
valuation calculation.  The existing lower-bound engine in `StonehamSumsNormal.lean` obtains
this growth from pairwise-coprime `c_i`; it cannot be invoked unchanged when both families have
`c = 7`.

## Next highest-value attack

Generalize the reduced-denominator layer of `StonehamSumsNormal.lean` for two families with the
same prime `c = 7` and exponent gap one or two:

1. clear the two rational coefficients and express the truncated orbit state over a common
   `7`-power denominator;
2. isolate the newest two phases and show, using the appropriate cancellation-depth lemma, that
   their numerator loses at most the fixed valuation of `a² ± ac + c²`;
3. prove older kicks have strictly larger 7-adic valuation and cannot deepen that loss;
4. derive the polynomial reduced-denominator lower bound required by the existing
   `VandeheyThm51` block-mean/approximation tail;
5. instantiate it for the three pairs `(1,2)`, `(1,3)`, and `(2,3)`, prove
   `StonehamThreeSevenPairwiseNormal`, and only then restore the Maze row to
   `.refuted/.kernel`.

Keep the analytic tail factored: the new work should replace the pairwise-coprime denominator
lemma, not duplicate the later Vandehey mean estimates.
