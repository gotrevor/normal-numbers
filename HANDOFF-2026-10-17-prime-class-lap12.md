# Prime class lap 12 (2026-10-17): T-B′ complete

## Concrete advance

- Closed the final normal-half obligation
  `StonehamPrimeClass.isRationallyJointNormal_of_linearIndependent` without changing its
  statement.  `StonehamPrimeClass.lean` is now sorry-free.
- Completed the literal arithmetic bridge in `StonehamPrimeClassPowerLower.lean`:
  - multiplying the geometric denominators reduces the complete history modulo the common
    prime depth to the bounded gap-pattern polynomial;
  - congruence beyond the valuation of a nonzero integer preserves its `p`-adic valuation;
  - the cyclotomic resultant bounds the deleted-phase evaluation uniformly over every gap
    pattern;
  - the geometric denominator product, top phase product, and `b^n` are `p`-adic units, so the
    same fixed loss bounds the actual cleared-state numerator;
  - consequently `p^(maxDepth-loss)` survives in the reduced state denominator.
- Combined that divisor with the max-depth/orbit-time estimate to prove
  `exists_primeClass_stonehamStateDenPowerLower`, then invoked the existing Vandehey/Weyl
  engine.  Zero integral coefficients are removed by restricting to their support; rational
  coefficients are handled by a common denominator.
- The kickoff endpoints are all landed and axiom-clean:
  `not_isRationallyJointNormal_of_not_linearIndependent`,
  `isRationallyJointNormal_of_linearIndependent`,
  `isRationallyJointNormal_iff_linearIndependent`,
  `isRationallyJointNormal_pair_iff`,
  `stonehamThreeSevenPairwiseNormal_holds`, and
  `stonehamThreeSeven_pairwise_not_joint_unconditional`.
- Removed the fourth and final prime-class waiver from `BarrierAudit`.  Updated the Maze row
  "joint normality is pairwise" from `.parked/.frozen` to `.refuted/.kernel`, linked it to the
  unconditional Stoneham triple counterexample, and closed its `MazeAudit` open list.

## Review findings

- Reconstructed the remaining proof route from the kickoff source, preceding campaign history,
  and the existing state/resultant interfaces.  The decisive seam was the literal common-depth
  numerator, not the already-proved finite-pattern nonvanishing.
- Checked the frozen public statements and definitions against the kickoff base commit: this lap
  changes only the final proof body in `StonehamPrimeClass.lean`; the support machinery is in the
  campaign's new `StonehamPrimeClassPowerLower.lean` module.
- Adversarially checked the edge cases used by the proof: a nonzero coefficient supplies a
  component even when the ambient family may otherwise be empty; small max depth is discharged
  by the trivial divisor; zero coefficients are removed before the all-nonzero analytic wrapper;
  and the rational clearing denominator is positive.
- No `sorry`, new axiom, or `native_decide` occurs in the target or the new power-lower module.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassPowerLower.lean` -- success.
- `lake build NormalNumbers.StonehamPrimeClassPowerLower` -- success (8,785 jobs).
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` -- success.
- `lake build NormalNumbers.StonehamPrimeClass` -- success (8,964 jobs).
- `lake build NormalNumbers.Maze` -- success (10,428 jobs).
- `lake build NormalNumbers.MazeAudit NormalNumbers.BarrierAudit` -- success (10,578 jobs);
  BarrierAudit reports 34 barriers, 26 proved, 6 cited, 2 frozen.
- Six separate `lean-green --target NormalNumbers.StonehamPrimeClass --import
  NormalNumbers.StonehamPrimeClass --axioms <declaration>` runs -- every run ended
  `FORMALIZE-TIER GREEN`, and every kickoff theorem printed exactly
  `[Classical.choice, Quot.sound, propext]`.
- Final `lean-green --target NormalNumbers.StonehamPrimeClass --import
  NormalNumbers.StonehamPrimeClass` -- 8,964 jobs, `FORMALIZE-TIER GREEN`.
- `git diff --check` -- success.
- `rg -n '\bsorry\b|\baxiom\b|native_decide'
  src/NormalNumbers/StonehamPrimeClass.lean
  src/NormalNumbers/StonehamPrimeClassPowerLower.lean` -- no matches.

## Current blocker

None.  The scoped host predicate and every additional kickoff completion condition are met.

## Next highest-value attack

No further in-scope proof attack remains.  The next operator action is review/merge of the green
campaign branch; unrelated repository proof debt should not delay this completion checkpoint.
