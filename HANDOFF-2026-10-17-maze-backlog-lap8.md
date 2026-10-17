# Maze backlog lap 8 — fixed 7-adic loss proved (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  Parts 1, 2, and 3/L1 remain complete.
Part 3/L2 remains open exactly at `StonehamThreeSevenPairwiseNormal`, as exposed by lap 7.

## Concrete crux advance

Lap 7's `stoneham_pair_cancellationDepth_le_one` and `_two` only said that cancellation
*through the entire kick depth* forces that depth below a fixed coefficient-norm valuation.
That implication alone did not yet justify the handoff's stronger phrase “loses at most the fixed
valuation”: a leading coefficient might conceivably have had an intermediate valuation.

`StonehamSumsBoundary.lean` now proves the actual eventual fixed-loss statements:

- `stoneham_pair_leadingVal_le_one` bounds
  `v₇(a + c·3^(7^n))` by `v₇(a²+ac+c²)` once `n` exceeds the latter;
- `stoneham_pair_leadingVal_le_two` bounds
  `v₇(a + c·(3^(7^n))²)` by `v₇(a²-ac+c²)` under the analogous threshold.

The proof is the missing two-scale argument.  If the leading valuation reached `n`, lap 7's
cancellation-depth theorem would contradict the threshold.  Hence it is below `n`; the already
proved cyclotomic congruence modulo `7^n` can then be lowered to precisely that valuation, and the
quadratic resultant forces the same power of seven into the fixed nonzero coefficient norm.

This is the load-bearing arithmetic conclusion needed at an equal-depth tie: after finitely many
kicks, the two newest terms lose only a coefficient-dependent constant number of denominator
powers.

## Verification

The edited module check succeeded:

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

The real scoped gate was then run exactly as follows:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSumsBoundary \
  --axioms NormalNumbers.stoneham_pair_leadingVal_le_one \
  --axioms NormalNumbers.stoneham_pair_leadingVal_le_two
```

It completed 10,470 jobs and ended `FORMALIZE-TIER GREEN`.  Both new declarations have exactly
`[Classical.choice, Quot.sound, propext]` as their axiom list.  Reported `sorry`s are pre-existing
proof debt outside the edited module.

## Current blocker

`StonehamThreeSevenPairwiseNormal` is still open.  The new lemmas control equal-depth ties, but the
full state proof must also split unequal depths, show older kicks have strictly larger valuation,
and convert the resulting state valuation into a reduced-denominator lower bound in the form used
by `stonehamState_mean_tendsto`.

This is hard but in-scope mathematics, not an operator/external blocker.  Do not call `box stuck`.

## Next highest-value attack

Prove a two-family same-prime replacement for `padicValRat_stonehamState_le`:

1. specialize to `c = 7`, base `3`, exponent pairs `(1,2)`, `(1,3)`, and `(2,3)`;
2. when the two `stonehamK`s differ, use the unique newest family as the strict valuation minimum;
3. when they agree at depth `K`, factor the two newest terms and apply the new `_leadingVal_le_*`
   theorem, while the older terms have valuation at least `-(K-1)`;
4. deduce `K-C ≤ padicValNat 7 state.den`, hence a linear-in-time reduced-denominator lower bound;
5. replace only the coprime denominator input in the existing Vandehey block-mean argument and
   instantiate all three pairs.
