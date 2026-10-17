# Maze backlog lap 9 — same-prime analytic engine isolated (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order. Parts 1, 2, and 3/L1 remain
complete. Part 3/L2 remains open exactly at `StonehamThreeSevenPairwiseNormal`, after lap 7
corrected the earlier statement-faithfulness failure.

## Concrete crux advance

The existing Vandehey mean argument in `StonehamSumsNormal.lean` formerly carried pairwise
coprimality of the Stoneham parameters through every analytic layer, even though it used that
hypothesis only to prove reduced-denominator growth. This obscured the exact interface needed
by the same-prime L2 pairs.

This lap introduces the frozen arithmetic interface

```lean
StonehamStateDenLinearLower b L c m p : Prop
```

which says that the rational orbit state's reduced denominator grows at least linearly in the
orbit time, up to the fixed `stonehamCoeffBound`. The complete downstream chain is now proved
from that interface without pairwise coprimality:

- `stonehamState_block_den_bounds_of_linearLower`;
- `stonehamState_square_bound_of_linearLower`;
- `stonehamState_square_mean_tendsto_of_linearLower`;
- `stonehamState_mean_tendsto_of_linearLower`;
- `stonehamCombination_mean_tendsto_of_linearLower`.

The original pairwise-coprime declarations keep their statements and are now wrappers. The
new `stonehamState_den_linearLower` proves the interface from the old product-denominator
bound, so no established theorem was weakened.

This removes the analytic proof from the live L2 blocker. For each pair among exponents
`(1,2)`, `(1,3)`, `(2,3)`, it is now enough to combine lap 8's fixed 7-adic leading-loss lemma
with the older terms and prove `StonehamStateDenLinearLower`; the Vandehey block and Cesaro
machinery then applies unchanged. The parked Maze row now names this narrowed reopen
condition and links the interface and terminal mean theorem.

## Verification

The edited module check succeeded:

```text
lake env lean src/NormalNumbers/StonehamSumsNormal.lean
```

The repository's real scoped gate was run exactly as follows:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSumsNormal \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamState_den_linearLower \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamState_square_mean_tendsto_of_linearLower \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamState_mean_tendsto_of_linearLower \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamCombination_mean_tendsto_of_linearLower
```

It completed 10,470 jobs and ended `FORMALIZE-TIER GREEN`. All four audited declarations
have exactly `[Classical.choice, Quot.sound, propext]` as their axiom list. Reported `sorry`s
are pre-existing proof debt outside the edited module.

## Current blocker

`StonehamThreeSevenPairwiseNormal` is still open. Its analytic half is now discharged modulo
one explicit arithmetic input. What remains is to prove `StonehamStateDenLinearLower` for two
families with common `c = 7`, base `3`, and exponent gap one or two. This is hard but in-scope
mathematics, not an operator or external-condition blocker; do not call `box stuck`.

## Next highest-value attack

In `StonehamSumsBoundary.lean`, specialize the state to two families and integer coefficients:

1. split on unequal versus equal kick depths;
2. at an unequal depth, isolate the unique newest term as the strict 7-adic minimum;
3. at a tie of depth `K`, factor the two newest terms and apply
   `stoneham_pair_leadingVal_le_one` or `_two`, while proving every older term has valuation
   at least `-(K-1)`;
4. include the rational clearing denominator as a fixed additive valuation loss and derive
   `StonehamStateDenLinearLower`;
5. invoke `stonehamCombination_mean_tendsto_of_linearLower`, clear arbitrary rational
   coefficients, prove all three pairs normal, and only then restore the Maze row to
   `.refuted/.kernel`.

