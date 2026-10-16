# Stoneham sums normal — lap 3 COMPLETE (2026-10-16)

## Concrete advance

The scoped target `src/NormalNumbers/StonehamSumsNormal.lean` is now sorry-free.  The frozen
Theorem A statement `isNormal_stonehamCombination` and its frozen headline specialization
`isNormal_two_stoneham_three_add_five` are proved without changing their statements.  Together
with lap 1's `vandeheyCor12_of_thm51`, all three kickoff declarations are complete.

This lap closed the whole remaining paper route:

- Proved the sharp reduced-denominator lower bound.  The new valuation stack isolates the unique
  newest term at every prime dividing an active `c i`, shows that it survives the other
  pairwise-coprime families, and derives
  `n^r ≤ state.den * ((∏ i, |p i|) * ∏ i, m i * c i)`.
- Proved the real Stoneham tail estimate and the full combination approximation
  `|b^n ξ - S_n| ≤ C₀/n`.
- Formalized the kick-block partition of `[1,J²]`.  There are at most
  `1 + r * log₂(J²)` bad blocks; on every other length-`J` block the rational state follows
  exact multiplication by `b`.
- Applied the derived Vandehey Corollary 1.2 on good blocks using the polynomial upper/lower
  denominator bounds, and proved square-time Weyl cancellation.
- Used `DecayAeNormal.tendsto_of_tendsto_sq` to interpolate square-time means to all Cesàro means,
  then transferred the result from `S_n` to `b^n ξ` with the `O(1/n)` phase error.
- Proved normality first for nonzero integer coefficients, reindexed to the active support to
  remove zero coefficients, cleared arbitrary rational denominators, and transported normality
  back with `isNormal_rat_mul_add`.

`STATUS.md` now records Theorem A and the `α₂,₃ + α₂,₅` headline.  No Maze row claimed
the pairwise-coprime theorem was open: the two Stoneham rows concern the still-valid
same-parameter counterexample `α₂,₃ + α₄,₃`, so the register was not changed.
The now-obsolete direct-sorry waiver for Theorem A was removed from `BarrierAudit.lean`.

## Verification

All of the following succeeded in this lap:

```text
lake env lean src/NormalNumbers/StonehamSumsNormal.lean
lake build NormalNumbers.StonehamSumsNormal
rg -n "sorry|admit" src/NormalNumbers/StonehamSumsNormal.lean
```

The `rg` command has no matches.  The real repository gate, including the three headline axiom
audits, was:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-stoneham-sums \
  --target NormalNumbers.StonehamSumsNormal \
  --axioms NormalNumbers.StonehamSumsNormal.vandeheyCor12_of_thm51 \
  --axioms NormalNumbers.StonehamSumsNormal.isNormal_stonehamCombination \
  --axioms NormalNumbers.StonehamSumsNormal.isNormal_two_stoneham_three_add_five
```

Verdict: `✅ FORMALIZE-TIER GREEN` (8762 jobs).  Each audited declaration depends exactly on
`[propext, Classical.choice, Quot.sound]`; the cited `VandeheyThm51` remains an explicit theorem
binder and is not an axiom.

The final full-repository gate also succeeded after the barrier audit required deletion of the
obsolete Theorem A waiver:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-stoneham-sums
```

Verdict: `✅ FORMALIZE-TIER GREEN` (10854 jobs); barrier audit: 34 barriers, 25 linked cruxes,
77 waivers, 104 unrelated open sorries scanned.

## Current blocker

None.  The host completion predicate and every kickoff done condition are met.  Unrelated sorries
reported by the repository-wide build are outside this scoped target.

## Next highest-value attack

Stop this treadmill campaign.  If the branch is reopened for publication work, the next useful
task is exposition/refactoring of the long block-estimate section, not further proof search; it
must preserve the three audited axiom baselines and the now-green scoped target.
