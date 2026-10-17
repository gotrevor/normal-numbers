# Literal Bailey--Borwein pairs lap 14 -- COMPLETE (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order, with host gate
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. The two ratified headline statements,
`VandeheyThm51`, and every Theorem A statement in `StonehamSumsNormal.lean` remain unchanged.

The scoped objective is complete: `StonehamPairsNormal.lean` is sorry-free, its target build is
green, both headline theorems have exactly the standard trust-base axioms, and the two temporary
`BarrierAudit` waivers were removed.

## Concrete crux advance

This lap closes every remaining branch of the literal sum and difference.

- `StonehamPairsAnalytic.lean` exposes the positive-power denominator interface through the full
  Vandehey/Weyl argument, plus the one-family and equal-family endpoints.
- `StonehamPairsDistinct.lean` completes the prime-divisor denominator bounds for both literal
  signs and packages multiplicatively independent pairs as normal.
- `StonehamPairsClasses.lean` proves that a multiplicatively dependent pair at least two consists
  of positive powers of one integral common base.
- New `StonehamPairsSameClass.lean` aligns `g^s` families over `g^(Nat.log g n)`, proves the exact
  common-denominator identities, and bounds cancellation uniformly. Differences work at every
  prime divisor of `g`. Sums split into:
  - an odd-prime branch, where tied newest kicks have unit coefficient `2`; and
  - the genuinely dyadic branch, where a geometric-tail congruence through precision `2^(J+2)`
    handles the exceptional tied phases, including step size one.
- The common-base sum endpoint removes the full 2-primary part of `g`: a remaining odd factor
  supplies the odd-prime branch, while complementary part one rewrites `g` as a power of two and
  invokes the dyadic theorem.
- `StonehamPairsNormal.lean` now dispatches equal bases, distinct multiplicative classes, and
  unequal powers in one class for the sum; and distinct versus same classes for the difference.
- `BarrierAudit.lean` no longer waives the two headline declarations.

No new `sorry`, axiom, native computation, statement change, or heartbeat override was introduced.

## Verification

Narrow and target builds:

```text
lake env lean src/NormalNumbers/StonehamPairsSameClass.lean
lake build NormalNumbers.StonehamPairsSameClass NormalNumbers.StonehamPairsNormal
rg -n '\bsorry\b' src/NormalNumbers/StonehamPairsNormal.lean
```

The Lean check exited zero, the target build completed 8,780 jobs, and the grep returned no match.

Real target and axiom gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsNormal \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_add \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_sub \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_add_of_common_power \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_sub_of_common_power \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_add_of_not_mulDep \
  --axioms NormalNumbers.StonehamPairsNormal.isNormal_stonehamAlpha_sub_of_not_mulDep
```

It completed 8,780 jobs and ended `FORMALIZE-TIER GREEN`. Every audited declaration prints exactly
`[Classical.choice, Quot.sound, propext]`.

After removing the stale waivers:

```text
lake build NormalNumbers.BarrierAudit
```

It completed 10,371 jobs successfully; the audit reports 34 barriers, 25 linked cruxes, 77 waivers,
and 104 open sorries scanned.

## Stretch review

The kickoff's conditional stretch target `StonehamThreeSevenPairwiseNormal` is not a corollary of
the machinery proved here. The literal Bailey--Borwein theorem fixes digit base `b`, varies the
Stoneham denominators `c₁,c₂`, and needs coefficient ratio `+1` or `-1`. The stretch proposition
instead fixes `c = 7`, varies digit-base exponents `m in {1,2,3}`, and quantifies over every
rational coefficient pair. Its existing tied-depth quadratic-norm lemmas remain useful, but it
still needs the unequal-depth state-denominator argument recorded in
`HANDOFF-2026-10-17-maze-backlog-lap10.md`. The Maze row therefore remains honestly parked.

## Current blocker

None for the scoped campaign. The host completion predicate and all kickoff done conditions are
met.

## Next highest-value attack

For optional stretch work only: return to the three-seven pairwise premise, prove the two
`stonehamK 7 m n` depths differ by at most one for `m in {1,2,3}`, control the unequal-depth
cleared numerator for arbitrary integer coefficient pairs, and package that as
`StonehamStateDenLinearLower`. Do not reopen the completed literal-pair proof.
