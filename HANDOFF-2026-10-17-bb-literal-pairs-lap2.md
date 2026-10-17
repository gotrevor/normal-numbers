# Literal Bailey--Borwein pairs lap 2 — finite Teichmueller core (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Its two ratified statements and
`VandeheyThm51` were not changed. The target still contains exactly those two scoped sorries.

## Concrete crux advance

Kickoff step 2 has begun with the finite-level form of item (K). New module
`StonehamPairsArithmetic.lean` proves the reusable congruence spine without introducing a
`p`-adic completion:

- `prime_pow_succ_dvd_pow_sub_pow`: if `x-y` is divisible by `p` and `p^e`, then
  `x^p-y^p` is divisible by `p^(e+1)`. The proof uses the geometric-sum factorization and proves
  its cofactor divisible by `p`; it does not use binomial coefficients.
- `teichmullerTower_dvd` / `teichmullerTower_modEq`: consecutive representatives
  `b^(p^(K+1))` and `b^(p^K)` agree modulo `p^(K+1)` for prime `p`.
- `teichmullerTower_modEq_of_le`: every later representative reduces to the fixed level-`K`
  representative modulo `p^(K+1)`. This is the finite compatible system required for the odd
  prime polar part.
- `twoTower_dvd`: for odd `b`, `b^(2^(K+1))` is `1` modulo `2^(K+3)`, supplying the extra dyadic
  precision required by the referee's special `ell = 2` clause.

`StonehamPairsNormal.lean` imports the new arithmetic module, so this machinery is checked on the
scoped target's actual import path.

## Verification

The narrow module check passed:

```text
lake env lean src/NormalNumbers/StonehamPairsArithmetic.lean
```

The real target gate was run as:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsArithmetic \
  --axioms NormalNumbers.StonehamPairsNormal.teichmullerTower_modEq_of_le \
  --axioms NormalNumbers.StonehamPairsNormal.twoTower_dvd
```

It completed 8,776 jobs and ended `FORMALIZE-TIER GREEN`. Both audited declarations print exactly
`[Classical.choice, Quot.sound, propext]`. The two target sorries are unchanged.

## Current blocker

The finite congruence engine is proved, but it has not yet been applied to the rational Stoneham
state. The remaining arithmetic half must compare each base phase
`b^(n-c^k)` with the appropriate finite representative at every prime dividing `c`, sum the
result into the polar part, identify the periodic tail, and prove the literal one/two-family tail
never vanishes. Only then can it yield `StonehamStateDenPowerLower` for the two target states.

## Next highest-value attack

First package (K) in the exact exponent form consumed by a Stoneham term: decompose an exponent
whose `ell`-valuation is `K`, use `teichmullerTower_modEq_of_le` for odd `ell`, and extend
`twoTower_dvd` through an odd cofactor for `ell = 2`. Then prove the polar-part congruence for a
single finite family sum. Keep the eventual-periodic and never-silent layers in this module (or a
new `StonehamPairsPeriodic.lean`) and feed the resulting positive-power denominator bound directly
to `stonehamCombination_mean_tendsto_of_powerLower`.
