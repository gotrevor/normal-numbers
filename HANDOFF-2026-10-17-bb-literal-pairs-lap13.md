# Literal Bailey--Borwein pairs lap 13 -- distinct-class sum power bound (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Neither headline statement,
`VandeheyThm51`, nor any Theorem A statement in `StonehamSumsNormal.lean` changed. The target
file itself is unchanged and its two original headline sorries remain.

## Concrete crux advance

`StonehamPairsDistinct.lean` now completes the global denominator power bound for the literal
sum in the multiplicatively independent branch.

- `nat_rpow_log_ratio_le_prime_mul_prime_pow_natLog` converts the one-digit `Nat.log` error into
  the explicit inequality
  `n^(log p / log c) <= p * p^(Nat.log c n)`.
- `nat_rpow_log_ratio_le_prime_pow_mul_prime_pow_depth_sub` absorbs both a positive
  factorization multiplicity and the fixed Fourier loss `H` at cost `p^(H+1)`.
- `exists_global_power_lower_of_eventually` absorbs any finite prefix of a positive
  natural-valued denominator into the real constant.
- `eventually_pair_add_state_den_power_lower_of_prime_dvd_left` combines those estimates with
  lap 12's exact state divisor, automatic entry facts, and eventual unequal depth.
- The left/right support wrappers handle whichever base contains the slope-separating prime.
  Finally `exists_pair_add_state_den_power_lower_of_not_mulDep` selects that prime from
  `exists_prime_logSlope_ne_of_not_stonehamPairMulDep` and produces positive `rho,C` with the
  global bound required by `StonehamStateDenPowerLower` for every nonzero Fourier multiplier.

No new `sorry`, axiom, native computation, statement change, or heartbeat override was
introduced.

## Verification

Narrow check:

```text
lake env lean src/NormalNumbers/StonehamPairsDistinct.lean
```

It exited zero; only pre-existing FORMALIZE-tier `letI` style suggestions were reported.

Real target/axiom gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsNormal \
  --axioms NormalNumbers.StonehamPairsNormal.nat_rpow_log_ratio_le_prime_mul_prime_pow_natLog \
  --axioms NormalNumbers.StonehamPairsNormal.nat_rpow_log_ratio_le_prime_pow_mul_prime_pow_depth_sub \
  --axioms NormalNumbers.StonehamPairsNormal.exists_global_power_lower_of_eventually \
  --axioms NormalNumbers.StonehamPairsNormal.exists_pair_add_state_den_power_lower_of_not_mulDep
```

It completed 8,779 jobs and ended `FORMALIZE-TIER GREEN`. All four declarations print exactly
`[Classical.choice, Quot.sound, propext]`. The target reports only its two unchanged headline
sorries.

## Current blocker

The literal difference needs the same quantitative packaging. The exact divisor theorem already
exists (`prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_sub_den_of_depth_ne`), so this is a
controlled sign-generalization or a short parallel wrapper, not new arithmetic.

After that, the multiplicatively dependent/same-class branch remains the real mathematical
blocker: extract a primitive base `g` and positive exponents `s1,s2`, align both families at
`g`-depth, and use the already-proved never-silent/resultant machinery on the combined tail.
The equal-base sum should instead reduce to `2 * stonehamAlpha` and existing rational-scaling
normality; the difference headline excludes only `c1 = c2`.

## Next highest-value attack

First refactor or duplicate the new add packaging for coefficients `![h,-h]` and prove
`exists_pair_sub_state_den_power_lower_of_not_mulDep`. Then expose both results directly as
`StonehamStateDenPowerLower` witnesses and wire the distinct-class Weyl/normality branch. Do not
spend another lap on logarithmic growth: that bridge and finite-prefix absorption are complete.
