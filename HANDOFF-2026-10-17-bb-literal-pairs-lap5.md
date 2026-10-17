# Literal Bailey--Borwein pairs lap 5 -- finite polar period (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Do not change either headline statement,
`VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`. The target still contains
exactly its two original headline sorries.

## Concrete crux advance

Lap 4 assembled the product-deleted polar coefficient but left its dependence on the top depth
inside a large product. `StonehamPairsArithmetic.lean` now exposes and controls that dependence.

- `stonehamPolarExponent` and `stonehamPolarDeletedExponent` are the full and one-factor-deleted
  exponent sums. `stoneham_polarProduct_eq_pow` and `_erase_eq_pow` rewrite the corresponding
  products as single powers.
- `stonehamClearedFamily_mul_polarPower_modEq_of_factor` is the power-normalized full-history
  congruence. Its right side depends on a kick only through the deleted exponent.
- `exists_eventually_modEq_pow_and_geomSum` proves, by a finite-state pigeonhole argument, that
  `u^K` and its running geometric sum share an eventual period modulo every positive modulus.
  It deliberately assumes no coprimality, so it covers referee repair 2's preperiodic case
  `gcd(u,d) > 1`.
- `exists_eventually_modEq_stonehamPolarDeletedExponent` transfers that period to every fixed
  top offset `j = K-s`, with one period working uniformly in `s` after the linear threshold.

No existing statement changed and no new `sorry`, axiom, or native computation was introduced.

## Verification

Narrow checks:

```text
lake env lean src/NormalNumbers/StonehamPairsArithmetic.lean
lake env lean src/NormalNumbers/StonehamPairsNormal.lean
```

Real gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsArithmetic \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamClearedFamily_mul_polarPower_modEq_of_factor \
  --axioms NormalNumbers.StonehamPairsNormal.exists_eventually_modEq_pow_and_geomSum \
  --axioms NormalNumbers.StonehamPairsNormal.exists_eventually_modEq_stonehamPolarDeletedExponent
```

It completed 8,776 jobs and ended `FORMALIZE-TIER GREEN`. All three declarations print exactly
`[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged headline
sorries.

## Current blocker

The finite polar coefficient is now genuinely periodic, but nonvanishing over `Complex` has not
yet been converted into a uniform integer p-adic loss. The missing bridge should avoid building
general number-field norm infrastructure if possible: the finite representative has finite order
modulo `p^(aK+1)`, and the periodic coefficient is a fixed Laurent polynomial in that root. One
needs a fixed nonzero integer (cyclotomic resultant/norm) annihilating any common divisor of this
coefficient and the relevant cyclotomic modulus. Its fixed `p`-valuation gives the desired loss.

After the one-class one/two-family loss bound, distinct primitive classes still need the kickoff's
depth-rate separation before the result can be packaged as `StonehamStateDenPowerLower`.

## Next highest-value attack

Define the finite literal periodic coefficient in `ZMod (p^(a*K+1))` using the new deleted exponent
period, and prove a Bézout/resultant bound: `literalSum_tail_ne_zero` / `literalDiff_tail_ne_zero`
implies its fixed integer resultant is nonzero, hence bounds the p-adic valuation uniformly in
`K`. Finish one primitive class first, then combine the two families and prove distinct-class rate
separation before wiring `stonehamCombination_mean_tendsto_of_powerLower`.
