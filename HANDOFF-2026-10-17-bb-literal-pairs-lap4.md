# Literal Bailey--Borwein pairs lap 4 -- full-history polar numerator (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Do not change either headline statement,
`VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`. The target still contains
exactly its two original headline sorries.

## Concrete crux advance

The lap-3 handoff left a genuine structural gap: the proved item (K) controlled each kick at its
own precision, while the never-silent theorem applies to one finite periodic coefficient at the
top denominator depth. `StonehamPairsArithmetic.lean` now bridges those levels.

- `stonehamPhase_mul_topTeichmuller_modEq_of_factor` replaces the level-`j` representative by the
  single top representative `b^(p^(a*K))`. Multiplication by the clearing factor `c^(K-j)` raises
  the termwise congruence from `p^(a*j+1)` to the common precision `p^(a*K+1)`.
- `stonehamPhase_mul_topTeichmuller_modEq` is the canonical `factorization`/`ordCompl` wrapper.
- `stonehamClearedFamily_mul_polar_modEq_of_factor` assembles the termwise congruences for any
  common polar multiplier `Q = W_j R_j`.
- `stonehamClearedFamily_mul_polarProduct_modEq_of_factor` chooses `Q` as the product of every
  polar unit and `R_j` as the product with `j` deleted. This gives a full-history congruence with
  no inverse or division in `ZMod`.
- `stonehamClearedFamily` and `stonehamFamily_eq_cleared_div` identify that modular calculation
  with the exact integer numerator obtained by clearing the rational family by `c^K`.

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
  --axioms NormalNumbers.StonehamPairsNormal.stonehamPhase_mul_topTeichmuller_modEq \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamClearedFamily_mul_polarProduct_modEq_of_factor \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamFamily_eq_cleared_div
```

It completed 8,776 jobs and ended `FORMALIZE-TIER GREEN`. All three declarations print exactly
`[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged headline
sorries.

## Current blocker

The remaining arithmetic step is now sharply localized. Rewrite the product-deleted factors on
the right of `stonehamClearedFamily_mul_polarProduct_modEq_of_factor` as powers of the one top
representative. After removing their common power, the exponent depends eventually periodically
on `u^j` modulo the finite order. For a literal one/two-family sum or difference, group one period
by primitive-class depth; `literalSum_tail_ne_zero` / `literalDiff_tail_ne_zero` proves that fixed
cyclotomic coefficient is nonzero. Its integer norm/resultant must then give a uniform bound on
the relevant p-adic valuation. Distinct primitive classes additionally need the kickoff's depth-
rate separation.

## Next highest-value attack

Define the product-deleted exponent sum and prove its eventual periodicity modulo the order of the
top representative modulo `p^(a*K+1)`. Package the resulting coefficient as an algebraic integer,
apply the existing literal noncancellation lemma under all embeddings, and use its nonzero norm to
obtain a K-independent p-adic cancellation bound. First finish one primitive class with one or two
families; then prove the distinct-class rate separation and expose the resulting
`StonehamStateDenPowerLower` interface consumed by `stonehamCombination_mean_tendsto_of_powerLower`.
