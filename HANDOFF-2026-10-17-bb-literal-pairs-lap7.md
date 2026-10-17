# Literal Bailey--Borwein pairs lap 7 -- actual numerator reindexed as a polar tail (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Do not change either headline statement,
`VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`. The target still contains
exactly its two original headline sorries.

## Concrete crux advance

This lap connects the full-history arithmetic congruence to the fixed-resultant language instead
of leaving the connection as a proposed reindexing.

In `StonehamPairsArithmetic.lean`:

- `pow_modEq_pow_of_exponent_modEq` proves the missing modular evaluation bridge: congruent
  exponents modulo `d` give congruent powers modulo `D` whenever the base is a `d`-th root of
  unity modulo `D`.
- `exists_eventually_modEq_polarDeletedPower` combines that bridge with the already-proved
  periodicity of `stonehamPolarDeletedExponent`. One threshold and period control every fixed top
  offset after evaluation at an approximate root of unity.
- `sum_Icc_one_reflect` reindexes a positive-depth history by offsets below its top kick.

In `StonehamPairsResultant.lean`:

- `eval_polarTailPolynomial_stonehamDeleted` proves that the actual product-deleted coefficient is
  literally the evaluation of a `polarTailPolynomial`, with base-`c` weights exposed.
- `stoneham_polarRhs_eq_eval` restores the common `b^n` factor.
- `stonehamClearedFamily_mul_polarPower_modEq_polarTail` composes this identity with
  `stonehamClearedFamily_mul_polarPower_modEq_of_factor`. Thus the complete cleared one-family
  numerator, not merely its newest term, is congruent to a single dominated tail-polynomial
  evaluation at the finite Teichmuller representative.

No statement was weakened and no new `sorry`, axiom, or native computation was introduced.

## Verification

Narrow checks:

```text
lake env lean src/NormalNumbers/StonehamPairsArithmetic.lean
lake build NormalNumbers.StonehamPairsArithmetic
lake env lean src/NormalNumbers/StonehamPairsResultant.lean
```

Real gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsResultant \
  --axioms NormalNumbers.StonehamPairsNormal.pow_modEq_pow_of_exponent_modEq \
  --axioms NormalNumbers.StonehamPairsNormal.exists_eventually_modEq_polarDeletedPower \
  --axioms NormalNumbers.StonehamPairsNormal.eval_polarTailPolynomial_stonehamDeleted \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamClearedFamily_mul_polarPower_modEq_polarTail
```

It completed 8,777 jobs and ended `FORMALIZE-TIER GREEN`. All four audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged
headline sorries.

## Current blocker

The new polynomial still has length `K`: both its degree data and resultant vary with the growing
top depth, so the lap-6 fixed-resultant theorem cannot yet be applied directly. The required finite
reduction is now sharply isolated. For a proposed loss bound `q`, choose a fixed offset cutoff `S`
with `a*S > q`; all terms at offsets `s >= S` carry enough `p`-power through `c^s` to vanish at
precision `q+1`. For the finitely many offsets `s < S`, reduce deleted exponents modulo `p-1` and
use their common eventual period to obtain finitely many fixed polar-tail polynomials (one per
period class). Their nonzero resultants give a maximum fixed loss. Closing the resulting finite
maximum/threshold argument yields the uniform valuation bound for the complete one-family
numerator.

After that, add the literal two-family coefficients (bounds two for sums and one for differences),
then distinct-class rate separation and the `StonehamStateDenPowerLower` packaging.

## Next highest-value attack

Formalize a truncated evaluation congruence: if `c = p^a*u`, then modulo `p^N` the reindexed tail
evaluation agrees with its first `S` offsets whenever `N <= a*S`. Next freeze those `S` exponents
modulo `p-1` on each eventual period class and take the maximum valuation of the resulting finite
list of nonzero resultants. This is the last missing step between the proved full-numerator
congruence and a uniform one-family p-adic loss bound.
