# Literal Bailey--Borwein pairs lap 8 -- fixed-length polar-tail reduction (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Do not change either headline statement,
`VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`. The target still contains
exactly its two original headline sorries.

## Concrete crux advance

This lap proves the finite truncation and periodic-freezing layer requested by lap 7. In
`StonehamPairsResultant.lean`:

- `polarTail_sum_modEq_truncate_of_factor` proves that every top-offset term `s >= S` vanishes
  modulo `p^N` whenever `c = p^a*u` and `N <= a*S`.
- `polarTailPolynomial_eval_modEq_truncate_of_factor` packages this as a congruence from the
  growing length-`K` polar polynomial to its first `S` offsets.
- `polarTailPolynomial_eval_modEq_of_exponents` transfers exponent congruences through any
  approximate root of unity.
- `exists_eventually_modEq_truncatedPolarTail` combines that transfer with the established
  eventual period of the deleted exponents. One threshold and period freeze all retained offsets.
- `stonehamClearedFamily_mul_polarPower_modEq_truncatedTail` composes truncation with the actual
  full-history numerator congruence. At every precision satisfying `N <= a*S` and
  `N <= a*K+1`, the complete cleared numerator is congruent to a fixed-length polar tail.

Thus the growing polynomial/resultant obstruction from lap 7 is removed at any preassigned
precision. No statement was weakened and no new `sorry`, axiom, or native computation was
introduced.

## Verification

Narrow checks:

```text
lake env lean src/NormalNumbers/StonehamPairsResultant.lean
git diff --check
```

Real gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsResultant \
  --axioms NormalNumbers.StonehamPairsNormal.polarTail_sum_modEq_truncate_of_factor \
  --axioms NormalNumbers.StonehamPairsNormal.exists_eventually_modEq_truncatedPolarTail \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamClearedFamily_mul_polarPower_modEq_truncatedTail
```

It completed 8,777 jobs and ended `FORMALIZE-TIER GREEN`. All three audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged
headline sorries.

## Current blocker

The retained `S`-term polynomial can now be frozen on finitely many depth-period classes, but a
uniform loss bound must be chosen without a circular cutoff: if `q` is the maximum valuation of
the frozen resultants, truncation at precision `q+1` requires `q+1 <= a*S`. Merely enlarging `S`
also changes those resultants, so this inequality cannot be assumed.

The clean route is to exploit periodicity in the offset `s` itself. Sum each eventual periodic
tail as a rational geometric series with denominator `1-c^T`, a `p`-adic unit because `p | c`.
The repaired top-digit argument should prove the resulting fixed numerator nonzero. Its finitely
many period-class resultants then define `q` independently of `S`; choose `S` afterwards with
`q+1 <= a*S` and invoke this lap's truncation theorem.

## Next highest-value attack

Prove a finite geometric compression theorem for a coefficient/exponent pattern periodic modulo
`d`: `(1-c^T)` times its infinite base-`c` tail is a fixed polynomial of length `T` plus the finite
preperiod. Specialize the deleted Stoneham exponents, prove the compressed numerator nonzero by
the existing complex dominance lemma, and take the maximum p-adic valuation of the finitely many
nonzero cyclotomic resultants. Then choose `S` from that already-fixed maximum and derive the
uniform one-family numerator loss bound.
