# Literal Bailey--Borwein pairs lap 6 review -- resultant loss bridge (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Do not change either headline statement,
`VandeheyThm51`, or Theorem A's statements in `StonehamSumsNormal.lean`. The target still contains
exactly its two original headline sorries.

## Review verdict

The checked-in theorem graph and recent commits were reconstructed rather than trusting lap 5's
narrative. Both headline statements are unchanged from the ratification commit. The positive-power
denominator interface in `StonehamPairsAnalytic.lean` still feeds the complete Weyl/normality
argument, and Theorem A cannot shortcut the open cases because its family parameters must be
pairwise coprime. The lap-5 proposed cyclotomic-resultant bridge is genuinely load-bearing and is
valid: the missing assertion is exactly that simultaneous divisibility of a finite polar
coefficient and an approximate root-of-unity equation forces divisibility of one fixed nonzero
integer.

No route change was warranted, so `DIRECTION.md` was not edited.

## Concrete crux advance

New module `src/NormalNumbers/StonehamPairsResultant.lean` closes that abstract bridge.

- `dvd_resultant_of_dvd_eval` evaluates the integral Sylvester Bezout identity: a modulus dividing
  `F(z)` and `G(z)` divides `Res(G,F)`.
- `padicValInt_eval_le_resultant` converts this into a uniform valuation bound once the precision
  of the approximate root exceeds the valuation of a nonzero resultant.
- `resultant_ne_zero_of_complex_root_nonvanishing` proves the integral resultant nonzero by mapping
  to `Complex` and using the product over all roots.
- `polarTailPolynomial` packages a finite periodic polar coefficient with arbitrary root exponents.
  `polarTailPolynomial_eval_ne_zero` applies the already-proved top-digit domination theorem at
  every complex root of unity, and `polarTail_resultant_ne_zero` supplies the resulting fixed
  nonzero integer.
- `teichmullerRepresentative_pow_pred_modEq_one` proves directly that `b^(p^K)` is a
  `(p-1)`-st root of unity modulo `p^(K+1)`, including `p = 2`.
- `padicValInt_polarTail_eval_teichmuller_le_resultant` is the complete finite-level conclusion:
  evaluation at the actual finite Teichmuller representative loses at most the fixed resultant
  valuation after a fixed depth threshold.

This introduces no new `sorry`, axiom, or native computation. The only target-file change is the
new module import; both frozen theorem statements remain byte-identical.

## Verification

Narrow checks:

```text
lake env lean src/NormalNumbers/StonehamPairsResultant.lean
lake build NormalNumbers.StonehamPairsResultant NormalNumbers.StonehamPairsNormal
```

The build completed 8,777 jobs successfully. Real gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsResultant \
  --axioms NormalNumbers.StonehamPairsNormal.teichmullerRepresentative_pow_pred_modEq_one \
  --axioms NormalNumbers.StonehamPairsNormal.padicValInt_eval_le_resultant \
  --axioms NormalNumbers.StonehamPairsNormal.resultant_ne_zero_of_complex_root_nonvanishing \
  --axioms NormalNumbers.StonehamPairsNormal.polarTail_resultant_ne_zero \
  --axioms NormalNumbers.StonehamPairsNormal.padicValInt_polarTail_eval_teichmuller_le_resultant
```

It completed 8,777 jobs and ended `FORMALIZE-TIER GREEN`. All five audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged
headline sorries.

## Current blocker

The generic uniform-loss theorem is complete, but the actual one/two-family coefficient has not
yet been expressed as one of its `polarTailPolynomial`s with data independent of the growing top
depth. The missing finite assembly is:

1. reindex the right side of
   `stonehamClearedFamily_mul_polarPower_modEq_of_factor` by offsets from the top kick;
2. use `exists_eventually_modEq_stonehamPolarDeletedExponent`, compatibility of the finite
   Teichmuller representatives, and exponents modulo `p-1` to replace the growing coefficient by
   one of finitely many periodic tail polynomials;
3. verify the literal coefficient bounds (`M = 2` for sums, `M = 1` for differences), apply the
   new fixed-resultant bound, and transfer it back to the complete cleared numerator.

After the one-class one/two-family loss bound, distinct primitive classes still need the kickoff's
depth-rate separation before packaging `StonehamStateDenPowerLower` and discharging the headlines.

## Next highest-value attack

Prove the modular evaluation bridge for congruent exponents first: if `w^d = 1` modulo `D` and
`e1 = e2` modulo `d`, then `w^e1 = w^e2` modulo `D`. Combine it with
`teichmullerTower_modEq_of_le` and
`exists_eventually_modEq_stonehamPolarDeletedExponent` to freeze the top-offset coefficient into
finitely many phase polynomials. Instantiate `padicValInt_polarTail_eval_teichmuller_le_resultant`
for the one-family case before adding the second same-class family.
