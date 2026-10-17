# Literal Bailey--Borwein pairs lap 9 reflection -- one-family units and depth separation (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Neither headline statement,
`VandeheyThm51`, nor any Theorem A statement in `StonehamSumsNormal.lean` changed. A diff from the
ratification commit `d590955e` still shows imports only in the target file. Its two original
headline sorries remain.

## Reflection verdict

The lap-8 handoff proposed geometrically compressing the periodic infinite tail in order to break
a circular cutoff/resultant bound for one family. Reconstructing the actual congruence showed that
this was too broad. For one family, top offset zero is already a `p`-adic unit and every older
offset contains a factor of `c`, hence a factor of `p`. The cleared numerator is therefore a unit
modulo every prime dividing `c`; no resultant or geometric compression is needed there.

This changes the dependency graph without changing the mathematical route:

- one family is exact and lossless at every denominator prime;
- two families at unequal `p`-depths have valuation exactly the smaller depth, so the local
  arithmetic for distinct primitive classes is complete;
- geometric compression/resultants remain genuinely necessary only after two **same-class**
  families have been aligned at one primitive-base depth, where their newest unit terms can
  cancel;
- the analytic `StonehamStateDenPowerLower` -> Weyl chain from lap 1 remains valid and unchanged.

Thus the former circular one-family cutoff was a cargo-culted subproblem, not the campaign crux.
The revised split matches Lemma 3' in the source: rate separation for distinct classes, periodic
combined tails for one class.

## Concrete crux advance

`StonehamPairsResultant.lean` now proves the complete local distinct-depth package:

- `not_dvd_stonehamClearedFamily_of_factor` proves directly from lap 8's precision-one truncation
  that the full cleared one-family numerator is not divisible by `p`.
- `not_dvd_stonehamClearedFamily` and
  `padicValInt_stonehamClearedFamily_eq_zero` provide the canonical factorization forms for every
  prime divisor of `c`.
- `padicValInt_unit_mul_pow_add_mul_pow_of_lt` proves the exact elementary separation law: a unit
  at depth `e` plus any term at depth `f > e` has valuation `e`.
- `padicValInt_pairCleared_eq_of_depth_lt` applies that law to the actual cross-cleared numerator
  of two Stoneham families, for either literal sign (indeed any integer second coefficient).
- `padicValInt_pairCleared_add_eq_min_of_depth_ne` and
  `padicValInt_pairCleared_sub_eq_min_of_depth_ne` give the exact minimum-depth valuation for
  literal sums and differences at a common prime.
- `stonehamPairFamilies_eq_cleared_div` identifies this integer with the exact common-denominator
  rational two-family state consumed by the analytic engine.

No new `sorry`, axiom, or native computation was introduced.

## Verification

Narrow check:

```text
lake env lean src/NormalNumbers/StonehamPairsResultant.lean
```

Real target/axiom gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsResultant \
  --axioms NormalNumbers.StonehamPairsNormal.not_dvd_stonehamClearedFamily \
  --axioms NormalNumbers.StonehamPairsNormal.padicValInt_stonehamClearedFamily_eq_zero \
  --axioms NormalNumbers.StonehamPairsNormal.padicValInt_pairCleared_add_eq_min_of_depth_ne \
  --axioms NormalNumbers.StonehamPairsNormal.padicValInt_pairCleared_sub_eq_min_of_depth_ne \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamPairFamilies_eq_cleared_div
```

It completed 8,777 jobs and ended `FORMALIZE-TIER GREEN`. All five audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`. The only scoped warnings are the two unchanged
headline sorries.

## Current blocker

The remaining arithmetic is now cleanly split.

1. **Distinct classes:** prove the global slope lemma. If `c1,c2` are not powers of one primitive
   integer, some prime `p` has unequal normalized factorization slopes. Consequently
   `|v_p(c1) K1(n) - v_p(c2) K2(n)|` grows linearly in `log n`. The theorems above then give a
   positive-power reduced-denominator lower bound. Exclusive-prime support is already covered by
   `padicValInt_pairCleared_eq_of_depth_lt`; the common-prime min corollaries cover overlapping
   support.
2. **Same class:** write `c_i = g^{s_i}` and align both histories at the primitive `g`-depth.
   Compress the eventual periodic **combined** coefficient by the fixed unit denominator
   `1-g^T`, prove its fixed numerator nonzero with `literalSum_tail_ne_zero` /
   `literalDiff_tail_ne_zero`, and apply the existing resultant loss bound. This is the only place
   the lap-8 geometric-compression idea remains load-bearing.
3. Package both branches as `StonehamStateDenPowerLower`, use the existing rational-state/Weyl
   assembly, and handle `c1 = c2` in the sum by `isNormal_rat_mul_add` as required by the kickoff.

## Next highest-value attack

Formalize the class dichotomy at the factorization-vector level, with a theorem that the
non-same-class branch supplies a prime of unequal normalized slope. Turn the strict asymptotic
slope gap into an eventual lower bound for the two integer depths
`c_i.factorization p * stonehamK ...`; combine it immediately with
`stonehamPairFamilies_eq_cleared_div` and the exact min-valuation lemmas. This should close the
entire distinct-class branch while simultaneously fixing the precise interface needed by the
same-class primitive-base compression.
