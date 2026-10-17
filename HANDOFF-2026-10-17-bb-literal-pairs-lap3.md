# Literal Bailey--Borwein pairs lap 3 review -- exponent (K) and never-silent core (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. The two ratified headline statements,
`VandeheyThm51`, and every statement in `StonehamSumsNormal.lean` remain unchanged. The target still
contains exactly its two headline sorries.

## Adversarial route review

The route still reaches both headlines. `StonehamStateDenPowerLower` feeds
`stonehamCombination_mean_tendsto_of_powerLower`; the existing approximation and Weyl machinery
then proves normality once the literal one/two-family states have a positive-power reduced-
denominator lower bound. A diff from the kickoff commit `d590955e` confirms that the target theorem
statements have not drifted: only the two intended arithmetic/analytic imports were added.

Lap 2's next move was correct but underspecified. The polar argument does not merely need the tower
representatives to be compatible: it consumes phases `b^(n-c^j)` after a factorization of `c`.
Introducing modular inverses at this stage would create avoidable `ZMod` bookkeeping. The integral
identity proved this lap multiplies the phase by its finite representative and recovers `b^n`
directly. This is the exact form needed when the rational state numerator is cleared.

The referee's repair 3 is also route-decisive, not optional cleanup. The old prose case split for
literal pairs is replaced by one complex norm inequality, valid under every cyclotomic embedding.

## Concrete crux advance

`StonehamPairsArithmetic.lean` now completes finite item (K) in the consumed exponent forms:

- `teichmullerTower_power_modEq_of_le` raises compatible representatives by the same unit part;
- `teichmullerPower_modEq_of_factor` and `teichmullerPower_modEq` specialize to
  `c = p^a u`, including the canonical `ordProj`/`ordCompl` factorization;
- `twoPower_modEq_one`, `twoPower_modEq_one_of_factor`, and
  `twoPower_modEq_one_of_even` prove the full dyadic precision;
- `stonehamPhase_mul_teichmuller_modEq` packages the odd-prime polar phase integrally;
- `twoStonehamPhase_modEq` packages the dyadic polar phase.

The same module now proves the repaired never-silent core:

- `mul_sum_range_pow_lt_pow`: `M * sum_{s<J} g^s < g^J` whenever `M < g`;
- `geom_weighted_sum_ne_zero_of_norm`: a complex base-`g` polynomial with a nonzero top
  coefficient and lower coefficient norms at most `M < g` cannot vanish;
- `literalSum_tail_ne_zero`: coefficient norms at most two, for `g >= 3`;
- `literalDiff_tail_ne_zero`: coefficient norms at most one, for `g >= 2`.

Thus the finite congruence spine and the mathematical noncancellation statement at the far end of
the periodic-tail argument are both kernel-proved. No new `sorry`, axiom, or native computation was
introduced.

## Verification

The narrow checks passed:

```text
lake env lean src/NormalNumbers/StonehamPairsArithmetic.lean
lake env lean src/NormalNumbers/StonehamPairsNormal.lean
```

The real target gate was run as:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsArithmetic \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamPhase_mul_teichmuller_modEq \
  --axioms NormalNumbers.StonehamPairsNormal.twoStonehamPhase_modEq \
  --axioms NormalNumbers.StonehamPairsNormal.literalSum_tail_ne_zero \
  --axioms NormalNumbers.StonehamPairsNormal.literalDiff_tail_ne_zero
```

It completed 8,776 jobs and ended `FORMALIZE-TIER GREEN`. All four audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`. The gate reports only the two unchanged scoped
headline sorries in `StonehamPairsNormal.lean` (plus unrelated debt in imported legacy modules).

## Current blocker

The bridge between the two proved ends is still open: assemble the individual phase congruences
into the one/two-family polar coefficient, prove its eventual periodicity, and turn nonvanishing of
the fixed cyclotomic coefficient into a uniform bound on numerator cancellation. Then compare the
prime-depth rates of two distinct primitive classes. This is the remaining arithmetic content of
Lemma 3-prime and is exactly what must yield `StonehamStateDenPowerLower`.

## Next highest-value attack

Stay with one or two literal families; do not formalize all of Theorem C. Define the cleared
single-family numerator at a prime `p | c`, use `stonehamPhase_mul_teichmuller_modEq` term-by-term,
and isolate the finite polar coefficient indexed by `ordCompl[p] c ^ j`. Prove its eventual
periodicity modulo `ord_p(b)`. For a same-class literal pair, express one full period as the
base-`g` polynomial consumed by `literalSum_tail_ne_zero` / `literalDiff_tail_ne_zero`, then use a
fixed integer norm or resultant to bound its `p`-adic cancellation uniformly. In the distinct-
class case, prove that unequal depth slopes make one nonzero polar coefficient strictly deepest.
Those two cases should directly supply the positive-power denominator bound and allow the existing
Weyl assembly to discharge both headlines.
