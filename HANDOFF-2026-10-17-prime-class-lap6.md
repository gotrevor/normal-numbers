# Prime class lap 6 REVIEW (2026-10-17): corrected mixed-state preparation

## Concrete advance

- Adversarial review found that lap 5's proposed inverse-Mahler coefficients are necessary but
  not sufficient for the common-state congruence.  A mixed `p^(s i)` history also contributes an
  inverse Teichmuller phase, a geometric factor `p^(s i) - 1`, and a depth-gap factor
  `p^(D - δ i)`.  The new `StonehamPrimeClassState.lean` records all three explicitly.
- `primeClassInverseMahlerCoefficient_ne_zero`,
  `stonehamCombination_inverseMahler`, and
  `isNormal_inverseMahlerCombination_iff` package the nonzero rational witness obtained by
  dividing an integral cyclotomic relation by the canonical Mahler multipliers.  The terminating
  corrections combine into one rational number and therefore do not affect base-`b` normality.
- `integerRelation_inverseRoot_eq_zero` and
  `prime_pow_dvd_integerRelation_eval_teichmuller_complement` orient the fixed relation correctly
  for the inverse phases in a cleared Stoneham state.  Complementary nonnegative exponents give
  the required finite Teichmuller divisibility at every precision.
- `primeClassStateCoefficientScale_mul_historyWeight` proves the exact mixed-depth identity
  ```text
  ((p^s - 1) * p^(D-δ)) * (p^δ * sum_{j<K} (p^s)^j)
    = p^D * (p^(s*K) - 1).
  ```
  Its signed family form, `prime_pow_add_dvd_sum_alignedHistories`, turns one inverse-phase
  relation modulo `p^E` into divisibility of the full aligned history by `p^(D+E)`.
- `stonehamState_eq_primeClassClearedStateNumerator_div` identifies the existing analytic
  `stonehamState` exactly with the explicit integer numerator at any common prime depth `T`.
  Finally, `exists_inverseMahlerWitness_of_not_linearIndependent` assembles the nonzero original
  rational coefficient vector, its reduced integral relation, both finite phase orientations,
  and the normality equivalence.
- No frozen theorem statement changed.  The scoped target still has exactly its two ratified
  analytic sorries; the new state module is sorry-free.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassState.lean` — success, no warnings.
- `lake build NormalNumbers.StonehamPrimeClassState` — success, 8,778 jobs.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success with only the two existing
  scoped sorry warnings.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass --import NormalNumbers.StonehamPrimeClassState` with axiom
  checks for `exists_inverseMahlerWitness_of_not_linearIndependent`,
  `prime_pow_add_dvd_sum_alignedHistories`,
  `stonehamState_eq_primeClassClearedStateNumerator_div`,
  `prime_pow_dvd_integerRelation_eval_teichmuller_complement`, and
  `isNormal_inverseMahlerCombination_iff` — 8,961 jobs; every declaration exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` — clean.

## Current blocker

The dependent/non-normal half now has the exact coefficient and numerator algebra, but it still
needs the depth/phase scheduling lemma connecting them.  Choose a positive-density periodic cell
of digit positions on which the depths
`s i * stonehamK (fun j => p^(s j)) u i n` have fixed bounded gaps `δ i` below a common depth
`T`.  On that cell, prove that the powers
`b^(n - u i * (p^(s i))^k)` appearing in `primeClassClearedStateNumerator` have, modulo the
required growing `p`-power, the common inverse-Teichmuller phases represented by the complementary
exponents.  Then `prime_pow_add_dvd_sum_alignedHistories` supplies the growing numerator
divisibility, leaving a bounded reduced denominator and the existing positive-density
zero-window contradiction.

The independent/normal half remains afterward and needs the complementary uniform bounded-loss
estimate for every nonzero relation polynomial.

## Next highest-value attack

Stay in `StonehamPrimeClassState.lean`.  First formalize the periodic depth-alignment cell and the
phase congruence for the literal summands of `primeClassClearedStateNumerator`; then specialize the
generic aligned-history divisibility theorem to that numerator.  Package the resulting bounded-
denominator statement in the form consumed by the L1/L2 zero-window machinery and discharge
`not_isRationallyJointNormal_of_not_linearIndependent` before starting the normal half.
