# Prime class lap 8 (2026-10-17): literal cleared-state divisibility

## Concrete advance

- `StonehamPrimeClassState.lean` now packages the complete fixed-gap arithmetic step requested by
  lap 7.
- `primeClassClearedStateNumerator_eq_alignedHistories` identifies the literal numerator, whose
  depths are defined by `stonehamK`, with the aligned-history expression once the selected depths
  and common-depth gaps are fixed.
- `prime_pow_add_dvd_primeClassClearedStateNumerator` composes the full-precision phase congruence,
  the complementary cyclotomic relation, and aligned-history divisibility.  It then proves that
  the common finite phase product is prime to `p` and cancels it, yielding
  `p^(D+E)` divisibility of the actual cleared-state numerator.
- No frozen statement changed.  The scoped target still has exactly its two ratified analytic
  sorries; the enlarged state module is sorry-free.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassState.lean` — success, no warnings.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success with only the two existing
  scoped sorry warnings.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass --import NormalNumbers.StonehamPrimeClassState --axioms
  NormalNumbers.StonehamPrimeClass.primeClassClearedStateNumerator_eq_alignedHistories --axioms
  NormalNumbers.StonehamPrimeClass.prime_pow_add_dvd_primeClassClearedStateNumerator` — 8,961
  jobs; both declarations exactly `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check` — clean.

## Current blocker

The dependent/non-normal half now lacks only its scheduling and analytic wrapper.  For the
reduced exponents `u i`, construct a positive-density periodic cell of positions `n` on which
`K i = stonehamK (fun j => p^(s j)) u i n` has fixed bounded gaps
`δ i = T - s i*K i` from one common depth `T`.  The new theorem then gives growing divisibility
of the literal numerator.  This must be converted, through
`stonehamState_eq_primeClassClearedStateNumerator_div`, into a uniformly bounded reduced
denominator (or directly into a finite-grid orbit constraint), and fed to a general
positive-density obstruction to base-`b` normality.

The independent/normal half remains afterward and needs the complementary uniform bounded-loss
estimate for every nonzero relation polynomial.

## Next highest-value attack

Prove the periodic fixed-gap cell for the literal `stonehamK` depths.  Package enough inequalities
on that cell to instantiate `prime_pow_add_dvd_primeClassClearedStateNumerator` with `E` growing
and fixed `D`; then prove the bounded-denominator-to-non-normal analytic lemma and discharge
`not_isRationallyJointNormal_of_not_linearIndependent` before starting the normal half.
