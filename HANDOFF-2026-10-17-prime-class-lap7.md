# Prime class lap 7 (2026-10-17): full-precision phase alignment

## Concrete advance

- `StonehamPrimeClassState.lean` now proves the missing finite phase bridge from the literal
  cleared Stoneham histories to lap 6's abstract aligned-history algebra.
- `primeClassPhase_mul_topTeichmuller_modEq` replaces one entered phase by the top finite
  Teichmuller representative at the full precision `p^(s*K+1)` after denominator clearing.
- `primeClassClearedHistory_mul_topTeichmuller_modEq` sums that congruence and identifies the
  remaining coefficient exactly with `primeClassHistoryWeight`, including an arbitrary common-
  depth gap `δ`.
- `primeClassClearedHistories_mul_phaseProduct_modEq` assembles all families using the product of
  their top phases.  The coefficient left in family `i` is precisely the product with `i`
  deleted.
- `primeClassDeletedPhaseProduct_modEq` identifies that deleted product with the common finite
  representative raised to `primeClassComplementExponent u i`.  Consequently
  `prime_pow_dvd_integerRelation_deletedPhaseProducts` transfers the complementary cyclotomic
  relation proved in lap 6 to the actual mixed-depth phase products.
- No frozen statement changed.  The scoped target still has exactly its two ratified analytic
  sorries; the enlarged state module is sorry-free.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassState.lean` — success, no warnings.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success with only the two existing
  scoped sorry warnings.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass --import NormalNumbers.StonehamPrimeClassState` with axiom
  checks for the five new declarations above — 8,961 jobs; every declaration exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` — clean.

## Current blocker

The local phase/cyclotomic algebra is now connected.  The dependent/non-normal half still needs
the global scheduling and denominator wrapper.  Choose a positive-density periodic cell of
positions `n` on which
`K i = stonehamK (fun j => p^(s j)) u i n` has bounded fixed gaps
`δ i = T - s i*K i` from a common depth `T`.  On that cell, specialize
`primeClassClearedHistories_mul_phaseProduct_modEq`; combine
`prime_pow_dvd_integerRelation_deletedPhaseProducts` with
`prime_pow_add_dvd_sum_alignedHistories`; then cancel the phase product, which is coprime to `p`,
to obtain growing divisibility of the literal `primeClassClearedStateNumerator`.  Convert that to
a bounded reduced denominator via `stonehamState_eq_primeClassClearedStateNumerator_div` and feed
the existing positive-density zero-window contradiction.

The independent/normal half remains afterward and needs the complementary uniform bounded-loss
estimate for every nonzero relation polynomial.

## Next highest-value attack

First package the just-proved congruences and aligned-history divisibility into one theorem for
`primeClassClearedStateNumerator` under abstract fixed-gap hypotheses, including coprime
cancellation of the common phase product.  Then prove the periodic fixed-gap cell for the literal
`stonehamK` depths and discharge
`not_isRationallyJointNormal_of_not_linearIndependent` before starting the normal half.
