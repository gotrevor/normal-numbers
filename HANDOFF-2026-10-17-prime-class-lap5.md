# Prime class lap 5 (2026-10-17): canonical mixed-`s` exponent normalization

## Concrete advance

- `StonehamPrimeClassMahler.lean` now defines the canonical split
  `m = u * (p^s)^a`, where `a = v_p(m) / s` and
  `u = ordCompl[p](m) * p^(v_p(m) % s)`.
- `primitiveRoot_pow_primeClassReducedExponent` proves that this reduction preserves the
  cyclotomic phase: `ζ^u = ζ^m`.  The familywise corollary shows that the exact linear-
  independence criterion in T-B' is unchanged after reducing every exponent with its own `s i`.
- `stonehamAlpha_primeClass_normalize` combines the split with lap 4's iterated Mahler identity:
  each original family member is a nonzero power-of-`p^s` multiple of its reduced member, minus
  an explicit finite base-`b` rational correction.
- This closes the canonical factorization and phase-invariance substep requested after lap 4.
  No frozen statement changed.  The scoped target still has exactly its two ratified analytic
  sorries.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassMahler.lean` — success.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success with only the two existing
  scoped sorry warnings.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass --import NormalNumbers.StonehamPrimeClassMahler` with axiom
  checks for `primeClassReducedExponent_mul_pow`,
  `primitiveRoot_pow_primeClassReducedExponent`,
  `primitiveRoot_primeClassReducedPowers_eq`,
  `linearIndependent_primeClassReducedPowers_iff`, and
  `stonehamAlpha_primeClass_normalize` — 8,960 jobs; every declaration exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` — clean.

## Current blocker

The dependent/non-normal half still needs the common-state theorem.  Lap 5 reduces every
`m i` to a phase-equivalent exponent `u i` with `v_p(u i) < s i`, and identifies the required
Mahler multiplier `(p^(s i))^(a i)`.  The next proof must choose the original rational Fourier
coefficient by dividing the fixed nonzero integral cyclotomic relation coefficient by this
multiplier.  The finite corrections then terminate in the base-`b` orbit.  What remains is to
show that the mixed reduced subseries has long pieces whose cleared numerator is divisible by
the growing power supplied by `exists_integerRelation_prime_pow_dvd_teichmuller_of_not_linearIndependent`,
and convert those pieces to the L1/L2 positive-density zero-window contradiction.

The normal half remains afterward and needs the complementary bounded-loss statement for every
nonzero relation polynomial.

## Next highest-value attack

Continue kickoff step 2 in a new `StonehamPrimeClassState.lean`: package the inverse Mahler
coefficient vector, prove it is nonzero and that its normalized cyclotomic relation is the fixed
integral one, then formulate and prove the mixed-`s` cleared-state congruence.  Feed that congruence
into a generalized version of the zero-window argument in `StonehamSumsBoundary.lean` to discharge
`not_isRationallyJointNormal_of_not_linearIndependent`.
