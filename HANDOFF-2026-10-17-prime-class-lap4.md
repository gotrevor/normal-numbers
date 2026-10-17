# Prime class lap 4 (2026-10-17): Mahler exponent normalization

## Concrete advance

- Added `StonehamPrimeClassMahler.lean`, proving the exact Mahler identity
  `alpha_(B^c,c) = c * alpha_(B,c) - B^(-c)` directly from the convergent defining series.
- `stonehamAlpha_pow_base_iterate` iterates the identity through an arbitrary power `c^a` and
  records the entire terminating correction as a finite sum.  The exponent-form corollary
  `stonehamAlpha_exponent_mul_pow` states the result in the parameters used by
  `primeClassFamily`: a factor `c^a` in `m` becomes the nonzero coefficient `c^a`, plus a finite
  base-`b` rational correction.
- This closes the exact algebraic substep requested in kickoff step 2 for moving factors of
  `p^s` out of `m` before assembling the mixed-`s i` state.  The new module is imported by the
  scoped target and root library.  No frozen statement changed; the target still has exactly its
  two ratified analytic sorries.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassMahler.lean` — success.
- `lake build NormalNumbers.StonehamPrimeClassMahler` — 8,763 jobs, success.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success with only the two existing
  scoped sorry warnings.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass --import NormalNumbers.StonehamPrimeClassMahler` with separate
  axiom checks for `stonehamAlpha_pow_base`, `stonehamAlpha_pow_base_iterate`, and
  `stonehamAlpha_exponent_mul_pow` — 8,960 jobs; every declaration exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` — clean.

## Current blocker

The dependent/non-normal half still needs the common-state theorem.  For each index, write
`m i = u_i * p^(s_i*q_i+r_i)` with `r_i < s_i`.  The new iterate moves the `p^(s_i*q_i)` factor
into a coefficient `(p^s_i)^q_i`; since `orderOf (b : ZMod p) | p-1`, multiplication of the
remaining exponent by any power of `p` does not change its cyclotomic phase.  Choosing the
original rational coefficient with the inverse of that Mahler factor therefore recovers the
fixed integral cyclotomic relation, while the finite corrections terminate in the base-`b`
orbit.  What remains is to formalize this canonical factorization/coefficient choice and show
the resulting mixed subseries has the required long bounded-denominator pieces.

The normal half remains after the dependent half and needs the complementary bounded-loss
statement for a nonzero relation polynomial.

## Next highest-value attack

Continue kickoff step 2 in `StonehamPrimeClassMahler.lean`: use `m.factorization p`,
`ordCompl[p] m`, and Euclidean division by `s` to prove the per-index normalized identity and the
root-of-unity phase invariance `zeta^(u*p^r) = zeta^m`.  Package the inverse Mahler coefficient
vector and prove it remains nonzero and realizes the original integral cyclotomic relation.
Then assemble the common rational state and generalize the L1/L2 zero-window contradiction.
