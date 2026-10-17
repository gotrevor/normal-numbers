# Prime class lap 10 (2026-10-17): bounded max-depth patterns

## Concrete advance

- Added the sorry-free `StonehamPrimeClassPowerLower.lean` and imported it from the scoped target.
- Defined the weighted entered depth `s_i K_i(n)`, its finite-family maximum, and the gap below
  that maximum.
- Proved `primeClassMaxDepthGap_lt`: for every nonzero orbit time,
  `T(n) - s_i K_i(n) < u_i + s_i`.  The proof is elementary and uniform: the next kick of
  component `i` bounds `n` above, component `j` bounds it below, and `u_i <= p^u_i` converts the
  comparison to exponents.  Thus there is no time-dependent scheduling loss.
- Packaged the gap vector as `primeClassGapPattern : ∀ i, Fin (u i + s i)`, making the finite
  pattern space explicit in Lean rather than leaving finiteness in prose.
- Proved `orbitTime_lt_prime_pow_add_maxDepth`, namely
  `n < p^(u_i + T(n) + s_i)` for every chosen component.  Hence once a divisor
  `p^(T-B)` is obtained, the existing power-denominator API can receive a positive (indeed
  linear-scale before fixed losses) lower bound.
- Proved `cyclotomic_resultant_integerRelation_ne_zero`: under independence of the chosen powers
  of a primitive root, every nonzero cleared integral coefficient polynomial has nonzero
  resultant with the cyclotomic polynomial.  This is the per-pattern fixed obstruction needed
  to bound p-adic cancellation.
- Added a singleton content anchor: its max-depth gap is identically zero.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassPowerLower.lean` -- success, no output.
- `lake build NormalNumbers.StonehamPrimeClassPowerLower` -- success, 8,783 jobs.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` -- success; only the existing
  independent/normal-half `sorry` warning remains.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target NormalNumbers.StonehamPrimeClass
  --import NormalNumbers.StonehamPrimeClass` with axiom checks for
  `primeClassMaxDepthGap_lt`, `orbitTime_lt_prime_pow_add_maxDepth`,
  `cyclotomic_resultant_integerRelation_ne_zero`, and the previously proved dependent headline --
  8,964 jobs; every checked declaration is exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

Only `isRationallyJointNormal_of_linearIndependent` remains directly sorried.  For a fixed
nonzero Fourier coefficient vector, inverse-Mahler normalization first gives a nonzero integral
coefficient vector on the reduced exponents `u_i`.  At a max-depth gap pattern `delta`, clearing
the mixed histories produces a polynomial in the finite Teichmuller phase whose coefficients are
the original coefficients multiplied by nonzero factors built from `p^delta_i` and
`p^(s_j)-1`.  Its exponents are the complementary exponents already used by the dependent-half
state algebra.

The next seam is to prove that independence of `zeta^u_i` is preserved by this complementary
orientation, then state the exact pattern polynomial and prove it nonzero.  The new resultant
lemma supplies one nonzero integer per pattern.  Since `primeClassGapPattern` ranges over a finite
type, maximize their p-adic valuations to obtain one uniform loss `B`.  The existing finite-phase
congruence and rational state bridge should then give `p^(T-B)` in the reduced denominator.

## Next highest-value attack

In `StonehamPrimeClassPowerLower.lean`, prove
`LinearIndependent Q (fun i => zeta^(primeClassComplementExponent u i))` from independence of
`zeta^u_i` (use the inverse primitive root plus multiplication by the common nonzero
`zeta^(sum u)`).  Define the gap-pattern cleared coefficient vector and apply
`cyclotomic_resultant_integerRelation_ne_zero` to it.  Package the maximum resultant valuation
over `∀ i, Fin (u i + s i)`, then connect that bound to the literal cleared-state numerator and
reduced denominator.  Do not revisit scheduling: both bounded patterns and growth of `T` are now
kernel-proved.
