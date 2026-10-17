# Prime class lap 11 (2026-10-17): finite-pattern resultant loss

## Concrete advance

- Extended the sorry-free `StonehamPrimeClassPowerLower.lean` along the remaining normal-half
  route.
- Proved `linearIndependent_powers_complement`: replacing every exponent `u_i` by the common-cap
  complement `sum(u)-u_i` preserves rational linear independence.  The proof passes through the
  inverse primitive root and cancels the common nonzero root-of-unity factor.
- Defined the exact fixed-gap coefficient vector `primeClassPatternCoefficient`.  Its `i`-th
  entry is the Fourier coefficient times `p^delta_i` and the product of all geometric
  denominators `(p^s_j-1)` with `j != i`; this is the coefficient naturally paired with the
  deleted finite-phase product in the cleared state.
- Proved that this coefficient vector is nonzero for every gap pattern whenever the Fourier
  vector is nonzero.
- Proved `cyclotomic_resultant_primeClassPattern_ne_zero`: independence makes the cyclotomic
  resultant of the complementary-exponent pattern polynomial nonzero for every pattern.
- Defined `primeClassPatternResultantLoss` as the supremum of the `p`-adic valuations of these
  resultants over the fixed finite type `forall i, Fin (u_i+s_i)`, and proved every pattern is
  bounded by it.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassPowerLower.lean` -- success, no output.
- `lake build NormalNumbers.StonehamPrimeClassPowerLower` -- success, 8,783 jobs.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target NormalNumbers.StonehamPrimeClass
  --import NormalNumbers.StonehamPrimeClass` with separate `--axioms` checks for
  `linearIndependent_powers_complement`, `primeClassPatternCoefficient_ne_zero`,
  `cyclotomic_resultant_primeClassPattern_ne_zero`,
  `padicValInt_patternResultant_le_loss`, and the dependent headline -- 8,964 jobs; every checked
  declaration has exactly `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

Only `isRationallyJointNormal_of_linearIndependent` remains directly sorried.  The finite loss
constant is now present and proved to bound the correct nonzero resultants.  What remains is the
literal modular bridge from the common-depth numerator to the pattern polynomial.

Let `T=max_i(s_i K_i)`, `delta_i=T-s_i K_i`, `G=product_i(p^s_i-1)`, and let `P` be the product of
the top finite Teichmuller phases.  Multiplying the existing cleared-history congruence by `G`
and using the geometric-history identity should give, modulo `p^T`,

`G * N * P == -b^n * sum_i patternCoefficient(delta)_i * deletedPhaseProduct_i`.

The discarded newest terms have a factor `p^T`; this is why the clean statement is modulo `p^T`
rather than the existing `p^(T+1)` precision.  At any precision below all `s_i K_i`, the deleted
phase products become the pattern polynomial evaluated at `b^(p^E)`.  The general resultant
evaluation lemma then bounds its valuation by `primeClassPatternResultantLoss`.

## Next highest-value attack

In `StonehamPrimeClassPowerLower.lean`, prove the displayed scaled-numerator congruence in two
steps: first an exact algebraic identity rewriting `G * historyWeight_i` as the pattern
coefficient times `(p^(s_i K_i)-1)`, then compose it with
`primeClassClearedHistories_mul_phaseProduct_modEq` and downgrade to modulus `p^T`.  Apply
`primeClassDeletedPhaseProduct_modEq` and `StonehamPairsNormal.padicValInt_eval_le_resultant` at
precision above `primeClassPatternResultantLoss`.  Cancel the `p`-adic units `G`, `P`, and `b^n`,
deduce the reduced denominator divisor `p^(T-B)`, then combine lap 10's
`orbitTime_lt_prime_pow_add_maxDepth` with the existing `StonehamStateDenPowerLower` analytic
engine.  Do not revisit scheduling, complementary independence, or finiteness of the loss: those
are now kernel-proved.
