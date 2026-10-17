# Vandehey Theorem 5.1 lap 12 (review): Claim 4.6 corrected and proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovBigM` and imported it from
  `VandeheyProof.lean`, without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Proved `fixed_pow_factorization_eq`: for `q = 2 * ord(b, ∏ P)`, exact LTE gives
  `v_p(b^(q*m') - 1) = v_p(b^q - 1) + v_p(m')` for every `p ∈ P`.  The proof includes the
  exceptional prime `2`: `q` is even, so an odd base has `4 ∣ b^q - 1`.
- Proved `orderOf_dvd_fixedExponent_mul_modulus`:
  `ord(b,m') ∣ 2 * ord(b,∏ P) * m'`.
- Proved the exact paper claim `gcd_pow_orderOf_div_dvd_bigM`: with
  `τ = ord(b,m')` and `mbar = gcd(b^τ-1,m)`, one has `mbar / m' ∣ bigM b P`.
- Proved its consumed inequality `gcd_pow_orderOf_le_bigM_mul` and the rounded-divisor
  specializations `gcd_pow_rounded_orderOf_div_dvd_bigM` and
  `gcd_pow_rounded_orderOf_le_bigM_mul`.
- The scoped file still has exactly its single headline `sorry`; this lap completes the source
  claims preceding the Proposition 4.1 summation and does not claim campaign completion.

## Adversarial review finding

- The lap-11 handoff named the next target as `m / mbar ∣ bigM`.  Visual inspection of page 11
  of the paper confirms that Claim 4.6 is instead **`mbar / m' ∣ M`**, hence
  `mbar ≤ M*m'`.  The swapped quotient is false in general: the missing part of `m` above
  `mbar` is not bounded by the fixed `M(P)`.
- This correction does not change the campaign route.  It restores the exact estimate used a few
  lines later in Proposition 4.1, where the outer factor `m'` is replaced using
  `mbar ≤ M*m'`.
- Statement-integrity diff from kickoff commit `0807f767` shows that
  `LiteratureVandeheyDifferencing.lean` is unchanged and `VandeheyProof.lean` differs only by the
  ordered machinery imports.  The frozen theorem and three corollary statements have not drifted.
- Dependency graph: rungs 1--4 are proved.  In rung 5, Lemma 3.1, Lemmas 4.2--4.3,
  equations (12)--(13), and Claims 4.4--4.6 are now proved.  The remaining work in Proposition
  4.1 is the reduced-coefficient step, gcd-class summation, real-power algebra, and square-root
  optimization.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovBigM.lean`: passed.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovBigM
  NormalNumbers.VandeheyProof`: `Build completed successfully (8932 jobs)`.
- A temporary axiom-check file printed exactly
  `[propext, Classical.choice, Quot.sound]` for `bigM_factorization`,
  `fixed_pow_factorization_eq`, `orderOf_dvd_fixedExponent_mul_modulus`,
  `gcd_pow_orderOf_div_dvd_bigM`, `gcd_pow_orderOf_le_bigM_mul`, and both rounded
  specializations.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.gcd_pow_rounded_orderOf_div_dvd_bigM`:
  axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovBigM.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.

## Current blocker

Proposition 4.1 is not yet assembled.  After Lemma 3.1, each shifted coefficient
`a*(b^(i*τ)-1)/m` must be reduced by
`gcd(b^(i*τ)-1,m) = mbar*gcd(i,m/mbar)`, with a proof that the reduced numerator is coprime
to its exact denominator.  The assumed exponential-sum estimate must then be grouped by those
gcd classes and bounded with the proved Lemmas 4.2--4.3 before the rounded-divisor optimization.

## Next highest-value attack

First prove a reusable phase-reduction lemma for the shifted coefficient: cancellation by the
exact gcd preserves the phase and leaves an `IsCoprime` numerator/denominator pair.  Use Claim 4.5
to specialize its denominator to `m / (mbar*d)`.  Then prove the single correlation-sum estimate
obtained by grouping `i` according to `d = gcd(i,m/mbar)`, applying `gcd_Ico_count_le` and the two
`sum_divisors_rpow_*` lemmas.  That is the arithmetic core of Proposition 4.1; the remaining
rounded bounds and exponent algebra can follow as a separate lemma.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
