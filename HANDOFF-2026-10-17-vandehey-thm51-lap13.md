# Vandehey Theorem 5.1 lap 13: shifted coefficients reduced exactly

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovReduction` and imported it from
  `VandeheyProof.lean`, without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Proved `int_gcd_mul_natCast_eq_of_isCoprime`: multiplying the shifted natural factor by the
  original coefficient `a`, coprime to `m`, does not change its gcd with `m`.
- Proved `phase_reduce_of_isCoprime` and its rewrite-friendly form
  `phase_reduce_of_gcd_eq`: cancellation by the exact gcd preserves the finite Fourier phase and
  leaves an `IsCoprime` reduced numerator/denominator pair.
- Proved the production specialization `shifted_phase_reduce`.  It consumes Claim 4.5 directly
  and identifies the exact denominator of the `i`-th correlation as
  `m / (mbar * gcd i (m / mbar))`, while simultaneously supplying the coprimality hypothesis
  required by the assumed exponential-sum estimate in Proposition 4.1.
- The scoped file still has exactly its single headline `sorry`; this lap discharges the
  reduced-coefficient step named by lap 12 and does not claim campaign completion.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovReduction.lean`: passed.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovReduction
  NormalNumbers.VandeheyProof`: `Build completed successfully (8933 jobs)` before the final
  specialization; the final reduction module was rebuilt successfully (`8885 jobs`).
- A temporary axiom-check file printed exactly `[propext, Classical.choice, Quot.sound]` for
  `int_gcd_mul_natCast_eq_of_isCoprime`, `phase_reduce_of_isCoprime`,
  `phase_reduce_of_gcd_eq`, and `shifted_phase_reduce`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.shifted_phase_reduce`: axiom list
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- Commit pre-hook `lake build`: `Build completed successfully (10865 jobs)`.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovReduction.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.

## Current blocker

Proposition 4.1 is not yet assembled.  The reduced phase can now be bounded by the inductive
exponential-sum hypothesis at its exact denominator.  Those bounds must be grouped by
`d = gcd(i, m/mbar)`, estimated with `gcd_Ico_count_le_two_pow`, and collapsed with the two
`sum_divisors_rpow_*` lemmas.  The resulting squared estimate then needs the rounded-divisor
bounds and square-root/exponent algebra.

## Next highest-value attack

State and prove one correlation-aggregation lemma parameterized by the assumed bound
`A q^alpha L^gamma + B q^(-delta) L^nu (1 + log q)^r`.  Use
`shifted_phase_reduce` termwise, partition the `i` range over divisors of `m/mbar`, apply
`gcd_Ico_count_le_two_pow`, and use `sum_divisors_rpow_le_cP_mul` plus
`sum_divisors_rpow_neg_le_cP` to obtain the three-term estimate on page 13.  Keep the later
rounded-divisor substitution and square-root optimization in a separate lemma.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
