# Vandehey Theorem 5.1 lap 14: gcd-class aggregation proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovAggregation` and imported it from
  `VandeheyProof.lean`, without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Proved `sum_Ico_by_gcd`, the exact partition of the shift interval by the divisor-valued map
  `i ↦ gcd(i,n)`.
- Proved `sum_Ico_gcd_weight_le`, which sums Vandehey's Lemma 4.3 against an arbitrary
  nonnegative gcd-class weight. This is the correlation aggregation step on pp. 12--13 of the
  proof of Proposition 4.1.
- Proved `sum_Ico_gcd_weight_le_split`, replacing the totient main term by `n/d` and separating
  the result into the two divisor sums consumed by Lemma 4.2. Under the divisor involution these
  are exactly the paper's `d^(1+α)` / `d^(1-δ)` main sums and `d^α` / `d^(-δ)` error sums.
- The scoped file still has exactly its single headline `sorry`; this lap closes the combinatorial
  grouping step named by lap 13 and does not claim campaign completion.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovAggregation.lean`: passed.
- `git diff --check`: passed.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.sum_Ico_gcd_weight_le_split`: target build completed
  successfully (8934 jobs); axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

Proposition 4.1 is not yet assembled. The finite correlations can now be reduced termwise by
`shifted_phase_reduce` and aggregated with `sum_Ico_gcd_weight_le_split`. The remaining page-13
calculation must instantiate its weight with the assumed exponential-sum estimate, apply
`sum_divisors_rpow_le_cP_mul` and `sum_divisors_rpow_neg_le_cP`, and then combine this bound with
`norm_power_sum_range_sq_le_differencing`. After that come the rounded-divisor substitution and
square-root/exponent algebra.

## Next highest-value attack

Prove a specialized `correlation_sum_le` theorem in the aggregation module. Parameterize it by
the assumed bound
`A q^α L^γ + B q^(-δ) L^ν (1 + log q)^r`; use `shifted_phase_reduce` to obtain that bound for
each correlation, use `sum_Ico_gcd_weight_le_split`, and discharge its four divisor sums with
the two Lemma 4.2 theorems (using the divisor involution `d ↦ n/d`). Keep the subsequent
rounded-divisor optimization in a separate module/lemma.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
