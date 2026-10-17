# Vandehey Theorem 5.1 lap 15: sharp cutoff and correlation aggregation

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovCorrelation` and imported it from
  `VandeheyProof.lean`, without changing `VandeheyThm51` or any consumer statement.
- Proved `norm_power_sum_range_sq_le_differencing_cutoff`: the zero correlations in Lemma 3.1
  are removed exactly, leaving the shift range `Ico 1 (N ⌈/⌉ τ)`.
- Proved `natCast_ceilDiv_sub_one_le_div`, which turns that integral endpoint back into the
  paper's real cutoff `(⌈N/τ⌉ - 1) ≤ N/τ`.
- Strengthened Lemma 4.3 and both aggregation forms with the sharp main term `(X - 1)/n`:
  `gcd_Ico_count_le_sub_one`, `gcd_Ico_count_le_sub_one_two_pow`,
  `sum_Ico_gcd_weight_le_sub_one`, and `sum_Ico_gcd_weight_le_split_sub_one`.
  The earlier coarser public theorems remain available as corollaries.
- Proved `sum_Ico_gcd_two_rpow_le` and `_of_cutoff`, which perform the divisor involution and
  discharge all four sums with Lemma 4.2, producing exactly the `C_{P,1+α}`,
  `C_{P,1-δ}`, `C_{P,α}`, and `C_{P,δ}` factors on page 13.
- Proved `shifted_correlation_sum_le`: Claim 4.5's phase reduction is applied termwise, the
  reduced denominators inherit support in `P`, the sharp cutoff is used, and the complete
  pp. 12--13 correlation estimate follows.  `two_term_bound_mono` supplies the monotonicity
  step from the input estimate at `(q,L)` to common ambient `(m,N)` factors.
- The scoped file still has exactly its one headline `sorry`; this lap advances Proposition 4.1
  and does not claim campaign completion.

## Adversarial review finding

Lap 14's integral aggregation theorem used `X/n` and proposed feeding it the correlation range
directly.  That loses a full main term: the nonzero shifts satisfy `i * τ < N`, so their natural
endpoint is `X = ⌈N/τ⌉`, while the paper's Lemma 4.3 main term is based on the real cutoff
`N/τ`.  The coarser `X/n` is generally larger than `N/(τn)` and would change the frozen
constants.  The sharp count uses `(X - 1)/n`, and
`natCast_ceilDiv_sub_one_le_div` proves `(X - 1) ≤ N/τ`; this restores the published route.

The frozen statement remains unchanged from its freezing commit, and the repaired route still
feeds Proposition 4.1 and hence Theorem 5.1.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovCounting.lean`: passed.
- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovDifferencing.lean`: passed.
- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovDivisors.lean`: passed.
- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovAggregation.lean`: passed.
- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovCorrelation.lean`: passed.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.shifted_correlation_sum_le`: target build completed
  successfully (8935 jobs); axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `git diff 0807f767 -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean`: empty;
  the `VandeheyProof.lean` diff from that kickoff SHA contains imports only.
- `rg -n '\bsorry\b|\badmit\b|^axiom ' ...` over the scoped file and all touched Korobov
  modules: exactly `VandeheyProof.lean`'s headline `sorry`.

## Current blocker

Proposition 4.1 is not yet assembled.  The correlation side is now a single theorem, but it must
be inserted into the squared differencing inequality.  The resulting three groups then need the
order bound for `mbar`, `m' ∣ mbar`, Claim 4.6, the assumption `m' ≤ 2QN`, and equations
(12)--(13) to reach the exact `A'` and `B'` constants.  The proof must also handle the paper's
trivial-bound branches and the reduced-modulus `q = 1` case when deriving the correlation input
from the induction hypothesis.

## Next highest-value attack

Prove the squared Proposition 4.1 estimate under the paper's nontrivial-branch hypotheses.
Instantiate `shifted_correlation_sum_le` using `two_term_bound_mono`, combine it with
`norm_power_sum_range_sq_le_differencing_cutoff`, and normalize the result into the three terms
displayed immediately before the final square root on page 13.  Keep the rounded-divisor
substitution/exponent algebra as the next lemma; after that, discharge the trivial branches and
package Proposition 4.1 for the Theorem 5.1 induction.

The pre-existing untracked `TestVand.lean` was inspected but left unchanged.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
