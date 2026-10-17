# Vandehey Theorem 5.1 lap 16: squared differencing step assembled

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovStep` and imported it from
  `VandeheyProof.lean`, without changing `VandeheyThm51` or any consumer statement.
- Proved `norm_power_sum_sq_le_aggregated`.  This is the first complete assembly of the two
  large halves of Proposition 4.1: Lemma 3.1's squared differencing inequality is combined
  with `shifted_correlation_sum_le`, and the assumed two-term estimate at every reduced
  modulus is promoted to the common ambient factors
  `N^γ (1 + log m)^r` and `N^ν (1 + log m)^r` by `two_term_bound_mono`.
- Proved `rounded_step_data`, packaging every arithmetic input for the remaining
  normalization in one theorem: `m' | m`, equal prime support, preservation of `4`, both
  sides of equations (12)--(13), and Claim 4.6's `mbar ≤ M(P)m'`.
- The resulting interface is exactly the display on pp. 12--13 before the paper substitutes
  Claim 4.6 and the rounded-divisor bounds.  The scoped file still has exactly its one
  headline `sorry`; this lap advances Proposition 4.1 and does not claim completion.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovStep.lean`: passed.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.norm_power_sum_sq_le_aggregated`: target build
  completed successfully (8936 jobs); axiom list `[Classical.choice, Quot.sound, propext]`;
  final verdict `FORMALIZE-TIER GREEN`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyKorobovStep
  --axioms NormalNumbers.VandeheyKorobov.rounded_step_data`: target build completed
  successfully (8888 jobs); axiom list `[Classical.choice, Quot.sound, propext]`; final
  verdict `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `git diff 0807f767 -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean`: empty;
  the frozen statement remains unchanged.
- `rg -n '\bsorry\b|\badmit\b|^axiom '` over `VandeheyProof.lean` and the new step module:
  exactly `VandeheyProof.lean`'s headline `sorry`.

## Current blocker

Proposition 4.1 still needs its final real-exponent normalization.  Starting from
`norm_power_sum_sq_le_aggregated`, substitute `rounded_step_data`, the order estimate
`m ≤ M(P) * ord(b,mbar)` (with Claim 4.4 identifying that order with `τ`), and the
nontrivial-branch hypothesis `m' ≤ 2QN`.  The four aggregate pieces must then be collected
into the paper's three squared terms.  After taking square roots, the trivial branches
`N^(1+γ-ν) ≥ m` and `m' > 2QN` remain, followed by the Theorem 5.1 induction.

## Next highest-value attack

Prove a real-algebra normalization lemma from the aggregate right-hand side to

`(2^(s+1) B C[P,δ] + 1) m' N^ν L
 + (2 A M C[P,1+α] + 2^(s+2) A Q C[P,α]) (m/m')^α N^(1+γ) L
 + 2 B M C[P,1-δ] (m/m')^(-δ) N^(1+ν) L`,

where `L = (1 + log m)^r`.  Keep the power/division identities in a separate lemma and
feed it the inequalities from `rounded_step_data`; this avoids re-opening the analytic
correlation proof.  Then substitute the defining `x` and close the nontrivial branch of
Proposition 4.1.

The pre-existing untracked `TestVand.lean` was inspected but left unchanged.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
