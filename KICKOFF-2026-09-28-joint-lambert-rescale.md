# KICKOFF — Joint Lambert without AGP: rescale the search

Date: 2026-09-28. Operator authorization: Trevor's "continue", following his authorization to
pursue the unconditional synchronized-word claim.
Baseline: `20d5f75`. Scope: Joint Lambert only. Vandehey runs separately in `~/src/normal-numbers`.

## Target, frozen

In namespace `NormalNumbers.JointLambert`, new file `src/NormalNumbers/JointLambertUnconditional.lean`:

* `theorem jointLambertDisjunctivity_unconditional : JointLambertDisjunctivity`
* `theorem jointWords_two_four_unconditional : JointWords ({2,4} : Finset ℕ)`

NO hypotheses. Same `JointWords` and `JointLambertDisjunctivity` from baseline. Preserve every
pre-existing `JointLambert*.lean` byte-for-byte. Add modules instead. This is the qualitative
arbitrarily-late common-position statement, not normality and not the paper's quantitative count.

## Why this route is different

The AGP gap map identifies obstacles to the *specific strong* AGP statement, but does not
establish that AGP is necessary for our qualitative consumer. Two avoidable demands created the
detour:

1. The CRT modulus need not be a fixed power of the prime search endpoint `X`. Increase `X` as a
   function of the killed-window height `k`.
2. The excluded prime need not exceed `log X`. `exists_prime_allocation` already avoids any finite
   set of non-unit moduli. For one excluded prime `P`, remove `P` from the pool when present,
   costing at most one prime. `P = 1` means no exclusion, coprimality automatic.

Use the ALREADY PROVED `exists_pointwise_exponential_distribution` (`JointLambertAGPRange.lean`).
Do NOT use `exceptionalModulus_gt_log` or `agpExpRange_holds` (both unproved), and do not spend
this run proving them or full AGP.

## Schedule

Fix `c,a,r` from the encoder before selecting `k`. `L = 2^k`. Existing arithmetic gives
`log₂ B ≤ k⁴`, `log₂ Q ≤ k⁴`. Choose `U = 2^(k¹²)`, `X = U⁴ = 2^(4k¹²)`, `H = U³`, `Z = U⁶`.
The exponent 12 is `(k³)⁴`, so `count_lower_bound` is reused with parameter `k³`.

A. Get `P = P(X)` first, THEN allocate `q, p_jt` with `Dset = ∅` if `P = 1`, `{P}` otherwise.
B. `B ≤ 2^(k⁴) ≪ X^(1/3)`, so `exists_pointwise_exponential_distribution` applies. Its relative
   error budget is `C · 2^(k⁴) · (4k¹² log 2) · exp(−η √(log 2) k⁶) → 0`; eventually `≤ 2/5`, so
   with `π(X) ≥ (9/10) X/log X` we get `π(X;B,u) ≥ X/(2 φ(B) log X)`.
C. Port the candidate injection/count for `M/(16 k¹²)` candidates, `M = X/B + 1`.
D. Tail: `B,Q ≤ U`; `H ≤ M`; `n_m + j ≤ Z = H²`. Near tail averages to `O(k²⁴/2^k) → 0`; far tail
   `≤ 4·2^(6k¹²)/2^(2^k) → 0`. These two are the feasibility test.
E. Unconditional analogue of `exists_joint_small_tail` with EXACT same conclusion and quantifier
   order, then all-bases via `base_tail_le_half_binary_tail`.
F. Reuse `evenEncoding` and `floor_digit_of_common_offset`, mirroring `jointWords_of_inputs`.

## Execution

At most THREE laps, independent worktree. Challenge the argument first; a concrete obstruction is
progress. New modules `JointLambertRescaledPrimes`, `JointLambertRescaledTail`,
`JointLambertUnconditional`. Keep permanent exact-type controls for both final declarations and the
`P=1` / `P` outside pool / `P` inside pool cases. Audit transitive axioms at the settled batch, full
build, frozen-file diff against `20d5f75`, commit green. Document in
`docs/JOINT-LAMBERT-RESCALED-PROOF.md`; append a correction to the AGP gap doc. No novelty claims.
