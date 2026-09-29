# Joint Lambert disjunctivity, unconditionally: the rescaled prime search

**Date** 2026-09-29 · **Result**
`NormalNumbers.JointLambert.jointLambertDisjunctivity_unconditional` and
`jointWords_two_four_unconditional` (`src/NormalNumbers/JointLambertUnconditional.lean`),
no hypotheses, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## 1. What changed

Nothing in the mathematics of the joint-Lambert assembly. The only change is the
**schedule** of the prime search.

| | old (`JointLambertPrimeSelection`) | new (`JointLambertRescaledPrimes`) |
| --- | --- | --- |
| pool interval | `(2^k, 2^{k+1})` | same |
| CRT modulus | `B ≤ 2^{k⁴}` | same |
| search endpoint | `X = 2^{4k⁴}` | `X = 2^{4k¹²}` |
| modulus vs endpoint | `B = X^{1/4}` | `B = X^{1/12}`, and `log B = k⁴ ≪ √log X = 2k⁶√log 2` |
| analytic input | `AGP` (hypothesis) | `exists_pointwise_exponential_distribution` (**theorem**) |
| candidate density | `1/(16k⁴)` | `1/(16k¹²)` |
| excised conductor | `Dset`, `|Dset| ≤ D₀`, each `> log X` | `Dset = {P}` or `∅`, **no size condition** |

`B ≤ X^{1/4}` is exactly the range where only AGP-strength input works. `log B ≪ √log X`
is the Siegel–Walfisz range, where the installed material already lives. The consumer never
cared which: it consumes only "at least `M/(16·poly(k))` candidate indices".

## 2. The scale inequalities

Write `η, C` for the constants of `exists_pointwise_exponential_distribution`,
`s = √(log 2)`, `Λ = log X = 4k¹² log 2`, `√Λ = 2k⁶ s`.

**(a) The modulus is inside the theorem's range.** `B³ ≤ 2^{3k⁴} ≤ 2^{4k¹²} = X`, so
`B ≤ X^{1/3}`, i.e. `B ≤ powerDistributionLevel X = ⌊X^{1/3}⌋`.

**(b) The error is dominated** (`eventually_rescaled_error_small`). We need
`C·X·e^{−(η/2)√Λ} · φ(B) · Λ ≤ (2/5)·X`, i.e.

    C · 4k¹² · 2^{k⁴} · exp(−η k⁶ s)  =  4C·k¹²·exp(k⁴ log 2 − η k⁶ s)  ≤  2/5,

which holds eventually because `η s k² ≥ log 2 + 1` eventually, making the exponent
`≤ −k⁴ ≤ −k`. **On the old schedule the same computation gives the exponent
`k⁴ log 2 − η k² s → +∞`** — that divergence, and nothing else, is what forced AGP.

**(c) The count.** `π(X) ≥ (9/10) X/log X` (`Erdos446.eventually_primeCounting_tenth_bounds`),
so `π(X;B,u) ≥ π(X)/φ(B) − E ≥ (9/10 − 2/5)·X/(φ(B)Λ) = X/(2φ(B)Λ)` — AGP's own conclusion.

**(d) The tail** (`JointLambertRescaledTail`). `U = 2^{k¹²}`, `X = U⁴`, `H = U³`, `Z = U⁶`;
`B, Q ≤ 2^{k⁴} ≤ U`, so `H ≤ M = X/B + 1` and `n_m + j ≤ Z = H²`. Row bound
`sum_tau_progression_le` gives `S ≤ M(6k¹² + 4)`, and averaging over `≥ M/(16k¹²)` candidates
gives near tail `≤ (192k²⁴ + 128k¹²)/2^k → 0`; far tail `≤ 4·2^{6k¹²}/2^{2^k} → 0`. Both are
discharged by `eventually_nat_poly_le_two_pow` (degree 24 and 12), which replaces the explicit
degree-8 thresholds of `poly_eight_le_two_pow`.

## 3. The excised conductor costs at most one pool prime

`exists_pointwise_exponential_distribution` excises one conductor `P` (either `1` or prime),
chosen **before** the modulus. Three cases, all covered:

* `P = 1` — `Nat.coprime_one_right`; `Dset = ∅`, no pool prime lost.
* `P` prime, not in `(2^k, 2^{k+1})` — `exists_prime_allocation` removes nothing.
* `P` prime, in the pool — one prime removed. `D₀ = 1` in `pool_card_ge`, so
  `3k(1 + k² + 1) ≤ 2^k` still supplies the allocation.

No lower bound on `P` is used anywhere. `AGP`'s `D > log X` clause is simply not requested.

## 4. What is *not* claimed

* `AGP`, `AGPExpRange`, `exceptionalModulus_gt_log`, `agpExpRange_holds` stay open and
  untouched. This route does not prove them and does not depend on them.
* The result is the **qualitative** arbitrarily-late common-position statement
  (`JointWords` / `JointLambertDisjunctivity` as frozen in `JointLambertStatement.lean`).
  It is not normality, and not the paper's quantitative frequency count.
* No novelty or literature-priority claim is made.

## 5. Files

New: `JointLambertRescaledPrimes.lean`, `JointLambertRescaledTail.lean`,
`JointLambertUnconditional.lean`. Every pre-existing `JointLambert*.lean` is byte-for-byte
identical to `20d5f75` (`git diff --numstat 20d5f75` over them is empty); only
`src/NormalNumbers.lean` gains three imports.
