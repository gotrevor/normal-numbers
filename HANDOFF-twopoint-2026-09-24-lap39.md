# HANDOFF twopoint — lap 39: the convergent correction, bounded absolutely

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointMertensLower.lean` (sorry-free,
trust-triple).

## Crux
Mertens' lower bound `Σ_{p≤N}(log p)/p ≥ log N − C`, the last analytic input to part II of the
complex Wirsing step (lap 37).  Splitting `1/(p−1) = 1/p + 1/(p(p−1))`, the `log(N!)` double count
leaves a correction sum that must be bounded by an absolute constant.

## The advance
| result | content |
|---|---|
| `log_le_two_sqrt` | `log x ≤ 2√x` (apply `log y ≤ y − 1` to `y = √x`) |
| **`inv_rpow_le_telescope`** | `4/n^{3/2} ≤ 8(1/√(n−1) − 1/√n)` for `n ≥ 2` — the sharp telescoping comparison, proved by `nlinarith` on `a=√n`, `b=√(n−1)` with `a²−b²=1` |
| `sum_inv_sqrt_telescope` | `Σ_{n=2}^{N}(1/√(n−1) − 1/√n) = 1 − 1/√N` |
| **`sum_log_div_mul_pred_le`** | **`Σ_{n=2}^{N} (log n)/(n(n−1)) ≤ 8`, for every `N`** |

The constant is explicit and absolute, and the whole argument is elementary: no integrals, no
convergence tests, just `log x ≤ x − 1` and two telescopings.  Since the primes are a subset of
`[2,N]` and every term is nonnegative, `Σ_{p≤N}(log p)/(p(p−1)) ≤ 8` follows immediately.

## What remains for Mertens' lower bound
Exactly one brick: **Legendre's formula assembly**.  With
`Nat.Prime.factorization_factorial` and `Nat.factorization_prod_pow_eq_self`,

    N log N − N  ≤  log(N!)                                   (`log_factorial_ge`, lap 38)
                 =  Σ_{p≤N} (Σ_{k≥1} ⌊N/p^k⌋)·log p            (Legendre)
                 ≤  Σ_{p≤N} (N/(p−1))·log p                    (`sum_div_pow_le`, lap 38)
                 =  N·Σ_{p≤N}(log p)/p + N·Σ_{p≤N}(log p)/(p(p−1))
                 ≤  N·Σ_{p≤N}(log p)/p + 8N                    (this lap)

so `Σ_{p≤N}(log p)/p ≥ log N − 9`.  Every inequality in that chain is now a theorem except the
Legendre identity itself, which is mathlib API plus `Real.log_prod`.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 `ecfc5b6` · 38 `60f455a` · 39 (this).

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Mertens lower bound closable next lap: **70%** (one brick left, and it is mathlib API).
- Full `DelangeKernelMean` in this run: **15%**.
