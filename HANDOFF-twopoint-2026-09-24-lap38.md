# HANDOFF twopoint — lap 38: the two elementary halves of Mertens' lower bound

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointMertensLower.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

## Crux
Part II of the complex Wirsing step (lap 37) needs `Σ_{p≤N} (log p)/p ≥ log N − C`, the LOWER half
of Mertens' first theorem.  The repo had only `mertens_crude` (the upper bound `≤ 4 log N`).

## The advance
The classical proof counts `log(N!)` two ways.  Both elementary inputs are now theorems:

| result | content |
|---|---|
| **`log_factorial_ge`** | `N log N − N ≤ Σ_{n=1}^{N} log n`, proved **discretely** |
| **`sum_div_pow_le`** | `Σ_{k=1}^{K} ⌊N/p^k⌋ ≤ N/(p−1)` for `p ≥ 2`, with the exact geometric partial sum `Σ_{k=1}^{M} p^{-k} = (1 − p^{-M})/(p−1)` proved inside |

`log_factorial_ge` needs no integrals: the increment of `n ↦ n log n − n` is at most `log n`
precisely because `(n−1)·log(n/(n−1)) ≤ 1`, which is the same `log(m+1) − log m ≤ 1/m` bound the
Abel step (lap 37) already uses.  Nice economy — one inequality serves both the Toeplitz average
and Stirling's lower bound.

## The remaining brick for Mertens
Legendre's formula `log(N!) = Σ_{p≤N} (Σ_{k≥1} ⌊N/p^k⌋)·log p` (mathlib:
`Nat.Prime.factorization_factorial`), then

    N log N − N  ≤  log(N!)  ≤  Σ_{p≤N} (N/(p−1))·log p
                            =  N·Σ_{p≤N} (log p)/p  +  N·Σ_{p≤N} (log p)/(p(p−1)) ,

and the last sum is bounded by an absolute constant (`log n ≤ 2√n` gives `≤ 4Σ n^{-3/2} ≤ 12`).
Dividing by `N` yields `Σ_{p≤N}(log p)/p ≥ log N − 1 − C`.  Two named sub-bricks: the Legendre
assembly and the convergent constant.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 `ecfc5b6` · 38 (this).

The C1 crux itself is measured and pinned (lap 31 equivalence, lap 32 invariance); this thread is
the dischargeable `DelangeMean` debt.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Mertens lower bound closable in 2 laps: **60%**.
- Full `DelangeKernelMean` in this run: **15%**.
