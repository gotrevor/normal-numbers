# HANDOFF twopoint — lap 42: part II(a), the `S^{(p)} → S` replacement costs `O(1)`

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointMertensLower.lean` (sorry-free,
trust-triple).

## The advance
The Levin–Fainleib identity carries the coprimality-restricted sums `S^{(p)}`; the Toeplitz
argument needs `S` itself.  That replacement is now proved to cost an **absolute constant**,
uniformly in `N`:

| result | content |
|---|---|
| `delangeT_eq_prime_sum` | lap 33's identity restated on the named sums: `T(N) = (z−1)Σ_{p≤N}(log p/p)·S^{(p)}(N/p)` |
| **`norm_delangeSrestr_le_two_mul`** | `‖S‖ ≤ B` ⇒ `‖S^{(p)}(M)‖ ≤ 2B`, uniformly in `p, M` — strong induction on `M` through `delangeSrestr_rec`, using `u/p ≤ 1/2` |
| **`norm_delangeT_sub_primeSum_le`** | `‖T(N) − (z−1)Σ_{p≤N}(log p/p)·S(N/p)‖ ≤ 16B`, **for every `N`** |

The constant does not grow with `N` because the per-prime error is `≍ (log p)/p²`, and
`Σ_p (log p)/p² ≤ Σ_{n≥2}(log n)/(n(n−1)) ≤ 8` — that is `sum_log_div_mul_pred_le` from lap 39
being reused verbatim.  Nice: one elementary bound serves both the Mertens double count and this
interchange.

## What part II still needs
Only the Toeplitz step itself:

    Σ_{p ≤ N} (log p/p) · S(N/p) / log N  →  L    when  S(N) → L ,

with weights normalised by the two-sided Mertens bracket
`log N − 9 ≤ Σ_{p≤N}(log p)/p ≤ log N + log 4` (laps 40–41).  The argument is the same ε-split as
`tendsto_delangeAbel_div_log` (lap 37), with one extra wrinkle: the weight mass on primes
`p ≤ P₀` is `O_{P₀}(1)` (finite sum), so it vanishes after dividing by `log N`, and on the rest
`N/p → ∞`, so `S(N/p)` is within `ε` of `L`.

Then `T(N)/log N → (z−1)L`, and lap 37's `T(N)/log N → 0` forces **`L = 0`** — i.e.
`DelangeKernelMean` becomes exactly "`S` converges".

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 `ecfc5b6` · 38 `60f455a` · 39 `f0dd52e` ·
40 `58c4860` · 41 `acae678` · 42 (this).

C1 itself: measured and pinned (lap 31 equivalence, lap 32 invariance).

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Part II completable next lap: **70%**.
- Full `DelangeKernelMean` in this run: **15%**.
