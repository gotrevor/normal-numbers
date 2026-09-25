# HANDOFF twopoint — lap 41: Mertens' first theorem, BOTH halves, sharp

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointMertensLower.lean` (sorry-free,
trust-triple).

## The advance
**`mertens_upper`** — for `N ≥ 1`, `Σ_{p≤N} (log p)/p ≤ log N + log 4`.

Together with lap 40's `mertens_lower` the tree now has the two-sided sharp statement

    log N − 9  ≤  Σ_{p ≤ N} (log p)/p  ≤  log N + log 4 ,

with explicit absolute constants, proved entirely elementarily.  The repo's pre-existing
`mertens_crude` has constant `4` on the main term and is useless for normalising a Toeplitz
average; `mertens_upper` has constant `1`, which is what part II of the complex Wirsing step needs.

Mechanism: the same `log(N!)` double count run the other way.  `log(N!) ≤ N log N` trivially; from
below, keep only the `k = 1` Legendre term (`v_p(N!) ≥ ⌊N/p⌋`, via `Finset.single_le_sum` on
`Nat.factorization_factorial`), use `⌊N/p⌋ ≥ N/p − 1`, and pay the Chebyshev bound
`θ(N) ≤ N log 4` (`PrimeModel.Radical.theta_le`, already in the tree).

## Part II now reduces to bounded interchanges
With both halves in hand, the weights `w_p = (log p/p)/log N` over `p ≤ N` sum to `1 + O(1/log N)`,
so they form a regular summability method concentrated on large `p`.  The remaining steps, all
bounded-sequence arguments with no new analytic content:

1. `|S^{(p)}(M) − S(M)| ≤ (u/p)·B'` where `B' = B/(1−u/2)` and `B = sup‖S‖` (finite, since `S`
   converges) — immediate from `delangeSrestr_rec` (lap 34);
2. hence `Σ_{p≤N}(log p/p)|S^{(p)}(N/p) − S(N/p)| ≤ u B' Σ_p (log p)/p² = O(1)`, which vanishes
   after dividing by `log N`.  **The convergence of `Σ_p (log p)/p²` is `sum_log_div_mul_pred_le`
   (lap 39) again** — `1/p² ≤ 1/(p(p−1))`;
3. so it suffices that `Σ_{p≤N}(log p/p)·S(N/p)/log N → L`, a Toeplitz statement in the
   two-sided Mertens weights;
4. conclude `T(N)/log N → (z−1)L`; with lap 37's `T(N)/log N → 0` this forces **`L = 0`**.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 `ecfc5b6` · 38 `60f455a` · 39 `f0dd52e` ·
40 `58c4860` · 41 (this).

C1 itself: measured and pinned (lap 31 equivalence, lap 32 invariance) — the kickoff criterion.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Part II completable in 1–2 laps: **70%** (every input is now a theorem; only interchanges left).
- Full `DelangeKernelMean` in this run: **15%**.
