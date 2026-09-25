# HANDOFF twopoint — lap 37: the complex step, part I (Toeplitz); `S` convergent ⇒ `T = o(log N)`

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointDelangeLF.lean` (sorry-free,
trust-triple).

## The insight this lap
Lap 35 recorded that a real-valued Gronwall on `‖S‖` provably stalls at `(log N)^u`.  The way past
it is **not** a sharper inequality — it is to use the exact identity on `S` itself and read off the
*value* of the limit rather than its size:

    S(N)·log N = T(N) + Abel(N)          (exact, lap 35)
    T(N)       = (z−1)·Σ_{p≤N}(log p/p)·S^{(p)}(N/p)   (exact, lap 33/34)

If `S(N) → L`, the first line gives `T(N)/log N → 0` and the second gives `T(N)/log N → (z−1)L`.
Hence `(z−1)L = 0`, so **`L = 0` whenever `z ≠ 1`** — the value of the limit is forced, for free.
`DelangeKernelMean` therefore reduces to the bare *convergence* of `S`, with no need to identify
the limit.  That is a genuine structural simplification of the residue.

## Landed (part I — needs NO Mertens, no analytic input)
| result | content |
|---|---|
| **`sum_log_telescope`** | the Abel weights `c_m = log(m+1) − log m` sum to exactly `log N` |
| **`tendsto_delangeAbel_div_log`** | Toeplitz regularity: `S(N) → L` ⇒ `Abel(N)/log N → L` |
| **`tendsto_delangeT_div_log`** | hence `T(N)/log N → 0` |

`tendsto_delangeAbel_div_log` is the honest ε-argument: split the weighted average at the tail
index where `‖S − L‖ < ε/2`, bound the head by a constant over `log N → ∞`.  The weights are
nonnegative and exactly normalised, so no constant is lost.

## Part II — the only remaining analytic input
`Σ_{p≤N} (log p / p) = log N + O(1)` (Mertens' first theorem), plus the interchange showing
`S^{(p)}(N/p) → L/(1+(z−1)/p)` and that the weight mass concentrates on large `p`.  The repo has
`mertensSum` and the crude `mertens_crude : mertensSum N ≤ 4 log N`
(`PrimeModelRadicalMoment.lean`) — the **lower** bound `mertensSum N ≥ log N − C` is what part II
needs and is not yet in the tree.  `G4MertensAP.lean` has a `MertensRate` interface worth checking
before proving it from scratch.

After part II, `DelangeKernelMean` = "`S` converges", and the remaining task is a genuine
Tauberian/Wirsing convergence proof — which is where this residue's real difficulty lives, exactly
as the literature says.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 (this).

C1 itself: measured and pinned (lap 31 equivalence; lap 32 invariance).

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Part II (Mertens lower bound + interchange) closable in 2–3 laps: **55%**.
- Full `DelangeKernelMean` in this run: **15%** (the convergence of `S` is the real wall).
