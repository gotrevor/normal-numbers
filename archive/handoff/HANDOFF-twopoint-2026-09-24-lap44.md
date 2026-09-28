# HANDOFF twopoint — lap 44, 2026-09-25

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDelangeOmega.lean` (import added
to `src/NormalNumbers.lean`).  Nothing existing edited.  Build green; both new theorems
`#print axioms`-clean.

## Crux
The 🟡 `DelangeMean` axiom.  After lap 43 it is *exactly* "`delangeS z N` converges" (Wirsing).
The `log`-weighted Levin–Fainleib engine (`TwoPointDelangeLF.lean`) cannot close it: lap 35 showed
that passing to `‖·‖` replaces the multiplier `z−1` by `u = ‖z−1‖ > 0`, and the Gronwall fixed
point is `θ ≈ u`, giving `(log N)^u → ∞`.  The *sign* `Re(z−1) < 0` — the only reason `S → 0` —
is destroyed at exactly that step.

## Advance: a second, sign-preserving engine

1. `delangeOmegaT_eq` — **the `ω`-weighted Levin–Fainleib identity**, exact for every `N`:

       Σ_{n ≤ N} ω(n)·h(n)/n  =  (z−1) · Σ_{p ≤ N} (1/p) · S^{(p)}(N/p).

   Same two moves as the classical identity (split the weight over `p ∣ n`, reindex `n = pm`),
   but with `log n` replaced by `ω(n)`: **no `log`, no Abel summation, no Mertens input**, and the
   `p`-weight is `1/p` rather than `log p/p`.  Proof is strictly shorter than the `log` case —
   `ω(n) = #{p ≤ N : p ∣ n}` holds for every `0 < n ≤ N` with no squarefree case split
   (`filter_dvd_primesLe`).

2. `delangeGrade`, `delangeS_grade` — the grading `S(N;v) = Σ_{k ≤ N} v^k a_k(N)` with
   `a_k(N) = Σ_{n≤N, μ²=1, ω=k} 1/n ≥ 0`.  So `S(N;·)` is a polynomial in `v` with **nonnegative
   real coefficients**, and `delangeOmegaT` is literally `v·∂_v S(N;v)`.

## Why this is the right handle (the mechanism, to be formalised next)

In generating-function form item 1 reads `∂_v S(N;v) = Σ_{p≤N}(1/p)·S^{(p)}(N/p;v)`.  The
multiplier `Σ_{p≤N}1/p = log log N + O(1)` is **real and positive**.  Along the ray `v = r e^{iθ}`,

    d/dr ‖S‖² = 2 Re( conj(S)·e^{iθ}·Σ_p (1/p) S^{(p)}(N/p) ) ≈ 2 (log log N) cos θ · ‖S‖²,

and `cos θ < 0` precisely when `Re(z−1) < 0`.  That is an honest exponential *decay* — the
`(log N)^{Re v}` truth — obtained without ever discarding the phase.  The grading says why the
`log`-route cannot see it: `‖S(N;v)‖` was compared with `S(N;‖v‖)`, the same polynomial on the
positive ray, where the grades cannot cancel by construction.

The residual obligation is unchanged in *content* but now sits against a phase-preserving
multiplier: control `E := Σ_p (1/p)·(S^{(p)}(N/p) − S(N))`.  Note the mass of `Σ_{p≤N}1/p` coming
from `p > N^{1/e}` is `O(1)`, so only `p ≤ N^{ε}` matter, where `N/p` is within a bounded
`log log` shift of `N`.

## Next
Two concrete bricks, in order:
1. The graded recursion `k·a_k(N) = Σ_{p≤N}(1/p)·a^{(p)}_{k−1}(N/p)` — item 1 read off coefficient
   by coefficient, elementary, and the natural induction handle for `a_k(N) ≤ L^k/k!`
   (`L = Σ_{p≤N}1/p`), which is the sharp majorant.
2. The discrete energy step: state and prove the one-step inequality for
   `‖S(N;v)‖² − ‖S(N;v')‖²` along a grid on the ray, with `E` carried as a named hypothesis.
   Then `E` is the sole remaining sorry, and it is a *comparison of `S` at nearby scales*, not a
   cancellation statement.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged; pinned as
  an equivalence, WRAP 4 part A).
- `DelangeKernelMean` (convergence of `S`): 15% → **22%**, on the strength of the new engine
  having a multiplier that keeps the sign.
