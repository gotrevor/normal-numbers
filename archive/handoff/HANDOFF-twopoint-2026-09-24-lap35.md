# HANDOFF twopoint — lap 35: the Wirsing recursion, with zero analytic input

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointDelangeLF.lean` (sorry-free,
trust-triple).

## Crux
`DelangeKernelMean z : Σ_{n≤N} h_z(n)/n → 0` — the last dischargeable residue of the 🟡
`DelangeMean` axiom.

## The advance
The Levin–Fainleib inequality of lap 34 bounds the `log`-weighted sum `T(N)`, not `S(N)`.  Abel
summation converts one to the other.  The textbook form is
`Σ_{n≤N}(h(n)/n)log(N/n) = ∫_1^N S(t)dt/t`; here it is proved **purely discretely**, by induction,
so no integration theory enters:

| result | content |
|---|---|
| `delangeAbel z N` | `Σ_{1≤m<N} (log(m+1) − log m)·S(m)` |
| **`delangeS_mul_log`** | `S(N)·log N = T(N) + Abel(N)` — EXACT, every `N`, by induction |
| `log_succ_sub_log_le`, `log_succ_sub_log_nonneg` | `0 ≤ log(m+1) − log m ≤ 1/m` |
| `norm_delangeAbel_le` | `‖Abel(N)‖ ≤ Σ_{1≤m<N} ‖S(m)‖/m` |
| **`norm_delangeS_mul_log_le`** | **THE RECURSION** (below) |

    ‖S(N)‖·log N  ≤  u·Σ_{p≤N} (log p/p)·(‖S(N/p)‖ + (u/p)·A(N/p))  +  Σ_{1≤m<N} ‖S(m)‖/m

with `u = ‖z−1‖`.  **Both right-hand terms involve `S` only at arguments `< N`**, so this is a
genuine strong induction on `N`, and **no analytic input has been used anywhere to reach it** —
every step from `sum_delangeKernel_divisors` (lap 27) through here is an identity or a triangle
inequality.  That is the whole arithmetic half of Wirsing's theorem, machine-checked.

## What is left
1. **Mertens**: `Σ_{p≤N} log p/p ≤ log N + C`.  This is the ONLY external analytic input the
   endgame needs.  `src/PNTPort/` has quantitative PNT; mathlib has
   `Nat.Prime.sum_log_div_le`-type bounds — check `Mathlib.NumberTheory.Mertens*` first.
2. **The size of `A(N)`**: need `A(N) ≪ (log N)^u`, i.e. the absolute companion.  Elementary
   (Mertens again, `Π_{p≤N}(1+u/p)`).
3. **The contraction**: with `u < 1`, feed `‖S(m)‖ ≤ B(log m)^{θ}` into the recursion and check
   `θ = u − 1 + ε` is a fixed point.  The `Σ_{m<N}‖S(m)‖/m` term contributes `B(log N)^{θ+1}/(θ+1)`
   and the prime term `u·B(log N)^{θ+1}·(…)`; the induction closes when `1/(θ+1) + u/(θ+1) < 1`,
   i.e. `θ > u`.  **Careful**: that gives `‖S(N)‖ ≪ (log N)^{u}`, which is NOT `o(1)`.  The
   `o(1)` needs the *complex* cancellation (`Re z < 1`), i.e. the argument must be run on `S`
   itself rather than `‖S‖` — the standard Halász/Wirsing step.  Record this before the next lap
   spends effort on a real-valued induction that provably cannot reach `o(1)`.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 (this).

C1 itself is measured and pinned (lap 31 equivalence, lap 32 invariance).

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- `DelangeKernelMean` for `‖z−1‖<1` closable in 3–6 laps: **30%** (revised down: the real-valued
  Gronwall provably stops at `(log N)^u`, so the endgame needs the complex step).
