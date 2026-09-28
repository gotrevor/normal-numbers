# HANDOFF twopoint — lap 46, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Build green; new
theorems `#print axioms`-clean.

## Crux and the state of it
`DelangeMean` ⟶ (43) "`delangeS z N` converges" ⟶ (44) the `ω`-weighted identity ⟶ (45) the ODE
`∂_v S(N;v) = Σ_{p≤N}(1/p)S^{(p)}(N/p;v)`, `S(N;0)=1`.  **This lap closes the analytic half of
that programme.**

## Landed
* `delangeL N = Σ_{p≤N} 1/p` (`= log log N + O(1)`, real, positive) and the named error
  `delangeE N v = Σ_{p≤N}(1/p)·( S^{(p)}(N/p;v) − S(N;v) )` (`delangeE_eq_sum`).
* `hasDerivAt_delangeSv'` — the ODE in the form `∂_v S = L·S + E`.
* `hasDerivAt_integratingFactorC` / `hasDerivAt_integratingFactor` — with `c = L·ξ`,
  `d/dw [ e^{-cw} S(N; wξ) ] = e^{-cw}·ξ·E_N(wξ)`.  The `L·S` main term is gone exactly.
* `delangeSv_zero`, `integral_const_mul_exp_mul`, `continuous_delangeSv/Restr/E` — plumbing.
* **`norm_delangeSv_le`** — the payoff.  For `1 ≤ N`, `‖ξ‖ = 1`, `Re ξ < 0`, `L > 0`, and
  `‖E_N(rξ)‖ ≤ B` on `r ∈ [0,1]`:

      ‖S(N; ξ)‖  ≤  exp(L · Re ξ)  +  B / (L · |Re ξ|).

  Proof: FTC on the integrating factor, `‖e^{-cr}‖ = e^{ar}` with `a = L|Re ξ|`, and
  `∫_0^1 B e^{ar} dr = (B/a)(e^a − 1)` via its explicit antiderivative.

## What this buys
`exp(L·Re ξ) ≍ (log N)^{Re ξ} → 0`, and the error term carries the **gain `1/L = O(1/log log N)`**.
So `DelangeKernelMean` now follows from a *boundedness* hypothesis:

    sup_N sup_{r ∈ [0,1]} ‖ delangeE N (r·ξ) ‖  <  ∞ .

Every earlier formulation in this repo demanded a cancellation/`o(1)` statement.  That `E_N` is
genuinely `O(1)` and not `o(1)` is exactly why the gain matters: the primes `p ∈ (N^{1/2}, N]`
already contribute weight `O(1)` with `S^{(p)}(N/p)` evaluated at an unrelated scale.

## The one remaining obligation
`‖delangeE N v‖ ≤ B` for `‖v‖ ≤ 1`, uniformly in `N`.  Split `Σ_{p≤N}(1/p)‖S^{(p)}(N/p;v)−S(N;v)‖`:
* `p > N^{1/2}` (or any `p > N^{δ}`): weight `Σ 1/p = O(1)` by Mertens (`mertens_upper` divided by
  `log`, or the `1/p` Mertens already in the tree), and each term is `≤ 2·sup_M‖S(M;v)‖`.  So this
  piece is `O(1)` **provided `S` is bounded** — which the same theorem's conclusion supplies by a
  bootstrap on `N`, since `exp(L Re ξ) ≤ 1` always.
* `p ≤ N^{δ}`: here `S^{(p)}(N/p;v) − S(N;v)` is a sum over `n ∈ (N/p, N]` plus the multiples of
  `p`; the grading (`delangeS_grade`, nonnegative coefficients) majorises it by the corresponding
  *real* quantity at `v = ‖v‖`, i.e. by `A(N) − A(N/p) + (1/p)A(N/p)` with `A` the absolute sum.
  The first piece telescopes against `Σ_p 1/p`.

The bootstrap is the point to be careful about: it is a genuine self-improving induction, not a
circularity, because the bound gained is `B/(L|Re ξ|)` with `L → ∞`.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 30% → **38%**.  The analytic engine is machine-checked end to end; what
  remains is elementary majorisation plus a bootstrap.
