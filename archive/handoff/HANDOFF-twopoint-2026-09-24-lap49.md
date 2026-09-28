# HANDOFF twopoint — lap 49, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Green; new theorems
`#print axioms`-clean.

## Crux
Lap 48 reduced the whole `DelangeMean` axiom (regime `‖z−1‖<1`) to one uniform bound
`‖delangeE N (r v)‖ ≤ B`.  This lap **removes the coprimality-restricted sums from that
obligation entirely.**

## Landed
* `sum_inv_mul_pred` (`Σ_{2≤n≤N} 1/(n(n−1)) = 1 − 1/N`) and **`sum_inv_sq_prime_le`**
  (`Σ_{p≤N} 1/p² ≤ 1`) — elementary, new to the tree.
* `delangeSvRestr_rec` — the repo's exact restriction recursion transported to the parametrised
  variable: `S^{(p)}(M;v) = S(M;v) − (v/p)·S^{(p)}(M/p;v)`.
* **`norm_delangeE_sub_toeplitz_le`** — for any `Φ` bounding `‖S^{(p)}‖`,

      ‖ delangeE N v  −  Σ_{p≤N} (1/p)·( S(N/p; v) − S(N; v) ) ‖  ≤  ‖v‖ · Φ .

  The replacement error is exactly `Σ_p (1/p)·(v/p)·S^{(p)}(N/p²;v)`, hence `≤ ‖v‖Φ·Σ_p 1/p²`.

## The obligation, in its final shape
    ∃ B, ∀ N, ∀ r ∈ [0,1],   ‖ Σ_{p ≤ N} (1/p) · ( S(N/p; rv) − S(N; rv) ) ‖  ≤  B .
No restricted sums, no `ω`-weights, no `log`s: a **pure Toeplitz statement about `delangeSv` at
dilated scales**, with the truth `O(‖v‖)·(log N)^{Re v} = o(1)` and the requirement only `O(1)`.

Boundary conditions already in kernel:
* `p > √N`: total weight `O(1)` (`sum_inv_prime_sdiff_le`), each term `≤ 2Φ` — settled.
* absolute majorisation refuted (lap 47): `Σ_p (1/p)(A(N)−A(N/p)) ≍ (log N)^{‖v‖} → ∞`.
* `Φ` itself: supplied by `norm_delangeSv_le` (`≤ 1 + B‖v‖/(L|Re v|)`), a bootstrap that closes
  once `B` is any absolute constant, because `L → ∞` (`tendsto_delangeL_atTop`).

## Next
The Toeplitz form invites one more exact move that has not been tried: apply
`hasDerivAt_delangeSv` to `N` and to `N/p` **simultaneously**, i.e. differentiate the difference
`Dp(v) := S(N/p;v) − S(N;v)` in `v`.  Then `∂_v Dp = Σ_q (1/q)(S^{(q)}(N/(pq)) − S^{(q)}(N/q))`,
which is the *same* Toeplitz object one scale down, with initial condition `Dp(0) = 0`.  Iterating
the integrating factor on `Σ_p (1/p) Dp` therefore gives a self-map whose kernel is `Σ_{p,q}
1/(pq)`, i.e. `L²`, against a gain `1/L` per application — the arithmetic of whether the iteration
converges is the next thing to settle on paper before formalising.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 45% → **48%**.
