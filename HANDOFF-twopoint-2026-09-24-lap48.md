# HANDOFF twopoint — lap 48, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Green; new theorems
`#print axioms`-clean.

## THE REDUCTION IS NOW MACHINE-CHECKED END TO END

    delangeKernelMean_of_errorBounded :
      Re z < 1  →  0 ≤ B  →  (∀ N, ∀ r ∈ [0,1], ‖delangeE N (r·(z−1))‖ ≤ B)
        →  DelangeKernelMean z

That is the entire remaining content of the 🟡 `DelangeMean` axiom in the regime `‖z−1‖ < 1`
(`delangeKernelTail_of_norm_lt_one`, lap 28, supplies the other residue).  **One hypothesis, no
`sorry`, no side conditions beyond `Re z < 1`.**

## Landed this lap
* `norm_delangeSv_le` generalised off the unit sphere: for any `ξ` with `Re ξ < 0`,
  `‖S(N;ξ)‖ ≤ exp(L·Re ξ) + B‖ξ‖/(L·|Re ξ|)` — so it applies directly at `ξ = z−1`,
  `‖z−1‖ < 1`, with no rescaling.
* **`tendsto_delangeL_atTop`** — `Σ_{p≤N} 1/p → ∞` (Mertens' second theorem), from mathlib's
  `not_summable_one_div_on_primes` plus `not_summable_iff_tendsto_nat_atTop_of_nonneg`.  Without
  this the lap-46 bound is vacuous; it is also new to the tree in this form.
* `tendsto_delangeSv_of_errorBounded`, `delangeKernelMean_of_errorBounded` — the squeeze and the
  transfer to the repo's named residue.

## The single remaining obligation
    ∃ B, ∀ N, ∀ r ∈ [0,1],   ‖ Σ_{p≤N} (1/p)·( S^{(p)}(N/p; r v) − S(N; r v) ) ‖ ≤ B .
Known (lap 47): the primes `p > √N` contribute `≤ 4·sup‖S‖` with an absolute constant, and the
absolute-majorant route to the small primes is refuted (it gives `(log N)^{‖v‖}`).  The true size
of the small-prime half is `O(‖v‖)·(log N)^{Re v} = o(1)`, so the target `O(1)` has a wide margin —
it is not a sharp estimate.

## What changed qualitatively over laps 43–48
| | before | now |
|---|---|---|
| shape of the obligation | a limit (`S` converges) | a **uniform bound** on one explicit sum |
| what must cancel | `S` itself, to `0` | nothing must go to `0`; `O(1)` suffices |
| margin | none (sharp) | the truth is `o(1)`, the requirement `O(1)` |
| analytic input | Wirsing's theorem | none beyond Mertens, all in kernel |

## Next
1. Bound the small-prime half.  The remaining honest handle is the *pair* of exact recursions
   `delangeSrestr_rec` (removes the coprimality at cost `1/p`) and `S(N)−S(M) = Σ_{M<n≤N} h/n`,
   used together so that the `Σ_p (1/p)·(A(N)−A(N/p))` divergence is never formed.
2. Failing that, the next reduction to try is replacing `S(N)` in `delangeE` by `S(N/p)` —
   i.e. comparing `S^{(p)}(N/p)` with `S(N/p)` (a *one-step* recursion, exactly `(v/p)S^{(p)}(N/p²)`,
   absolutely `O(1/p²)`) and pushing the whole scale discrepancy into `Σ_p (1/p)(S(N/p) − S(N))`.
   That reshapes the obligation into a pure Toeplitz statement about `S` and may be attackable by
   the same integrating factor applied to the difference.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 38% → **45%**.  Everything except one uniform `O(1)` bound is now kernel-checked.
