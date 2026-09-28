# HANDOFF twopoint — lap 28: `DelangeKernelTail` PROVED for `‖z−1‖ < 1`

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDelangeTail.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

## Crux this lap
The 🟡 `DelangeMean` axiom, decomposed at lap 27 into `DelangeKernelMean` + `DelangeKernelTail`.
SESSION-WRAP-3 named the tail as the highest-value 1–2-lap brick.  It closed in one.

## The advance
**`delangeKernelTail_of_norm_lt_one`** — for every `z : ℂ` with `‖z − 1‖ < 1`,
`(1/N) Σ_{n ≤ N} ‖h_z(n)‖ → 0`, **unconditionally**, no analytic input beyond Mertens.

Supporting theorems, all new and all reusable:
| lemma | content |
|---|---|
| `kataiOmega_le_omegaNat` | `ω_w(n) ≤ ω(n)` for `n ≠ 0` (the direction the Chebyshev step needs) |
| `card_small_omega_le` | `#{n ≤ N : ω(n) ≤ K}·(L/2)² ≤ 2NL` whenever `2K ≤ L(w)`, `2π(w) ≤ N` — Chebyshev on the in-kernel `turanKubilius` |
| `pow_omega_le_trunc` | `u^{ω(n)} ≤ u^{K+1} + [ω(n) ≤ K]` for `0 ≤ u ≤ 1` |
| `sum_norm_delangeKernel_le` | `Σ_{n≤N} ‖h_z(n)‖ ≤ N u^{K+1} + 8N/L(w)` |
| **`delangeMean_of_kernelMean`** | in the range `‖phase t − 1‖ < 1`, `DelangeMean t` now rests on the SINGLE residue `DelangeKernelMean` |

Argument: given `ε`, take `K` with `u^K < ε/2`, then Mertens (`tendsto_kataiPrimeRecip`) supplies
`w` with `L(w) > max(2K, 16/ε)`; the two bounds above give `≤ ε/2 + ε/2`.

## State of the 🟡 axiom
For `‖t‖_{ℝ/ℤ} < 1/6` (equivalently `‖e(t) − 1‖ < 1`) the only remaining obligation is
`DelangeKernelMean z : Σ_{n≤N} h_z(n)/n → 0` — a Wirsing/Levin–Fainleib comparison of the
truncated multiplicative sum with its Euler product, whose product side
(`prod_delangeLocal_tendsto_zero`) is already a theorem.  Outside that range the elementary route
provably fails (the tail is NOT `o(N)` when `‖z−1‖ ≥ 1`) and Halász / Selberg–Delange over
`src/PNTPort/` is required.

## Next
1. **`DelangeKernelMean` for `‖z−1‖ < 1`** (next brick).  Same truncation idea may not suffice —
   the sum `Σ h_z(n)/n` is not absolutely small, it needs the product comparison.  Likely route:
   `Σ_{n≤N} h_z(n)/n` vs `Π_{p≤N}(1 + (z−1)/p)` via the Levin–Fainleib / Wirsing inequality, i.e.
   a `log`-derivative identity `Σ_n h(n)/n · log n = Σ_{p^k} …` plus partial summation.
2. `MultiElliott` / `PairDecoupleGrowing` remain the 🔴 open leaf.  Cancellation mechanisms only.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (unchanged).
- `DelangeMean` fully discharged for `‖t‖ < 1/6` within this run: **40%** (was blocked on two
  residues, now on one).
