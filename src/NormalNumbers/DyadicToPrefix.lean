import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic means to prefix means (obligation W4 of DESIGN-2026-09-19-bcr-wiring.md)

If a bounded sequence has vanishing dyadic block means `(1/N) ∑_{N ≤ n < 2N} F n → 0`
along **all** `N → ∞` (not just powers of two), then its prefix means
`(1/n) ∑_{k < n} F k → 0`.  Route: split `[0, n)` into `[0, n/2^m)` and the dyadic
blocks `[n/2^{i+1}, n/2^i)`, `i < m`; each block is a dyadic block at scale
`N = ⌊n/2^{i+1}⌋` up to one rounding endpoint (cost `≤ ‖F‖_∞ / n` each), the head is
`≤ ‖F‖_∞ 2^{-m}`; choose `m` then `n`.  Pure analysis, elementary.
-/

open Filter Topology

namespace NormalNumbers

/-- Dyadic block mean `(1/N) ∑_{N ≤ n < 2N} F n`. -/
noncomputable def dyadicMean (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), F n) / N

/-- Prefix mean `(1/n) ∑_{k < n} F k`. -/
noncomputable def prefixMean (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, F k) / n

/-- **W4**: vanishing dyadic means at every scale give vanishing prefix means, for bounded `F`. -/
theorem prefixMean_tendsto_zero_of_dyadic (F : ℕ → ℂ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C)
    (hD : Tendsto (dyadicMean F) atTop (𝓝 0)) :
    Tendsto (prefixMean F) atTop (𝓝 0) := by
  sorry

end NormalNumbers
