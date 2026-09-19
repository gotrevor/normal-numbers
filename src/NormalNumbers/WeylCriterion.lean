import Mathlib.Analysis.Fourier.AddCircle
import NormalNumbers.RealDefs

/-!
# Weyl's criterion (obligation W3 of DESIGN-2026-09-19-bcr-wiring.md)

If every nonzero Fourier mean of a `[0,1)`-valued sequence vanishes, the sequence
is equidistributed in the sense of `NormalNumbers.Equidistributed` (visit
frequency of every `[a, c) ⊆ [0, 1)` tends to `c − a`).

Route (one lap): fix `[a, c)`; squeeze its indicator between continuous
`1`-periodic trapezoids `g₋ ≤ 1_{[a,c)} ≤ g₊` with `∫ (g₊ − g₋) ≤ ε`; view them on
`AddCircle 1` and approximate each uniformly within `ε` by a trigonometric
polynomial using `span_fourier_closure_eq_top`
(`Mathlib/Analysis/Fourier/AddCircle.lean`); the Fourier hypothesis makes the
Cesàro mean of every nonconstant `fourier n` vanish, so the mean of a trig
polynomial tends to its constant term, which is its integral; finish with `ε/3`.
No Selberg–Delange, no number theory: this file is pure analysis.
-/

open Filter Topology

namespace NormalNumbers

/-- The `h`-th Fourier mean of the first `n` terms of `u`. -/
noncomputable def fourierMean (u : ℕ → ℝ) (h : ℤ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (u k : ℂ))) / n

/-- **Weyl's criterion**, the direction used by the normality wiring: vanishing
Fourier means at every nonzero frequency give equidistribution. -/
theorem equidistributed_of_weyl (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0)) :
    Equidistributed u := by
  sorry

end NormalNumbers
