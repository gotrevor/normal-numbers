/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw
import NormalNumbers.CFDensity

/-!
# W3 — Gauss-map mixing (scaffold)

Work package W3 of expedition B5′ (`KHINCHIN.md` "W3 route" — the decided
self-contained route: conditional density → transfer-operator cone →
Lévy-style ratio contraction).  This is the core of the expedition: the
statements below are the *only* correlation input the downstream W4
Chebyshev assembly consumes.  Stated here and left `sorry` for the campaign.

Statement plan (provenance in each docstring):
* `measurePreserving_gaussMap` — `γ` is `gaussMap`-invariant (plants the
  Track B B1 flag; branch change-of-variables).
* `volume_inter_preimage_eq_integral` — the exact conditional-density
  identity: given `x ∈ I_w`, the distribution of `T^{|w|} x` has density
  `tailDensity t` with `t = qₙ₋₁/qₙ` (route step 1).
* `cylinder_mixing` — **the workhorse** (route step 2, Lévy 1929 geometric
  rate): the conditional distribution of `T^{|w|+k} x` given `I_w`
  converges to `γ` with multiplicative error `C·ρᵏ`, uniformly in `w`.
  Quantitative Gauss–Kuzmin–Lévy, cylinder-conditioned.
* `gauss_kuzmin` — the unconditioned corollary from uniform start
  (`h₀ = 1` is in the cone): Gauss's 1812 problem, quantitative form —
  plants the Track B B4 flag.

⚠️ Escape valve (JUDGE.md governs): if the geometric envelope resists and
only Kuzmin's `e^{-c√k}` rate materializes, do NOT grind — STOP on
`cylinder_mixing`, write the evidence into HANDOFF, and the judge weakens
the frozen rate to a summable-error form (which downstream W4 also
accepts).  A lap does not reshape the statement itself.

Hand-checked anchors (frozen with the statements): `h₀ ≡ 1` (uniform start
is in the cone); the density window endpoints `h₁(0) = 2`, `h₁(1) = 1/2`
are attained; the direction anchor `t([2]) = K()/K(2) = 1/2` (it is
`dropLast` over the word, never the reverse).
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Anchors (kernel-checked) -/

example : tailDensity 0 (1 / 3 : ℝ) = 1 := by norm_num [tailDensity]
example : tailDensity 1 (0 : ℝ) = 2 := by norm_num [tailDensity]
example : tailDensity 1 (1 : ℝ) = 1 / 2 := by norm_num [tailDensity]
example : ((cfK (([2] : List ℕ).dropLast) : ℝ)) / (cfK [2] : ℝ) = 1 / 2 := by
  norm_num [cfK]

/-! ## Invariance (Track B flag B1) -/

/-- The Gauss measure is `gaussMap`-invariant (Gauss, 1812 letter to
Laplace).  Change of variables over the inverse branches `y ↦ 1/(k+y)`:
`Σₖ g(1/(k+y))/(k+y)² = g(y)` for the density `g(y) = 1/((1+y) log 2)`.
The junk set `{x ∈ (0,1) : gaussMap x = 0} = {1/k} ∪ {0}` is countable,
hence `γ`-null. -/
theorem measurePreserving_gaussMap :
    MeasurePreserving gaussMap gaussMeasure gaussMeasure := by
  sorry

/-! ## The conditional density identity (route step 1) -/

/-- **Conditional density of the tail** (route step 1): for a genuine
cylinder `I_w` and measurable `A ⊆ (0,1)`,
`|I_w ∩ T^{-|w|}(A)| = (∫_A h_t)·|I_w|` where `t = K(w⁻)/K(w) = qₙ₋₁/qₙ`
and `h_t = tailDensity t`.  Two lines on paper from the `cylMap` LFT
algebra: `cylMap w` carries `Leb` on `(0,1)` to `Leb` on `I_w` with
Jacobian `1/(qₙ + qₙ₋₁y)²`, and `h_t(y) = qₙ(qₙ+qₙ₋₁)/(qₙ+qₙ₋₁y)²`
normalized by `|I_w| = 1/(qₙ(qₙ+qₙ₋₁))`.  Sanity: `∫₀¹ h_t = 1`, so
`A = (0,1)` recovers `volume_cfCylinder` up to null junk. -/
theorem volume_inter_preimage_eq_integral (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (A : Set ℝ) (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    volume (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' A) =
      ENNReal.ofReal
          (∫ y in A, tailDensity ((cfK w.dropLast : ℝ) / (cfK w : ℝ)) y) *
        volume (cfCylinder w) := by
  have h := volume_inter_preimage_aux w hpos A hA hA1
  rwa [tParam, if_neg hw] at h

/-! ## Mixing (route step 2 — the core) -/

/-- **Cylinder-conditioned quantitative Gauss–Kuzmin–Lévy** (the W3
workhorse; Lévy 1929 via the ratio-oscillation/cone argument on
`tailDensity` mixtures — `KHINCHIN.md` "W3 route" step 2): there are
`C > 0` and `ρ ∈ (0,1)` such that for EVERY genuine cylinder `I_w` and
every `k`, the conditional distribution of `T^{|w|+k} x` given `x ∈ I_w`
matches `γ` to within the multiplicative envelope `1 ± C·ρᵏ`:
`(1−Cρᵏ)·γ(A)·|I_w| ≤ |I_w ∩ T^{-(|w|+k)}(A)| ≤ (1+Cρᵏ)·γ(A)·|I_w|`.
Uniformity in `w` is the point — applied at a tower of base words it
yields every covariance bound the W4 Chebyshev assembly needs (B–Y
Lemma 6's role, per-stage bad measure `< ¼`).  The lower bound is vacuous
until `Cρᵏ < 1`; that is intended. -/
theorem cylinder_mixing :
    ∃ C ρ : ℝ, 0 < C ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) →
        ∀ (k : ℕ) (A : Set ℝ), MeasurableSet A → A ⊆ Set.Ioo (0 : ℝ) 1 →
          ENNReal.ofReal (1 - C * ρ ^ k) *
              (gaussMeasure A * volume (cfCylinder w)) ≤
              volume (cfCylinder w ∩ (gaussMap^[w.length + k]) ⁻¹' A) ∧
            volume (cfCylinder w ∩ (gaussMap^[w.length + k]) ⁻¹' A) ≤
              ENNReal.ofReal (1 + C * ρ ^ k) *
                (gaussMeasure A * volume (cfCylinder w)) := by
  sorry

/-- **Quantitative Gauss–Kuzmin from uniform start** (Track B flag B4;
Gauss 1812 / Kuzmin 1928 / Lévy 1929): the uniform density is `h₀ = 1`,
a point of the cone, so the same contraction gives
`(1−Cρᵏ)·γ(A) ≤ |{x ∈ (0,1) : Tᵏx ∈ A}| ≤ (1+Cρᵏ)·γ(A)`.
With `A = (1/(a+1), 1/a)` this is the classical digit law
`P(aₖ₊₁ = a) → log₂(1 + 1/(a(a+2)))`. -/
theorem gauss_kuzmin :
    ∃ C ρ : ℝ, 0 < C ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (k : ℕ) (A : Set ℝ), MeasurableSet A → A ⊆ Set.Ioo (0 : ℝ) 1 →
        ENNReal.ofReal (1 - C * ρ ^ k) * gaussMeasure A ≤
            volume (Set.Ioo (0 : ℝ) 1 ∩ (gaussMap^[k]) ⁻¹' A) ∧
          volume (Set.Ioo (0 : ℝ) 1 ∩ (gaussMap^[k]) ⁻¹' A) ≤
            ENNReal.ofReal (1 + C * ρ ^ k) * gaussMeasure A := by
  sorry

end NormalNumbers
