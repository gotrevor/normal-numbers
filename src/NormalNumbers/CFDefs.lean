/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Continued fraction definitions (Track B / expedition B5′)

The Gauss map, CF digits of a real, continuants, finite CF values, cylinder
sets, the Gauss measure, and the one-parameter conditional-density family
`h_t(y) = (1+t)/(1+ty)²` that powers the W3 mixing argument.

Conventions:
* Digits are read through iterates of the Gauss map:
  `cfDigit x n = ⌊(gaussMap^[n] x)⁻¹⌋₊`.  Total functions; on rationals the
  orbit hits `0` and the digit reads the junk value `0`, so "genuine digit"
  is exactly "digit ≥ 1" — lemmas carry `∀ a ∈ w, 1 ≤ a` hypotheses.
* `cfK` is the continuant `K(a₁,…,aₙ)`: for `x = [0; a₁, a₂, …]` the `n`-th
  convergent is `pₙ/qₙ` with `qₙ = cfK (a₁…aₙ)` and `pₙ = cfK (a₂…aₙ)`.
* Provenance: Becher–Yuhjtman, *On absolutely normal and continued fraction
  normal numbers*, IMRN 2019 (arXiv:1704.03622), §1.1 — see
  `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` and `KHINCHIN.md`.
-/

namespace NormalNumbers

open MeasureTheory

/-- The Gauss map `x ↦ 1/x mod 1` on `(0,1)`, sending `0` to `0`.
Junk values outside `[0,1)`. -/
noncomputable def gaussMap (x : ℝ) : ℝ :=
  if x = 0 then 0 else Int.fract x⁻¹

/-- The `n`-th CF partial quotient (0-indexed) of `x ∈ (0,1)`:
`aₙ₊₁ = ⌊1/(Tⁿx)⌋`.  Junk value `0` when the orbit hits `0` (rationals) or
leaves `(0,1)`; a genuine digit is always `≥ 1`. -/
noncomputable def cfDigit (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(gaussMap^[n] x)⁻¹⌋₊

/-- The continuant `K(a₁,…,aₙ)`: `K() = 1`, `K(a) = a`,
`K(a,b,…) = a·K(b,…) + K(…)`.  For `x = [0; a₁, a₂, …]` the convergent
denominators are `qₙ = cfK [a₁,…,aₙ]`. -/
def cfK : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | a :: b :: l => a * cfK (b :: l) + cfK l

/-- Convergent numerator: `pₙ = K(a₂,…,aₙ)`. -/
def cfP (w : List ℕ) : ℕ := cfK (w.drop 1)

/-- The value of the finite continued fraction `[0; a₁, …, aₙ]`, as a
rational: `cfVal [] = 0`, `cfVal (a :: l) = 1/(a + cfVal l)`.  Junk on
words containing a `0` digit. -/
def cfVal : List ℕ → ℚ
  | [] => 0
  | a :: l => 1 / (a + cfVal l)

/-- The CF cylinder of the word `w`: reals in `(0,1)` whose first
`w.length` CF digits spell `w`. -/
noncomputable def cfCylinder (w : List ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | ∀ i < w.length, cfDigit x i = w.getD i 0}

/-- The **offset** CF cylinder: reals in `(0,1)` whose CF digits at
positions `m, m+1, …, m+w.length-1` spell `w`.  `cfCylinderFrom 0 = cfCylinder`.
Used to name "future" events (digits from index `m` onward) in the
ψ-mixing statement (`Literature.philipp_psi_mixing`). -/
noncomputable def cfCylinderFrom (m : ℕ) (w : List ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | ∀ i < w.length, cfDigit x (m + i) = w.getD i 0}

/-- The Gauss measure `dγ = dx/((1+x) log 2)` on `(0,1)` — the
`gaussMap`-invariant probability measure. -/
noncomputable def gaussMeasure : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
    fun x => ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹)

/-- **Gauss measure of a subinterval**: `γ(u,v) = (log(1+v) - log(1+u))/log 2`
for `0 ≤ u ≤ v ≤ 1` — the closed form behind the Gauss–Kuzmin single-digit
law.  Same route as `gaussMeasure_univ` (`CFDigitLaw.lean`), generalized
from `(0,1)` to `(u,v)`.  Lives here (not `CFDigitLaw.lean`) since it is
pure real analysis on `gaussMeasure`'s definition, needed by `CFCylinder.lean`
(which `CFDigitLaw.lean` imports, so it can't import back). -/
theorem gaussMeasure_Ioo {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    gaussMeasure (Set.Ioo u v) =
      ENNReal.ofReal ((Real.log (1 + v) - Real.log (1 + u)) / Real.log 2) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ x ∈ Set.Icc u v, (0 : ℝ) < (1 + x) * Real.log 2 := by
    intro x hx
    nlinarith [hx.1, hu]
  set g : ℝ → ℝ := fun x => ((1 + x) * Real.log 2)⁻¹ with hg
  have hc : ContinuousOn g (Set.Icc u v) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact (hpos x hx).ne'
  have hIooss : Set.Ioo u v ⊆ Set.Icc u v := Set.Ioo_subset_Icc_self
  have hInt : MeasureTheory.IntegrableOn g (Set.Ioo u v) volume :=
    (hc.integrableOn_Icc).mono_set hIooss
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo u v)] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have := hpos x (hIooss hx)
    positivity
  have hval : ∫ x in Set.Ioo u v, g x ∂volume
      = (Real.log (1 + v) - Real.log (1 + u)) / Real.log 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le huv]
    have hsplit : ∀ x : ℝ, g x = (Real.log 2)⁻¹ * (1 + x)⁻¹ := by
      intro x
      simp only [hg]
      rw [mul_inv, mul_comm]
    simp only [hsplit]
    have hint : ∫ x in u..v, (1 + x)⁻¹ = Real.log (1 + v) - Real.log (1 + u) := by
      rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y⁻¹) 1,
        integral_inv_of_pos (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)]
    rw [intervalIntegral.integral_const_mul, hint, div_eq_inv_mul]
  have hsubset : Set.Ioo u v ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt hu hx.1, lt_of_lt_of_le hx.2 hv⟩
  rw [gaussMeasure, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left hsubset,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, hval]

/-- The inverse-branch map of the cylinder `w`: `y ↦ [0; a₁, …, aₙ + y]`
in lowest terms, i.e. `(pₙ + pₙ₋₁·y)/(qₙ + qₙ₋₁·y)`.  Sends `[0,1]` onto
the closure of `cfCylinder w`; its image of `y = Tⁿx` recovers `x`. -/
noncomputable def cylMap (w : List ℕ) (y : ℝ) : ℝ :=
  ((cfP w : ℝ) + (cfP w.dropLast : ℝ) * y) /
    ((cfK w : ℝ) + (cfK w.dropLast : ℝ) * y)

/-- The conditional-density family: `h_t(y) = (1+t)/(1+t·y)²`.  For
`t = qₙ₋₁/qₙ`, this is the density (w.r.t. Lebesgue) of `Tⁿx` given
`x ∈ cfCylinder w`, uniformly in `[1/2, 2]` — the engine of the W3
mixing/Chebyshev argument. -/
noncomputable def tailDensity (t : ℝ) (y : ℝ) : ℝ :=
  (1 + t) / (1 + t * y) ^ 2

end NormalNumbers
