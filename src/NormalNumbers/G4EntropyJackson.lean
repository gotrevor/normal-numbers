/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Jackson
import NormalNumbers.G4EntropyCapture

/-!
# Entropy expedition §3C: Fejér smoothing for an **arbitrary** bounded `dAv`-Lipschitz test

`G4Jackson.Frame.propJackson` smooths one specific test, `fr.test = clipTest fr.image fr.res`,
the clipped distance to the image of the *whole* orbit closure.  The entropy argument needs the
same smoothing for the clipped distance to `E_K(ℬ)`, the transported union of the selected joint
boxes — a different set at every `K`, chosen after seeing the data.

Inspection of the `G4Jackson` proof shows it uses only three properties of the test:

* continuity,
* `0 ≤ f ≤ 1`,
* `|f y − f y'| ≤ dAv y y' / ρ` (Lipschitz for the **average** coordinate metric).

So the whole development is reproved here for an arbitrary `f` with those three properties
(`smoothCoeff`, `sum_smoothCoeff_eq`, `norm_sum_smoothCoeff_sub_le`, `jackson_of_dAvLipschitz`),
and `Frame.propJackson`'s statement is recovered as the instance
`Frame.propJackson_of_general` (`G4Jackson.lean` itself is untouched).

`jackson_of_clipTest` is the form the expedition uses: for **any** nonempty `E`,

  `∃ c, (∀ y, ‖∑_q c_q χ_q y − clipTest E ρ y‖ ≤ 1/(ρ√(D+1))) ∧ ∑_{q≠0} ‖c_q‖ ≤ (2D+1)^r`.

The uniformity of `κ = 1/(ρ√(D+1))` and `Λ = (2D+1)^r` **in `E`** is what makes a data-dependent
choice of the captured collection `ℬ` legitimate: the approximation budget does not look at `E`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

section general

variable {r : ℕ} (D : ℕ) (f : Torus r → ℝ)

/-- The Fourier coefficients of the smoothed test `y ↦ ∫ f(y+w) P_D(w) dw`. -/
noncomputable def smoothCoeff (q : Fin r → ℤ) : ℂ :=
  (jackCoeff r D q : ℂ) * ∫ z : Torus r, (f z : ℂ) * torusChar (-q) z

variable {D f}

/-- The smoothed test is the trigonometric polynomial `∑_q c_q χ_q`. -/
theorem sum_smoothCoeff_eq (hcont : Continuous f) (y : Torus r) :
    ∑ q ∈ fourierBox r D, smoothCoeff D f q * torusChar q y
      = ∫ w : Torus r, (f (y + w) : ℂ) * (jackKer r D w : ℂ) := by
  have hsub : ∫ w : Torus r, (f (y + w) : ℂ) * (jackKer r D w : ℂ)
      = ∫ z : Torus r, (f z : ℂ) * (jackKer r D (z - y) : ℂ) := by
    rw [← integral_add_left_eq_self (fun z => (f z : ℂ) * (jackKer r D (z - y) : ℂ)) y]
    simp only [add_sub_cancel_left]
  rw [hsub]
  simp_rw [jackKer_expand, torusChar_sub, Finset.mul_sum]
  rw [integral_finsetSum (fourierBox r D)
    (f := fun q z => (f z : ℂ) * ((jackCoeff r D q : ℂ) * (torusChar q z * torusChar (-q) y)))
    fun q _ => integrable_of_continuous_torus
      ((Complex.continuous_ofReal.comp hcont).mul
        (continuous_const.mul ((continuous_torusChar q).mul continuous_const)))]
  rw [← sum_fourierBox_neg]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold smoothCoeff
  rw [neg_neg, jackCoeff_neg, mul_assoc, ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- **Uniform approximation for an arbitrary `dAv`-Lipschitz test.** -/
theorem norm_sum_smoothCoeff_sub_le (hcont : Continuous f) {ρ : ℝ} (hρ : 0 < ρ)
    (hlip : ∀ y y' : Torus r, |f y - f y'| ≤ dAv y y' / ρ) (y : Torus r) :
    ‖(∑ q ∈ fourierBox r D, smoothCoeff D f q * torusChar q y) - (f y : ℂ)‖
      ≤ 1 / (ρ * Real.sqrt (D + 1)) := by
  have hsq : 0 < Real.sqrt (D + 1) := Real.sqrt_pos.2 (by positivity)
  rw [sum_smoothCoeff_eq hcont]
  have hK := integral_jackKer r D
  have hcont_shift : Continuous fun w : Torus r => f (y + w) :=
    hcont.comp (continuous_const.add continuous_id)
  have hreal : (∫ w : Torus r, (f (y + w) : ℂ) * (jackKer r D w : ℂ)) - (f y : ℂ)
      = ((∫ w : Torus r, (f (y + w) - f y) * jackKer r D w : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have h1 : (f y : ℂ) = ∫ w : Torus r, ((f y * jackKer r D w : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul, hK, mul_one]
    rw [h1, ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only
      push_cast
      ring
    · exact integrable_of_continuous_torus
        ((Complex.continuous_ofReal.comp hcont_shift).mul
          (Complex.continuous_ofReal.comp (continuous_jackKer _ _)))
    · exact integrable_of_continuous_torus
        (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_jackKer _ _)))
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  have hpt : ∀ w : Torus r, |(f (y + w) - f y) * jackKer r D w|
      ≤ ((∑ ν, ‖w ν‖) / r) / ρ * jackKer r D w := by
    intro w
    rw [abs_mul, abs_of_nonneg (jackKer_nonneg _ _ _)]
    refine mul_le_mul_of_nonneg_right ?_ (jackKer_nonneg _ _ _)
    have := hlip (y + w) y
    rwa [dAv_add_left] at this
  have hint_abs : Integrable (fun w : Torus r => |(f (y + w) - f y) * jackKer r D w|) volume :=
    integrable_of_continuous_torus
      (((hcont_shift.sub continuous_const).mul (continuous_jackKer _ _)).abs)
  have hint_maj : Integrable
      (fun w : Torus r => ((∑ ν, ‖w ν‖) / r) / ρ * jackKer r D w) volume :=
    integrable_of_continuous_torus
      ((((continuous_finsetSum _ fun ν _ => (continuous_apply ν).norm).div_const _).div_const _).mul
        (continuous_jackKer _ _))
  calc |∫ w : Torus r, (f (y + w) - f y) * jackKer r D w|
      ≤ ∫ w : Torus r, |(f (y + w) - f y) * jackKer r D w| := abs_integral_le_integral_abs
    _ ≤ ∫ w : Torus r, ((∑ ν, ‖w ν‖) / r) / ρ * jackKer r D w :=
        integral_mono hint_abs hint_maj hpt
    _ = (1 / ρ) * ((1 / r) * ∑ ν, ∫ w : Torus r, ‖w ν‖ * jackKer r D w) := by
        rw [← integral_finsetSum, ← integral_const_mul, ← integral_const_mul]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
          exact Finset.sum_congr rfl fun ν _ => by ring
        · intro ν _
          exact integrable_of_continuous_torus
            ((continuous_apply ν).norm.mul (continuous_jackKer _ _))
    _ ≤ (1 / ρ) * ((1 / r) * ∑ _ν : Fin r, 1 / Real.sqrt (D + 1)) := by
        gcongr with ν _
        exact integral_norm_mul_jackKer_le r D ν
    _ ≤ 1 / (ρ * Real.sqrt (D + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hr : (1 / (r : ℝ)) * (r : ℝ) ≤ 1 := by
          rcases Nat.eq_zero_or_pos r with h | h
          · simp [h]
          · rw [one_div, inv_mul_cancel₀ (by exact_mod_cast h.ne')]
        calc (1 / ρ) * ((1 / r) * ((r : ℝ) * (1 / Real.sqrt (D + 1))))
            = (1 / ρ) * (1 / Real.sqrt (D + 1)) * ((1 / (r : ℝ)) * r) := by ring
          _ ≤ (1 / ρ) * (1 / Real.sqrt (D + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = 1 / (ρ * Real.sqrt (D + 1)) := by rw [mul_one, one_div_mul_one_div]

lemma norm_smoothCoeff_le_one (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1) (q : Fin r → ℤ) :
    ‖smoothCoeff D f q‖ ≤ 1 := by
  unfold smoothCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jackCoeff_nonneg _ _ _)]
  refine mul_le_one₀ (jackCoeff_le_one _ _ _) (norm_nonneg _) ?_
  refine norm_integral_le_one_of_le_one fun z => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 z)]
  exact mul_le_one₀ (h1 z) (norm_nonneg _) (norm_torusChar_le _ _)

/-- **The generalized Jackson bound.**  Any continuous `[0,1]`-valued test that is
`1/ρ`-Lipschitz for the average metric is uniformly `1/(ρ√(D+1))`-approximated by a
trigonometric polynomial of degree `D` with nontrivial Fourier mass at most `(2D+1)^r`.
Both budgets are **independent of the test**. -/
theorem jackson_of_dAvLipschitz (hcont : Continuous f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hlip : ∀ y y' : Torus r, |f y - f y'| ≤ dAv y y' / ρ) :
    ∃ c : (Fin r → ℤ) → ℂ,
      (∀ y, ‖(∑ q ∈ fourierBox r D, c q * torusChar q y) - (f y : ℂ)‖
        ≤ 1 / (ρ * Real.sqrt (D + 1))) ∧
      ∑ q ∈ (fourierBox r D).erase 0, ‖c q‖ ≤ (((2 * D + 1) ^ r : ℕ) : ℝ) := by
  refine ⟨smoothCoeff D f, norm_sum_smoothCoeff_sub_le hcont hρ hlip, ?_⟩
  calc ∑ q ∈ (fourierBox r D).erase 0, ‖smoothCoeff D f q‖
      ≤ ∑ _q ∈ (fourierBox r D).erase 0, (1 : ℝ) :=
        Finset.sum_le_sum fun q _ => norm_smoothCoeff_le_one h0 h1 q
    _ = ((fourierBox r D).erase 0).card := by simp
    _ ≤ (fourierBox r D).card := by exact_mod_cast Finset.card_erase_le
    _ = _ := by rw [NormalNumbers.G4.Frame.card_fourierBox]

end general

/-- **The form the expedition uses**: Jackson smoothing of the clipped distance to an
*arbitrary* nonempty set `E`, with budgets that do not depend on `E`. -/
theorem jackson_of_clipTest {r : ℕ} (D : ℕ) {E : Set (Torus r)} (hE : E.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ c : (Fin r → ℤ) → ℂ,
      (∀ y, ‖(∑ q ∈ fourierBox r D, c q * torusChar q y) - (clipTest E ρ y : ℂ)‖
        ≤ 1 / (ρ * Real.sqrt (D + 1))) ∧
      ∑ q ∈ (fourierBox r D).erase 0, ‖c q‖ ≤ (((2 * D + 1) ^ r : ℕ) : ℝ) :=
  jackson_of_dAvLipschitz (continuous_clipTest hE ρ) (fun y => clipTest_nonneg E hρ y)
    (fun y => clipTest_le_one E ρ y) hρ (fun y y' => abs_clipTest_sub_le hE hρ y y')

namespace Frame

open NormalNumbers.G4.Frame

/-- `Frame.propJackson` recovered as an instance of the general bound: the old endpoint is
untouched, and this reproves its exact statement from `jackson_of_clipTest`. -/
theorem propJackson_of_general (fr : NormalNumbers.G4.Frame) :
    fr.PropJackson (1 / (fr.res * Real.sqrt (fr.D + 1))) (((2 * fr.D + 1) ^ fr.r : ℕ) : ℝ) :=
  jackson_of_clipTest fr.D fr.image_nonempty fr.res_pos

end Frame

end NormalNumbers.G4Entropy
