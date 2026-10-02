/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.WeylCriterion

/-!
# Quantitative C′: an Erdős–Turán inequality by a Fejér sandwich (build gap 5)

The Fejér kernel `K_H(t) = |∑_{j≤H} e(jt)|²/(H+1)` is nonnegative, has unit mass over every
period, and is `≤ 1/(4δ²(H+1))` at distance `≥ δ` from `ℤ`.  Its window integrals
`g(x) = ∫_{x−β}^{x−α} K_H` are finite trigonometric polynomials whose nonzero coefficients are
`≤ 1/(π|m|)`, so `g` sandwiches the indicator of `[a, c)` with no Fourier-series convergence.
-/

open Complex Real MeasureTheory intervalIntegral Finset Filter

namespace NormalNumbers.PrimeModel.Quant

/-- The unit circle point `e(t) = exp(2πit)`. -/
noncomputable def zE (t : ℝ) : ℂ := Complex.exp (2 * π * I * t)

/-- The Fejér partial sum `∑_{j ≤ H} e(t)^j`. -/
noncomputable def fejS (H : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range (H + 1), zE t ^ j

/-- The Fejér kernel `K_H(t) = |∑_{j≤H} e(jt)|² / (H+1)`. -/
noncomputable def fejK (H : ℕ) (t : ℝ) : ℝ := ‖fejS H t‖ ^ 2 / (H + 1)

lemma fejK_nonneg (H : ℕ) (t : ℝ) : 0 ≤ fejK H t := by unfold fejK; positivity

lemma zE_pow (t : ℝ) (j : ℕ) : zE t ^ j = Complex.exp (2 * π * I * ((j : ℤ) : ℝ) * t) := by
  rw [zE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma norm_zE (t : ℝ) : ‖zE t‖ = 1 := by
  rw [zE, Complex.norm_exp]
  simp

lemma continuous_zE : Continuous zE := by unfold zE; fun_prop

lemma continuous_fejK (H : ℕ) : Continuous (fejK H) := by
  unfold fejK fejS; have := continuous_zE; fun_prop

/-- The double-sum expansion `K_H(t) = (H+1)⁻¹ ∑_{j,l} e((j−l)t)`. -/
lemma fejK_expand (H : ℕ) (t : ℝ) :
    ((fejK H t : ℝ) : ℂ) = (1 / ((H : ℂ) + 1)) * ∑ j ∈ range (H + 1), ∑ l ∈ range (H + 1),
      Complex.exp (2 * π * I * (((j : ℤ) - l : ℤ) : ℝ) * t) := by
  have hconj : (starRingEnd ℂ) (zE t) = Complex.exp (-(2 * π * I * t)) := by
    rw [zE, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  have hsq : ((‖fejS H t‖ ^ 2 : ℝ) : ℂ) = fejS H t * (starRingEnd ℂ) (fejS H t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [fejK]; push_cast
  rw [show ((‖fejS H t‖ : ℂ)) ^ 2 = ((‖fejS H t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, hsq]
  rw [div_eq_mul_inv, mul_comm, one_div]
  congr 1
  rw [fejS, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_pow, hconj, zE, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `∫_p^q e(mt) dt` for `m ≠ 0`. -/
lemma integral_exp_int {m : ℤ} (hm : m ≠ 0) (p q : ℝ) :
    ∫ t in p..q, Complex.exp (2 * π * I * (m : ℝ) * t)
      = (Complex.exp (2 * π * I * (m : ℝ) * q) - Complex.exp (2 * π * I * (m : ℝ) * p))
        / (2 * π * I * (m : ℝ)) := by
  have hc : (2 * π * I * (m : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  exact integral_exp_mul_complex hc

lemma exp_two_pi_int (m : ℤ) (p : ℝ) :
    Complex.exp (2 * π * I * (m : ℝ) * ((p + 1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * (m : ℝ) * p) := by
  rw [show 2 * π * I * ((m : ℝ) : ℂ) * ((p + 1 : ℝ) : ℂ)
      = 2 * π * I * (m : ℝ) * p + (m : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Unit mass over every period. -/
lemma integral_fejK_period (H : ℕ) (p : ℝ) : ∫ t in p..(p + 1), fejK H t = 1 := by
  have hc : ((∫ t in p..(p + 1), fejK H t : ℝ) : ℂ) = 1 := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [fejK_expand]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      exact (continuous_finsetSum _ (fun l _ => by fun_prop)).intervalIntegrable _ _)]
    have hin : ∀ j ∈ range (H + 1), ∫ t in p..(p + 1), ∑ l ∈ range (H + 1),
        Complex.exp (2 * π * I * (((j : ℤ) - l : ℤ) : ℝ) * t) = 1 := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum (fun l _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        have hm : ((j : ℤ) - l) ≠ 0 := by omega
        rw [integral_exp_int hm, exp_two_pi_int, sub_self, zero_div]
      · intro h; exact absurd hj h
    rw [Finset.sum_congr rfl hin]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  exact_mod_cast hc

/-- `|sin(πt)| ≥ 2δ` at distance `≥ δ` from `{0, ±1}` inside `(−1, 1)`. -/
lemma two_mul_le_abs_sin {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ |t|) (h2 : |t| ≤ 1 - δ) :
    2 * δ ≤ |Real.sin (π * t)| := by
  have key : ∀ s : ℝ, δ ≤ s → s ≤ 1 / 2 → 2 * δ ≤ Real.sin (π * s) := by
    intro s hs1 hs2
    have := Real.mul_le_sin (x := π * s) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * s) = 2 * s := by field_simp
    linarith
  have hab : |t| ≤ 1 := by linarith
  have e : |Real.sin (π * t)| = Real.sin (π * |t|) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at hab ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos]))
    · rw [abs_of_nonpos ht] at hab ⊢
      rw [show π * t = -(π * -t) by ring, Real.sin_neg, abs_neg]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos]))
  rw [e]
  rcases le_total |t| (1 / 2) with hs | hs
  · exact key _ h1 hs
  · have := key (1 - |t|) (by linarith) (by linarith)
    rwa [show π * (1 - |t|) = π - π * |t| by ring, Real.sin_pi_sub] at this

lemma norm_zE_sub_one_sq (t : ℝ) : ‖zE t - 1‖ ^ 2 = 4 * Real.sin (π * t) ^ 2 := by
  have hz : zE t = Complex.exp (((2 * π * t : ℝ) : ℂ) * I) := by
    rw [zE]; congr 1; push_cast; ring
  rw [hz, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show ((Real.cos (2 * π * t) : ℂ) + (Real.sin (2 * π * t) : ℂ) * I - 1)
      = ((Real.cos (2 * π * t) - 1 : ℝ) : ℂ) + ((Real.sin (2 * π * t) : ℝ) : ℂ) * I by
      push_cast; ring]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hc : Real.cos (2 * π * t) = 1 - 2 * Real.sin (π * t) ^ 2 := by
    rw [show 2 * π * t = 2 * (π * t) by ring, Real.cos_two_mul, Real.cos_sq']; ring
  have hs : Real.sin (2 * π * t) = 2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [show 2 * π * t = 2 * (π * t) by ring, Real.sin_two_mul]
  rw [hc, hs]
  have := Real.sin_sq_add_cos_sq (π * t)
  nlinarith [this]

/-- **Pointwise decay.**  At distance `≥ δ` from `{0, ±1}`, `K_H(t) ≤ 1/(4δ²(H+1))`. -/
lemma fejK_le (H : ℕ) {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ |t|) (h2 : |t| ≤ 1 - δ) :
    fejK H t ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by
  have hsin := two_mul_le_abs_sin hδ h1 h2
  have hz : 4 * δ ≤ ‖zE t - 1‖ := by
    have hsq := norm_zE_sub_one_sq t
    have : (4 * δ) ^ 2 ≤ ‖zE t - 1‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_abs (Real.sin (π * t)), abs_nonneg (Real.sin (π * t))]
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg (zE t - 1)]
  have hgeom : fejS H t * (zE t - 1) = zE t ^ (H + 1) - 1 := by
    rw [fejS]; exact geom_sum_mul _ _
  have hnum : ‖zE t ^ (H + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_zE, one_pow, norm_one]; norm_num
  have hS : ‖fejS H t‖ * (4 * δ) ≤ 2 := by
    have := congrArg norm hgeom
    rw [norm_mul] at this
    nlinarith [norm_nonneg (fejS H t)]
  have hS' : ‖fejS H t‖ ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [fejK, div_le_div_iff₀ (by positivity) (by positivity)]
  have h0 := norm_nonneg (fejS H t)
  have hsq : ‖fejS H t‖ ^ 2 ≤ (1 / (2 * δ)) ^ 2 := pow_le_pow_left₀ h0 hS' 2
  have e : (1 / (2 * δ)) ^ 2 * (4 * δ ^ 2) = 1 := by field_simp; ring
  have hH : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ 4 * δ ^ 2 * ((H : ℝ) + 1))]

end NormalNumbers.PrimeModel.Quant
