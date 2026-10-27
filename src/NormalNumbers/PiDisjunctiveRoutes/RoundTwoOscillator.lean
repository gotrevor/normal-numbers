/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.RoundTwoPilotTargets

/-!
# Oscillator pilot: low-degree certificates are blind

Positive quadrature identities for `R = P'' + P` show that oscillator
certificates of degree at most 3 cannot reject `x = 3`, and of degree at most 4
cannot reject both `x = 3` and `x = 4`.  Both points avoid the word `[1]`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots

open Polynomial

/-- A rational polynomial of degree `≤ 4`, mapped to `ℝ`, is an explicit quartic. -/
lemma realPoly_eq_quartic (P : Polynomial ℚ) (hP : P.natDegree ≤ 4) :
    realPoly P = ∑ i ∈ Finset.range 5, C ((P.coeff i : ℚ) : ℝ) * X ^ i := by
  have h := P.as_sum_range' 5 (by omega)
  unfold realPoly
  conv_lhs => rw [h]
  simp [Polynomial.map_sum, ← C_mul_X_pow_eq_monomial]

/-- The parent's positive quadrature for quartics. -/
theorem quarticQuadratureIdentity : QuarticQuadratureIdentity := by
  intro P hP
  simp only
  have hR : ∀ t : ℝ, ((realPoly P).derivative.derivative + realPoly P).eval t =
      (2 * (P.coeff 2 : ℝ) + 6 * (P.coeff 3 : ℝ) * t + 12 * (P.coeff 4 : ℝ) * t ^ 2) +
      ((P.coeff 0 : ℝ) + (P.coeff 1 : ℝ) * t + (P.coeff 2 : ℝ) * t ^ 2 +
        (P.coeff 3 : ℝ) * t ^ 3 + (P.coeff 4 : ℝ) * t ^ 4) := by
    intro t
    rw [realPoly_eq_quartic P hP]
    simp [Finset.sum_range_succ, derivative_mul]
    ring
  have hE : ∀ t : ℝ, (realPoly P).eval t =
      (P.coeff 0 : ℝ) + (P.coeff 1 : ℝ) * t + (P.coeff 2 : ℝ) * t ^ 2 +
        (P.coeff 3 : ℝ) * t ^ 3 + (P.coeff 4 : ℝ) * t ^ 4 := by
    intro t
    rw [realPoly_eq_quartic P hP]
    simp [Finset.sum_range_succ]
  simp only [hR, hE]
  ring

/-- Cubic identity: `P(0)+P(3) = R(1)+R(2)` for `deg P ≤ 3`. -/
theorem cubic_identity (P : Polynomial ℚ) (hP : P.natDegree ≤ 3) :
    (realPoly P).eval 0 + (realPoly P).eval 3 =
      ((realPoly P).derivative.derivative + realPoly P).eval 1 +
      ((realPoly P).derivative.derivative + realPoly P).eval 2 := by
  have h4 : P.coeff 4 = 0 := P.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [realPoly_eq_quartic P (by omega)]
  simp [Finset.sum_range_succ, derivative_mul, derivative_X_pow, h4]
  ring

theorem cubicBlindAtThree : CubicBlindAtThree := by
  intro P hP hpos
  rw [cubic_identity P hP]
  exact add_pos (hpos 1 ⟨by norm_num, by norm_num⟩) (hpos 2 ⟨by norm_num, by norm_num⟩)

theorem quarticEndpointObstruction : QuarticEndpointObstruction := by
  intro P hP hpos
  have h := quarticQuadratureIdentity P hP
  simp only at h
  rw [h]
  have := hpos 0 ⟨le_rfl, by norm_num⟩
  have := hpos (1 / 2) ⟨by norm_num, by norm_num⟩
  have := hpos (3 / 2) ⟨by norm_num, by norm_num⟩
  have := hpos 2 ⟨by norm_num, by norm_num⟩
  have := hpos 4 ⟨by norm_num, le_rfl⟩
  positivity

/-- Scoped negation for the Maze; higher degrees are outside this claim. -/
theorem not_quartic_endpoint_certificate :
    ¬ ∃ P : Polynomial ℚ, P.natDegree ≤ 4 ∧ PositiveOscillator P ∧
      (realPoly P).eval 0 + (realPoly P).eval 3 ≤ 0 ∧
      (realPoly P).eval 0 + (realPoly P).eval 4 ≤ 0 := by
  rintro ⟨P, hD, hP, h3, h4⟩
  have h := quarticEndpointObstruction P hD hP
  linarith

theorem quarticRejectsThree : QuarticRejectsThree := by
  have hreal : realPoly quarticControl =
      -X ^ 4 + 8 * X ^ 3 - 8 * X ^ 2 - 32 * X + C (65 / 4 : ℝ) := by
    simp [realPoly, quarticControl, Polynomial.map_sub, Polynomial.map_add]
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [hreal]
    simp [derivative_mul]
    have h : 0 ≤ t * (4 - t) * (t - 2) ^ 2 :=
      mul_nonneg (mul_nonneg ht.1 (by linarith [ht.2])) (sq_nonneg _)
    nlinarith [h]
  · rw [hreal]; simp; norm_num

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots
