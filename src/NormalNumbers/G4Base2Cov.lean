/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Base-2 very-large primes: the deterministic covariance algebra (N4, abstract)

`ω_{S,>Y} = Σ_ℓ (1 − g_ℓ) + err` with `err ≥ 0` small on average.  Centring at
`m = Σ_ℓ (1 − δ_ℓ)` the cross moment of two shifts is the bin-pair cross moments plus
`O((2C₀ + A)·avg err)`, where `C₀` bounds the bin part pointwise (not `B` times anything).
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- **The error terms cost `(2C₀ + A)·ε₁`.** -/
theorem abs_avg_cross_le (P : Finset ℕ) (Fi Fj ei ej m : ℕ → ℝ) {C₀ A ε₁ ε₂ : ℝ}
    (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A)
    (hFi : ∀ n ∈ P, |Fi n - m n| ≤ C₀) (hFj : ∀ n ∈ P, |Fj n - m n| ≤ C₀)
    (hei : ∀ n ∈ P, 0 ≤ ei n) (hej : ∀ n ∈ P, 0 ≤ ej n) (heiA : ∀ n ∈ P, ei n ≤ A)
    (havgi : (P.card : ℝ)⁻¹ * ∑ n ∈ P, ei n ≤ ε₁) (havgj : (P.card : ℝ)⁻¹ * ∑ n ∈ P, ej n ≤ ε₁)
    (hmain : |(P.card : ℝ)⁻¹ * ∑ n ∈ P, (Fi n - m n) * (Fj n - m n)| ≤ ε₂) :
    |(P.card : ℝ)⁻¹ * ∑ n ∈ P, (Fi n + ei n - m n) * (Fj n + ej n - m n)|
      ≤ ε₂ + (2 * C₀ + A) * ε₁ := by
  have hc : (0 : ℝ) ≤ (P.card : ℝ)⁻¹ := by positivity
  have hsplit : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (Fi n + ei n - m n) * (Fj n + ej n - m n)
      = (P.card : ℝ)⁻¹ * ∑ n ∈ P, (Fi n - m n) * (Fj n - m n)
        + (P.card : ℝ)⁻¹ * ∑ n ∈ P, ((Fi n - m n) * ej n + ei n * (Fj n - m n)
          + ei n * ej n) := by
    rw [← mul_add, ← sum_add_distrib]; congr 1
    refine sum_congr rfl fun n _ => by ring
  have hrest : |∑ n ∈ P, ((Fi n - m n) * ej n + ei n * (Fj n - m n) + ei n * ej n)|
      ≤ ∑ n ∈ P, (C₀ * ej n + C₀ * ei n + A * ej n) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have h1 : |(Fi n - m n) * ej n| ≤ C₀ * ej n := by
      rw [abs_mul, abs_of_nonneg (hej n hn)]
      exact mul_le_mul_of_nonneg_right (hFi n hn) (hej n hn)
    have h2 : |ei n * (Fj n - m n)| ≤ C₀ * ei n := by
      rw [abs_mul, abs_of_nonneg (hei n hn), mul_comm]
      exact mul_le_mul_of_nonneg_right (hFj n hn) (hei n hn)
    have h3 : |ei n * ej n| ≤ A * ej n := by
      rw [abs_of_nonneg (mul_nonneg (hei n hn) (hej n hn))]
      exact mul_le_mul_of_nonneg_right (heiA n hn) (hej n hn)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add hmain ?_)
  rw [abs_mul, abs_of_nonneg hc]
  calc (P.card : ℝ)⁻¹ * |∑ n ∈ P, ((Fi n - m n) * ej n + ei n * (Fj n - m n) + ei n * ej n)|
      ≤ (P.card : ℝ)⁻¹ * ∑ n ∈ P, (C₀ * ej n + C₀ * ei n + A * ej n) :=
        mul_le_mul_of_nonneg_left hrest hc
    _ = C₀ * ((P.card : ℝ)⁻¹ * ∑ n ∈ P, ej n) + C₀ * ((P.card : ℝ)⁻¹ * ∑ n ∈ P, ei n)
          + A * ((P.card : ℝ)⁻¹ * ∑ n ∈ P, ej n) := by
        simp only [sum_add_distrib, ← mul_sum]; ring
    _ ≤ C₀ * ε₁ + C₀ * ε₁ + A * ε₁ := by gcongr
    _ = (2 * C₀ + A) * ε₁ := by ring

/-- **Bin-pair expansion.**  The cross moment of two bin sums is at most `B²` times the worst
bin-pair cross moment. -/
theorem abs_avg_binSum_le (P : Finset ℕ) {B : ℕ} (u v : Fin B → ℕ → ℝ) {ε₂ : ℝ}
    (h : ∀ ℓ ℓ', |(P.card : ℝ)⁻¹ * ∑ n ∈ P, u ℓ n * v ℓ' n| ≤ ε₂) :
    |(P.card : ℝ)⁻¹ * ∑ n ∈ P, (∑ ℓ, u ℓ n) * (∑ ℓ', v ℓ' n)| ≤ (B : ℝ) ^ 2 * ε₂ := by
  have heq : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (∑ ℓ, u ℓ n) * (∑ ℓ', v ℓ' n)
      = ∑ ℓ, ∑ ℓ', (P.card : ℝ)⁻¹ * ∑ n ∈ P, u ℓ n * v ℓ' n := by
    simp_rw [sum_mul_sum, ← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun ℓ _ => ?_
    simp_rw [mul_sum]
    exact sum_comm
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun ℓ _ => abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun ℓ _ => sum_le_sum fun ℓ' _ => h ℓ ℓ').trans ?_
  simp; ring_nf; rfl

end NormalNumbers.G4.Base2
