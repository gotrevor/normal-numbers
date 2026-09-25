/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtElliottMatch

/-!
# Assembling the log-averaged `D = 2` rung

Laps 7–12 reduced the two-shift `ζ^ω` correlation to a finite sum, over coprime powerful pairs
`(d, e)` with `d, e ≤ Y`, of sums

    ∑_j  (weight) · ζ₀^{Ω(e j + b₀)} · ζ₁^{Ω(d j + b₁)} ,   b₀ = (a+1)/d, b₁ = (a+2)/e,

with a truncation error `(1 + log N) · bridgeTail(Y)` (lap 12) and both structural hypotheses of
`Erdos67b.NonasymptoticLogElliott` verified (lap 11, determinant exactly `1`).

One mismatch of *weights* remains between our sum and `Erdos67b.elliottLogCorrelation`: ours
carries the harmonic weight of the ORIGINAL variable `n = L j + a` (`L = de`), while the Elliott
correlation carries the harmonic weight of the PROGRESSION variable `j`.  This file shows the
two differ by an **absolutely bounded** amount:

    ∑_{j ≥ 1} | 1/(Lj + a) − 1/(Lj) |  =  ∑_{j ≥ 1} a / (Lj(Lj+a))  ≤  (a/L²)·∑ j⁻²  ≤  2/L ,

using `a < L` (which `exists_joint_class` provides).  Summed over the `(d, e)` with `d, e ≤ Y`
this is a constant `C(Y)` depending on `Y` **but not on `N`** — and since `Y` is chosen from `ε`
*before* `N → ∞`, it is negligible against the main term of size `≍ log W`.

That is the last structural obstruction.  What is then left is genuinely the deep input:
`Erdos67b.NonasymptoticLogElliott` itself, which in this repo is the open, ratified bet
`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott` (Tao, Forum Math. Pi 4 (2016), Thm 1.3).
Note it is the GENERAL two-function, two-form statement that is needed: the dependency's proved
`Erdos67b.unitCircleLogElliott` covers only `g₂ = conj g₁` along `n` and `n + h`, whereas our two
twists `ζ₀, ζ₁` are independent and our two forms have leading coefficients `e` and `d`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- `∑_{j=1}^{J} j⁻² ≤ 2 − 1/J`, by telescoping.  (Elementary; avoids invoking Basel.) -/
theorem sum_inv_sq_le (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ ≤ 2 - 1 / (J : ℝ) := by
  induction J with
  | zero => omega
  | succ J ih =>
    rcases Nat.eq_or_lt_of_le hJ with h1 | h1
    · have : J = 0 := by omega
      subst this
      norm_num
    · have hJ1 : 1 ≤ J := by omega
      have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
      have hJ1R : (0 : ℝ) < ((J : ℝ) + 1) := by linarith
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : (((J + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / (J : ℝ) - 1 / ((J : ℝ) + 1) := by
        have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have heq : 1 / (J : ℝ) - 1 / ((J : ℝ) + 1) = 1 / ((J : ℝ) * ((J : ℝ) + 1)) := by
          field_simp
          ring
        rw [heq, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hcast2 : (((J + 1 : ℕ) : ℝ)) = (J : ℝ) + 1 := by push_cast; ring
      calc ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ + (((J + 1 : ℕ) : ℝ) ^ 2)⁻¹
          ≤ (2 - 1 / (J : ℝ)) + (1 / (J : ℝ) - 1 / ((J : ℝ) + 1)) :=
            add_le_add (ih hJ1) hstep
        _ = 2 - 1 / ((J : ℝ) + 1) := by ring
        _ = 2 - 1 / ((J + 1 : ℕ) : ℝ) := by rw [hcast2]

/-- **Weight transfer.**  Replacing the harmonic weight of the original variable `n = Lj + a`
by that of the progression variable `j` (scaled by `1/L`) costs at most `2/L`, uniformly in the
length `J` of the sum and in the summand `G`. -/
theorem weight_transfer {L a : ℕ} (hL : 0 < L) (haL : a < L) (J : ℕ) (G : ℕ → ℂ)
    (hG : ∀ j, ‖G j‖ ≤ 1) :
    ‖(∑ j ∈ Icc 1 J, (((L * j + a : ℕ) : ℝ))⁻¹ • G j)
        - (L : ℝ)⁻¹ • ∑ j ∈ Icc 1 J, ((j : ℝ))⁻¹ • G j‖ ≤ 2 / (L : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hrw : (∑ j ∈ Icc 1 J, (((L * j + a : ℕ) : ℝ))⁻¹ • G j)
      - (L : ℝ)⁻¹ • ∑ j ∈ Icc 1 J, ((j : ℝ))⁻¹ • G j
      = ∑ j ∈ Icc 1 J, ((((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹) • G j := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, sub_smul]
  rw [hrw]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Icc 1 J,
      ‖((((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹) • G j‖
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hjR : (0 : ℝ) < (j : ℝ) := by linarith
    have hcast : ((L * j + a : ℕ) : ℝ) = (L : ℝ) * (j : ℝ) + (a : ℝ) := by push_cast; ring
    have hden : (0 : ℝ) < (L : ℝ) * (j : ℝ) + (a : ℝ) := by positivity
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjR
    have hdne : (L : ℝ) * (j : ℝ) + (a : ℝ) ≠ 0 := ne_of_gt hden
    have hdiff : (((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹
        = - ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ)))) := by
      rw [hcast]
      field_simp
      ring
    rw [norm_smul, hdiff]
    have hGj := hG j
    have hbound : ‖- ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))))‖
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have h1 : (L : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ ((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ)) := by
        have hprod : (0 : ℝ) ≤ (L : ℝ) * (j : ℝ) * (a : ℝ) :=
          mul_nonneg (mul_nonneg hLR.le hjR.le) (Nat.cast_nonneg a)
        nlinarith [hprod]
      have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      calc (a : ℝ) = (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ * ((L : ℝ) ^ 2 * (j : ℝ) ^ 2) := by
            field_simp
        _ ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ *
              (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))) := by
            refine mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ‖- ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))))‖ * ‖G j‖
        ≤ ((a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹) * 1 :=
          mul_le_mul hbound hGj (norm_nonneg _) (by positivity)
      _ = (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · norm_num
    positivity
  · have hsum : ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ ≤ 2 := by
      refine (sum_inv_sq_le J hJ).trans ?_
      have : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
      have : 0 < 1 / (J : ℝ) := by positivity
      linarith
    have haL' : (a : ℝ) ≤ (L : ℝ) := by
      have : a ≤ L := le_of_lt haL
      exact_mod_cast this
    calc (a : ℝ) / (L : ℝ) ^ 2 * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * 2 := by
          refine mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (L : ℝ) / (L : ℝ) ^ 2 * 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact div_le_div_of_nonneg_right haL' (by positivity)
      _ = 2 / (L : ℝ) := by field_simp

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.sum_inv_sq_le
#print axioms NormalNumbers.CastingOut.weight_transfer
