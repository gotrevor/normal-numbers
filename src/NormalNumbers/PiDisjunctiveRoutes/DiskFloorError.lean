/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.DiskResidueCostume

/-!
# The disk floor-error bound is already at the perimeter scale

The divisor formula and the elementary alternating-series remainder turn the
existing area estimate into a bound on the *entire* character-weighted floor
error.  Consequently a vanishing scaled tail-floor error is not a new
digit-visitation estimate.  Both classical arithmetic inputs are explicit.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.DiskFloorError

noncomputable def leibnizPartial (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ)/d

/-- Classical alternating-series remainder, in the denominator cutoff convention.
There are ceil(D/2) nonzero terms; the next odd denominator is at least D+1.
This is a named input, not an axiom and not a new conjecture about digits. -/
def LeibnizRemainderBound : Prop :=
  ∀ D : ℕ, |leibnizPartial D-Real.pi/4| ≤ 1/((D : ℝ)+1)

noncomputable def floorError (n D : ℕ) : ℝ :=
  16^n*leibnizPartial D-(diskSmallPart n D : ℝ)

noncomputable def tailFloorError (n D : ℕ) : ℝ :=
  floorError n (16^n)-floorError n D

theorem floorError_eq (n D : ℕ) :
    floorError n D = ∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) *
      ((16 : ℝ)^n/d-((16^n/d : ℕ) : ℝ)) := by
  have hc : (diskSmallPart n D : ℝ) = ∑ d ∈ Finset.Icc 1 D,
      (chiFour d : ℝ)*((16^n/d : ℕ) : ℝ) := by
    rw [diskSmallPart, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [floorError, leibnizPartial, hc]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem floorError_abs_le (n D : ℕ) : |floorError n D| ≤ D := by
  rw [floorError_eq]
  calc |∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) *
          ((16 : ℝ)^n/d-((16^n/d : ℕ) : ℝ))|
      ≤ ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : (0 : ℝ) < d := by
          exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hlo := Nat.cast_div_le (α := ℝ) (m := 16^n) (n := d)
        have hhi : (16 : ℝ)^n/d < ((16^n/d : ℕ) : ℝ)+1 := by
          apply (div_lt_iff₀ hdpos).mpr
          have h := Nat.lt_div_mul_add (a := 16^n) (b := d) (by exact_mod_cast hdpos)
          have h' : ((16^n : ℕ) : ℝ) < ((16^n/d*d+d : ℕ) : ℝ) := by
            exact_mod_cast h
          push_cast at h'
          nlinarith
        push_cast at hlo
        have hfract : |(16 : ℝ)^n/d-((16^n/d : ℕ) : ℝ)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hchi : |(chiFour d : ℝ)| ≤ 1 := by
          unfold chiFour
          split_ifs <;> norm_num
        rw [abs_mul]
        exact mul_le_one₀ hchi (abs_nonneg _) hfract
    _ = D := by simp

@[blueprint (title := "The full disk floor error is bounded by the existing perimeter estimate")]
theorem total_floorError_bound (hdiv : DiskDivisorIdentity)
    (hL : LeibnizRemainderBound) (n : ℕ) :
    |floorError n (16^n)| ≤ (5*(4 : ℝ)^n+5)/4 := by
  have hR : ((4^n : ℕ)^2) = 16^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hcount : (diskCount (4^n) : ℝ) =
      1+4*(diskSmallPart n (16^n) : ℝ) := by
    have h := hdiv (4^n)
    rw [hR] at h
    change (diskCount (4^n) : ℤ) = 1+4*diskSmallPart n (16^n) at h
    exact_mod_cast h
  have hs := diskCount_sub_area (4^n) (Nat.one_le_pow _ _ (by norm_num))
  have hRreal : ((4 : ℝ)^n)^2 = (16 : ℝ)^n := by exact_mod_cast hR
  push_cast at hs
  rw [hRreal, hcount, abs_le] at hs
  have hl := hL (16^n)
  push_cast at hl
  have hN : (0 : ℝ) < 16^n+1 := by positivity
  have hscaled : |(16 : ℝ)^n*(leibnizPartial (16^n)-Real.pi/4)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16^n)]
    calc (16 : ℝ)^n * |leibnizPartial (16^n)-Real.pi/4|
        ≤ 16^n*(1/(16^n+1)) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ 1 := by rw [mul_one_div, div_le_one hN]; linarith
  rw [abs_le] at hscaled ⊢
  unfold floorError
  constructor <;> nlinarith

@[blueprint (title := "Tail floor errors already vanish at the disk digit-shadow scale")]
theorem tail_floorError_scaled_bound (hdiv : DiskDivisorIdentity)
    (hL : LeibnizRemainderBound) (n D : ℕ) (hD : D ≤ 4^n) :
    |4*tailFloorError n D/(8 : ℝ)^n| ≤ 14/(2 : ℝ)^n := by
  have ht := total_floorError_bound hdiv hL n
  have hs := floorError_abs_le n D
  have hd : (D : ℝ) ≤ (4 : ℝ)^n := by exact_mod_cast hD
  have h1 : (1 : ℝ) ≤ 4^n := one_le_pow₀ (by norm_num)
  have he : |tailFloorError n D| ≤ (14*(4 : ℝ)^n)/4 := by
    unfold tailFloorError
    have h := abs_sub_le (floorError n (16^n)) 0 (floorError n D)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by positivity : (0 : ℝ) < 8^n)]
  have h8 : (8 : ℝ)^n = 2^n*4^n := by rw [← mul_pow]; norm_num
  rw [h8, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 2^n)]

end NormalNumbers.PiDisjunctiveRoutes.DiskFloorError
