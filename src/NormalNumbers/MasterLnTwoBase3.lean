/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterKicked
import NormalNumbers.LnTwoIrrational
import NormalNumbers.PiSqBBP

/-!
# Hypothesis A ⇒ `ln 2` normal in base 3 (Bailey–Crandall Thm 1.1)

`ln 2 = 2·artanh(1/3) = Σ_{n≥1} (6/(2n−1))/9ⁿ`: an instance of `hypA_isNormal_of_kicked` in
base 9, then base descent `9 = 3²`.
-/
namespace NormalNumbers.MasterConjectures
open Polynomial Filter NormalNumbers

/-- The base-9 kick for `ln 2 = 2·artanh(1/3) = Σ_{n≥1} (6/(2n−1))/9ⁿ`. -/
noncomputable def lnTwoNineKick (n : ℕ) : ℝ := 6 / (2 * (n : ℝ) - 1)

theorem hasSum_lnTwoNine :
    HasSum (fun k : ℕ => lnTwoNineKick (k + 1) / ((9 : ℕ) : ℝ) ^ (k + 1)) (Real.log 2) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := 1 / 3) (by norm_num [abs_of_pos])
  have hv : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hv] at h
  convert h using 1
  funext k
  simp only [lnTwoNineKick]
  push_cast
  have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [show (9 : ℝ) ^ (k + 1) = 3 * 3 ^ (2 * k + 1) by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; ring]
  rw [div_pow, one_pow]
  have h2 : (2 * ((k : ℝ) + 1) - 1) = 2 * k + 1 := by ring
  rw [h2]
  field_simp
  ring

theorem tendsto_lnTwoNine_tail :
    Tendsto (fun n : ℕ => ((9 : ℕ) : ℝ) ^ n * (Real.log 2 - kickedPartial 9 lnTwoNineKick n))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => 1 * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 : ℝ)
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [Real.norm_eq_abs]
  have hcap : ∀ m, n + 1 ≤ m → |lnTwoNineKick m| ≤ 6 / (2 * (n : ℝ) + 1) := by
    intro m hm
    have hmR : (n : ℝ) + 1 ≤ m := by exact_mod_cast hm
    rw [lnTwoNineKick, abs_of_pos (by apply div_pos <;> linarith)]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  refine (kicked_tail_abs_le (b := 9) (by norm_num) n hasSum_lnTwoNine hcap).trans ?_
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  push_cast
  rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- **Hypothesis A ⇒ `ln 2` normal in base 9** (the `artanh(1/3)` series, `p = 6`, `q = 2X − 1`). -/
theorem hypA_lnTwo_base9 (hA : BaileyCrandallHypA) : IsNormal 9 (Real.log 2) := by
  refine hypA_isNormal_of_kicked hA (C 6) (C 2 * X - C 1) 9 (by norm_num)
    (by simp) ?_ ?_ lnTwoNineKick ?_ _ irrational_log_two tendsto_lnTwoNine_tail
  · rw [natDegree_C]
    have : (C 2 * X - C 1 : ℤ[X]).natDegree = 1 := by compute_degree!
    omega
  · intro n hn h
    simp at h
    omega
  · intro n hn
    simp [lnTwoNineKick]

/-- **Hypothesis A ⇒ `ln 2` normal in base 3** (Bailey–Crandall Thm 1.1; `9 = 3²`). -/
theorem hypA_lnTwo_base3 (hA : BaileyCrandallHypA) : IsNormal 3 (Real.log 2) :=
  isNormal_of_isNormal_pow (b := 3) (K := 2) (by norm_num) (by norm_num) (hypA_lnTwo_base9 hA)

end NormalNumbers.MasterConjectures
