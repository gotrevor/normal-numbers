/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogArith

/-!
# N2 and N6: the tail, and the shift along index-free stretches

`x_S = Σ_{m ∈ S} 1/(m 2^m)`.  `two_pow_mul_xS_sub`: `0 ≤ 2^n x_S − R_n ≤ 1/(n+1)`.
`Rs_succ`, `Rs_shift`: `R_{n+t} = 2^t R_n` when `S` misses `(n, n+t]`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset

open Classical in
/-- `x_S = Σ_{m ∈ S} 1/(m·2^m)`. -/
noncomputable def xS (S : ℕ → Prop) : ℝ :=
  ∑' m : ℕ, if S m then 1 / ((m : ℝ) * 2 ^ m) else 0

open Classical in
lemma term_le (S : ℕ → Prop) (m : ℕ) :
    0 ≤ (if S m then 1 / ((m : ℝ) * 2 ^ m) else 0) ∧
      (if S m then 1 / ((m : ℝ) * 2 ^ m) else 0) ≤ (1 / 2) ^ m := by
  split_ifs
  · refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [one_div_pow, one_div, one_div]
      apply inv_anti₀ (by positivity)
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) m]
  · exact ⟨le_rfl, by positivity⟩

open Classical in
lemma summable_term (S : ℕ → Prop) :
    Summable fun m : ℕ => if S m then 1 / ((m : ℝ) * 2 ^ m) else 0 :=
  Summable.of_nonneg_of_le (fun m => (term_le S m).1) (fun m => (term_le S m).2)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- **N2.**  `0 ≤ 2^n x_S − R_n ≤ 1/(n+1)` when `S ⊆ {m ≥ 1}`. -/
theorem two_pow_mul_xS_sub (S : ℕ → Prop) (hS : ∀ m, S m → 1 ≤ m) (n : ℕ) :
    0 ≤ (2 : ℝ) ^ n * xS S - (Rs S n : ℝ) ∧
      (2 : ℝ) ^ n * xS S - (Rs S n : ℝ) ≤ 1 / (n + 1) := by
  classical
  set f : ℕ → ℝ := fun m => if S m then 1 / ((m : ℝ) * 2 ^ m) else 0 with hf
  have hsum := summable_term S
  have hsplit := hsum.sum_add_tsum_nat_add (n + 1)
  have hhead : (2 : ℝ) ^ n * ∑ i ∈ range (n + 1), f i = (Rs S n : ℝ) := by
    unfold Rs
    simp only [Rat.cast_sum, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_zero]
    rw [Finset.mul_sum, Finset.range_eq_Ico]
    rw [show Icc 1 n = Ico 1 (n + 1) from rfl]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have h0 : f 0 = 0 := by simp only [hf]; rw [if_neg (fun h => by have := hS 0 h; omega)]
    rw [h0, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ico] at hm
    simp only [hf]
    split_ifs
    · have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      rw [show (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m by rw [← pow_add]; congr 1; omega]
      field_simp
    · simp
  have htail_sum : Summable fun i => f (i + (n + 1)) :=
    (summable_nat_add_iff (n + 1)).2 hsum
  have heq : (2 : ℝ) ^ n * xS S - (Rs S n : ℝ) = (2 : ℝ) ^ n * ∑' i, f (i + (n + 1)) := by
    rw [← hhead, show xS S = ∑' m, f m from rfl, ← hsplit]; ring
  rw [heq]
  constructor
  · exact mul_nonneg (by positivity) (tsum_nonneg fun i => (term_le S _).1)
  · -- `f (i+n+1) ≤ (1/(n+1)) · (1/2)^{i+n+1}`
    have hb : ∀ i, f (i + (n + 1)) ≤ 1 / (n + 1) * ((1 / 2) ^ (n + 1) * (1 / 2) ^ i) := by
      intro i
      simp only [hf]
      split_ifs
      · rw [← pow_add, one_div_pow, div_mul_div_comm, one_mul]
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        rw [add_comm (n + 1) i]
        have : ((n : ℝ) + 1) ≤ (i : ℝ) + (n + 1) := by have : (0:ℝ) ≤ i := by positivity
                                                       linarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
      · positivity
    have hgs : Summable fun i : ℕ => 1 / ((n : ℝ) + 1) * ((1 / 2) ^ (n + 1) * (1 / 2) ^ i) :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_left _
    have := Summable.tsum_le_tsum hb htail_sum hgs
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two] at this
    calc (2 : ℝ) ^ n * ∑' i, f (i + (n + 1))
        ≤ 2 ^ n * (1 / (n + 1) * ((1 / 2) ^ (n + 1) * 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (n + 1) := by
          rw [pow_succ, one_div_pow]; field_simp

lemma Rs_succ (S : ℕ → Prop) (n : ℕ) [Decidable (S (n + 1))] :
    Rs S (n + 1) = 2 * Rs S n + if S (n + 1) then 1 / ((n : ℚ) + 1) else 0 := by
  classical
  unfold Rs
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    split_ifs
    · rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]; ring
    · simp
  · simp only [Nat.sub_self, pow_zero]
    split_ifs <;> push_cast <;> ring

/-- **N6.**  `R_{n+t} = 2^t R_n` when `S` misses `(n, n+t]`. -/
theorem Rs_shift (S : ℕ → Prop) (n t : ℕ) (h : ∀ j, n < j → j ≤ n + t → ¬ S j) :
    Rs S (n + t) = 2 ^ t * Rs S n := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← add_assoc, Rs_succ, ih (fun j h1 h2 => h j h1 (by omega)),
      if_neg (h _ (by omega) (by omega))]
    ring

end NormalNumbers.GrowingLocalizedLog
