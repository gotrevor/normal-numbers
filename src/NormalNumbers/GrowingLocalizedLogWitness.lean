/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# An admissible unbounded `Y` for `ζ_Y`

`witnessY n = max 3 (log₂ log₂ log₂ n)`, with integer logarithms.  It is monotone, at least 3,
tends to infinity, and eventually `π(witnessY n) ≤ witnessY n ≤ ½ log₂ log n`
(`witnessY_admissible`).  This discharges `exists_unbounded_zetaY`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Filter

/-- `max 3 (log₂ log₂ log₂ n)`. -/
def witnessY (n : ℕ) : ℕ := max 3 (Nat.log 2 (Nat.log 2 (Nat.log 2 n)))

lemma primeCounting_le_self (n : ℕ) : n.primeCounting ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
  calc (Finset.filter Nat.Prime (Finset.range (n + 1))).card ≤ (Finset.Icc 1 n).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        simp only [Finset.mem_Icc]; exact ⟨hp.2.one_lt.le, by omega⟩
    _ = n := by simp

lemma witnessY_mono : Monotone witnessY := fun _ _ h =>
  max_le_max le_rfl (Nat.log_mono_right (Nat.log_mono_right (Nat.log_mono_right h)))

lemma three_le_witnessY (n : ℕ) : 3 ≤ witnessY n := le_max_left _ _

lemma tendsto_log2 : Tendsto (Nat.log 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun k => ⟨2 ^ k, fun n hn => Nat.le_log_of_pow_le (by norm_num) hn⟩

lemma witnessY_tendsto : Tendsto witnessY atTop atTop :=
  tendsto_atTop_mono (fun _ => le_max_right _ _)
    (tendsto_log2.comp (tendsto_log2.comp tendsto_log2))

lemma two_mul_add_one_le_two_pow {c : ℕ} (hc : 3 ≤ c) : 2 * c + 1 ≤ 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih => rw [pow_succ]; omega

theorem witnessY_admissible : ∀ᶠ n : ℕ in atTop,
    ((witnessY n).primeCounting : ℝ) ≤ (1 / 2) * Real.logb 2 (Real.log n) := by
  have hb : ∀ᶠ n : ℕ in atTop, 7 ≤ Nat.log 2 (Nat.log 2 n) :=
    (tendsto_log2.comp tendsto_log2).eventually_ge_atTop 7
  filter_upwards [hb] with n hb
  set a := Nat.log 2 n
  set b := Nat.log 2 a
  set c := Nat.log 2 b
  have ha0 : a ≠ 0 := by intro h; simp [b, h] at hb
  have hn0 : n ≠ 0 := by intro h; simp [a, h] at ha0
  have h1 : 2 ^ a ≤ n := Nat.pow_log_le_self 2 hn0
  have h2 : 2 ^ b ≤ a := Nat.pow_log_le_self 2 ha0
  have h3 : 2 ^ c ≤ b := Nat.pow_log_le_self 2 (by omega)
  -- `log₂ log n ≥ b − 1`
  have hlog2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlogn : (2 : ℝ) ^ b * Real.log 2 ≤ Real.log n := by
    have e1 : ((2 : ℝ) ^ b) ≤ a := by exact_mod_cast h2
    have e2 : (a : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
    nlinarith
  have hu : (b : ℝ) - 1 ≤ Real.logb 2 (Real.log n) := by
    have hpos : 0 < (2 : ℝ) ^ b * Real.log 2 := by positivity
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hlogn
    refine le_trans ?_ this
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_self_eq_one
      (by norm_num), mul_one]
    have : -1 < Real.logb 2 (Real.log 2) := by
      rw [show (-1 : ℝ) = Real.logb 2 (1 / 2) by
        rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]]
      exact Real.logb_lt_logb (by norm_num) (by norm_num) (by linarith)
    linarith
  have hY : (witnessY n : ℝ) ≤ ((b : ℝ) - 1) / 2 := by
    have : 2 * witnessY n + 1 ≤ b := by
      show 2 * max 3 c + 1 ≤ b
      rcases le_or_gt c 3 with hc | hc
      · rw [max_eq_left hc]; omega
      · rw [max_eq_right (by omega)]
        exact (two_mul_add_one_le_two_pow hc.le).trans h3
    have : (2 * witnessY n + 1 : ℝ) ≤ b := by exact_mod_cast this
    linarith
  calc ((witnessY n).primeCounting : ℝ) ≤ witnessY n := by
        exact_mod_cast primeCounting_le_self _
    _ ≤ _ := by linarith

end NormalNumbers.GrowingLocalizedLog
