/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEndgame
import NormalNumbers.AdderCertMain

/-!
# The six-fold adder disjunction (the frozen headline)

Brief: `BRIEF-adder-disjunction-formalization.md` §"The theorem to prove";
discovery: `docs/adder-collapse-hunt-2026-08-29.md`.

**At least one of the following holds**: `00` occurs infinitely often in the
binary expansion of ln 2; `001` in ln 3; `11` in ln 6; `001` in ln 18;
`010` in ln 12; `000` in ln 54.

🧊 The word-to-constant pairing and the six constants are FROZEN (exact
collapse computation, 2026-08-29).  The six constants are the ℤ₊-span
points `a·ln 2 + b·ln 3` for `(a,b) ∈ {(1,0),(0,1),(1,1),(1,2),(2,1),(1,3)}`
(`ln 18 = ln 2 + 2·ln 3`, `ln 12 = 2·ln 2 + ln 3`, `ln 54 = ln 2 + 3·ln 3`).

Proof: negate; the six no-occurrence tails let the true carry/window state
walk the certified 73728-state automaton forever (`famState_shadow`), whose
certificate forces eventual periodicity of the input digits
(`input_eventually_periodic`), making ln 2 rational — contradicting
`irrational_log_two`.  Phase-1 tier: the main certificate is checked by
`native_decide` (`Lean.ofReduceBool` disclosed); everything else is
kernel-tier.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Sanity anchor (brief §freezing): ln 2 = 0.10110001…₂, so `00` first
occurs at digit positions 4,5. -/
example : OccursAt 2 (Real.log 2) [0, 0] 4 := by
  have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hu : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hfr : Int.fract (Real.log 2) = Real.log 2 := by
    rw [Int.fract_eq_self]
    constructor <;> nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  unfold digitOf
  rw [hfr]
  interval_cases j
  · have h32 : ⌊Real.log 2 * ((2:ℕ):ℝ) ^ (4 + 0 + 1)⌋ = 22 := by
      apply Int.floor_eq_iff.2
      constructor <;> push_cast <;> nlinarith
    rw [h32]
    rfl
  · have h64 : ⌊Real.log 2 * ((2:ℕ):ℝ) ^ (4 + 1 + 1)⌋ = 44 := by
      apply Int.floor_eq_iff.2
      constructor <;> push_cast <;> nlinarith
    rw [h64]
    rfl

/-- **The six-fold adder disjunction.** -/
theorem adder_sixfold_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 2) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 3) [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 6) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 18) [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 12) [0, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 54) [0, 0, 0] n) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hcon
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  obtain ⟨N₃, hN₃⟩ := h₃
  obtain ⟨N₄, hN₄⟩ := h₄
  obtain ⟨N₅, hN₅⟩ := h₅
  obtain ⟨N₆, hN₆⟩ := h₆
  have hlog2 : (2:ℝ) ≠ 0 := by norm_num
  have hlog3 : (3:ℝ) ≠ 0 := by norm_num
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num, Real.log_mul hlog2 hlog3]
  have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18:ℝ) = 2 * 3 ^ 2 from by norm_num, Real.log_mul hlog2 (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 from by norm_num, Real.log_mul (by norm_num) hlog3,
      Real.log_pow]
    push_cast; ring
  have h54 : Real.log 54 = Real.log 2 + 3 * Real.log 3 := by
    rw [show (54:ℝ) = 2 * 3 ^ 3 from by norm_num, Real.log_mul hlog2 (by norm_num),
      Real.log_pow]
    push_cast; ring
  refine no_occurrence_contradiction mainFamily (by decide) main_cert_ok
    (Real.log 2) (Real.log 3) irrational_log_two
    (by decide) (by decide) (by decide) ?_
  intro ch hch
  fin_cases hch
  · refine ⟨N₁, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((0:ℕ):ℝ) * Real.log 3) [0, 0] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((0:ℕ):ℝ) * Real.log 3 = Real.log 2 from by
      push_cast; ring]
    exact hN₁ n hn
  · refine ⟨N₂, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((0:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3) [0, 0, 1] n
    rw [show ((0:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3 = Real.log 3 from by
      push_cast; ring]
    exact hN₂ n hn
  · refine ⟨N₃, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3) [1, 1] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3 = Real.log 6 from by
      push_cast; rw [h6]; ring]
    exact hN₃ n hn
  · refine ⟨N₄, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((2:ℕ):ℝ) * Real.log 3) [0, 0, 1] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((2:ℕ):ℝ) * Real.log 3 = Real.log 18 from by
      push_cast; rw [h18]; ring]
    exact hN₄ n hn
  · refine ⟨N₅, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((2:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3) [0, 1, 0] n
    rw [show ((2:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3 = Real.log 12 from by
      push_cast; rw [h12]; ring]
    exact hN₅ n hn
  · refine ⟨N₆, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((3:ℕ):ℝ) * Real.log 3) [0, 0, 0] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((3:ℕ):ℝ) * Real.log 3 = Real.log 54 from by
      push_cast; rw [h54]; ring]
    exact hN₆ n hn

end NormalNumbers.Adder
