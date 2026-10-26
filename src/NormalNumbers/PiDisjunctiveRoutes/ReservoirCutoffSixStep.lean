/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSix

/-! # Exact reservoir/residual recurrence at a general cutoff `s·n`

`R^s_{n+1} = 16 R^s_n − E^s_n + I^s_n`, `S^s_{n+1} = 16 S^s_n + E^s_n + 16·kick_n − I^s_n`.
The exit `E^s_n` enters along `(−1, +1)` and cancels in `R+S = 16ⁿ·piPartial n`
(`reservoirS_add_residualS`), whose recurrence involves only the BBP kick.  For
`s = 6` the exit is `rationalExit 6 n` (`exitS_six_eq`), so the arithmetic of
`exit_six_not_eventually_small` acts only on the fixed-sum fiber.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

noncomputable def reservoirS (s n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (16 : ℝ) ^ (n - j) *
    ((if Nat.Prime (8 * j + 1) ∧ s * n < 8 * j + 1 then 4 / (8 * (j : ℝ) + 1) else 0) -
     (if Nat.Prime (8 * j + 5) ∧ s * n < 8 * j + 5 then 1 / (8 * (j : ℝ) + 5) else 0))

noncomputable def residualS (s n : ℕ) : ℝ := (16 : ℝ) ^ n * piPartial n - reservoirS s n

noncomputable def exitS (s n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, reservoirTerm (fun m => s * n < m ∧ m ≤ s * (n + 1)) (n + 1 - j) j

noncomputable def entryS (s n : ℕ) : ℝ := reservoirTerm (fun m => s * (n + 1) < m) 1 n

theorem reservoirS_succ (s n : ℕ) :
    reservoirS s (n + 1) = 16 * reservoirS s n - exitS s n + entryS s n := by
  rw [reservoirS, Finset.sum_range_succ, entryS, reservoirS, exitS, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  have hs : s * (n + 1) = s * n + s := by ring
  simp only [hs]
  generalize s * n = a
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < n := Finset.mem_range.1 hj
    rw [reservoirTerm, show n + 1 - j = (n - j) + 1 by omega, pow_succ]
    by_cases hA : Nat.Prime (8 * j + 1) <;> by_cases hB : Nat.Prime (8 * j + 5) <;>
      simp only [hA, hB, true_and, false_and, if_false] <;> (try split_ifs) <;>
        first | omega | ring
  · rw [reservoirTerm, Nat.add_sub_cancel_left, pow_one]

theorem residualS_succ (s n : ℕ) :
    residualS s (n + 1) = 16 * residualS s n + exitS s n + 16 * bbpKick n - entryS s n := by
  rw [residualS, residualS, reservoirS_succ, piPartial, piPartial,
    Finset.sum_range_succ, bbpTerm]
  have h : (16 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

/-- The sum direction sees no exit: `R + S = 16ⁿ·piPartial n` for every cutoff. -/
theorem reservoirS_add_residualS (s n : ℕ) :
    reservoirS s n + residualS s n = (16 : ℝ) ^ n * piPartial n := by
  rw [residualS]; ring

/-- The difference direction carries twice the exit. -/
theorem sub_succ (s n : ℕ) :
    reservoirS s (n + 1) - residualS s (n + 1) =
      16 * (reservoirS s n - residualS s n) - 2 * exitS s n + 2 * entryS s n
        - 16 * bbpKick n := by
  rw [reservoirS_succ, residualS_succ]; ring

theorem exitS_six_eq (n : ℕ) : exitS 6 n = (CutoffReview.rationalExit 6 n : ℝ) := by
  rw [exitS, CutoffReview.rationalExit]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [reservoirTerm]
  split_ifs <;> push_cast <;> ring

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
