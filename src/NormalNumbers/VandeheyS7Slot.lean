/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SL: the block average is a SLOT average — one emission, one test

`BlockAverageBound` is stated over the whole emitted block `[N n, N (n+1))`, which invites the
reader to think of a burst of output digits being tested against the target word `w` at every
offset `j`.  For the run that is an illusion: the transducer emits **at most one digit per input
step** (`runWord_length_le_one`), so `N (n+1) − N n ∈ {0,1}` and the inner sum has at most one
term, namely `j = 0`.

This module cashes that in.  Writing `emitIndic Φ x n = (runWord Φ x n).length ∈ {0,1}` for the
indicator of "step `n` emits", the block average is exactly

    slotCount Φ x w p  =  Σ_{n<p} emitIndic n · 1[ Gⁿx ∈ mapBlockSet (runState Φ x n) w 0 ]

and `runClock Φ x p = Σ_{n<p} emitIndic n`.  So **`BlockAverageBound B` says precisely**

    #{n < p : step n emits AND Gⁿx ∈ s_n⁻¹(I_w)}  ≤  (B + ε) · #{n < p : step n emits} ,

a *relative* frequency among emission times, with no block structure left in it
(`blockAverageBound_iff_slot`).  This is the shape `ClassFreqBound` must be stated in: the
state cell `s_n ∈ B_i` and the orbit point `Gⁿx ∈ E_i` tested at ONE time, against the emission
count rather than against `p`.
-/
import NormalNumbers.VandeheyS7RunPin

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- The indicator of "step `n` emits a digit", as a real number. -/
noncomputable def emitIndic (Φ : MapState) (x : ℝ) (n : ℕ) : ℝ :=
  ((runWord Φ x n).length : ℝ)

lemma emitIndic_eq_zero_or_one (Φ : MapState) (x : ℝ) (n : ℕ) :
    emitIndic Φ x n = 0 ∨ emitIndic Φ x n = 1 := by
  have h := runWord_length_le_one Φ x n
  interval_cases hL : (runWord Φ x n).length
  · left; simp [emitIndic, hL]
  · right; simp [emitIndic, hL]

lemma emitIndic_nonneg (Φ : MapState) (x : ℝ) (n : ℕ) : 0 ≤ emitIndic Φ x n := by
  rcases emitIndic_eq_zero_or_one Φ x n with h | h <;> rw [h] <;> norm_num

/-- The emission count IS the clock. -/
lemma runClock_eq_sum_emitIndic (Φ : MapState) (x : ℝ) (p : ℕ) :
    ((runClock Φ x p : ℕ) : ℝ) = ∑ n ∈ range p, emitIndic Φ x n := by
  rw [runClock]
  push_cast
  rfl

/-- The number of output digits tested at input step `n`. -/
lemma runClock_sub (Φ : MapState) (x : ℝ) (n : ℕ) :
    runClock Φ x (n + 1) - runClock Φ x n = (runWord Φ x n).length := by
  rw [runClock_succ]; omega

/-- **One emission, one test.**  The whole block sum at step `n` collapses to the `j = 0` slot. -/
theorem blockHitCount_run_eq (Φ : MapState) (x : ℝ) (w : List ℕ) (n : ℕ) (z : ℝ) :
    blockHitCount (fun j => mapBlockSet (runState Φ x n) w j)
        (runClock Φ x (n + 1) - runClock Φ x n) z
      = emitIndic Φ x n * blockIndic (mapBlockSet (runState Φ x n) w 0) z := by
  rw [runClock_sub, blockHitCount, emitIndic]
  have h := runWord_length_le_one Φ x n
  interval_cases hL : (runWord Φ x n).length
  · simp
  · simp

/-- The slot count: emission times at which the current orbit point lands in the pulled-back
target cylinder. -/
noncomputable def slotCount (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) : ℝ :=
  ∑ n ∈ range p, emitIndic Φ x n * blockIndic (mapBlockSet (runState Φ x n) w 0) (gaussMap^[n] x)

theorem sum_blockHitCount_eq_slotCount (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) :
    (∑ n ∈ range p, blockHitCount (fun j => mapBlockSet (runState Φ x n) w j)
        (runClock Φ x (n + 1) - runClock Φ x n) (gaussMap^[n] x))
      = slotCount Φ x w p := by
  rw [slotCount]
  exact Finset.sum_congr rfl fun n _ => blockHitCount_run_eq Φ x w n _

/-- **S7-SL.**  `BlockAverageBound` for the run is exactly a relative-frequency statement
among emission times. -/
theorem blockAverageBound_iff_slot (Φ : MapState) (x : ℝ) (w : List ℕ) (B : ℝ) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j)
      ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop,
          slotCount Φ x w p ≤ (B + ε) * ((runClock Φ x p : ℕ) : ℝ) := by
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with p hp
    rwa [sum_blockHitCount_eq_slotCount] at hp
  · intro h ε hε
    filter_upwards [h ε hε] with p hp
    rwa [sum_blockHitCount_eq_slotCount]

/-- The slot count never exceeds the clock: at most one hit per emission. -/
theorem slotCount_le_runClock (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) :
    slotCount Φ x w p ≤ ((runClock Φ x p : ℕ) : ℝ) := by
  rw [slotCount, runClock_eq_sum_emitIndic]
  refine Finset.sum_le_sum fun n _ => ?_
  have hind : blockIndic (mapBlockSet (runState Φ x n) w 0) (gaussMap^[n] x) ≤ 1 := by
    rw [blockIndic]
    by_cases hm : gaussMap^[n] x ∈ mapBlockSet (runState Φ x n) w 0
    · simp [Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hm]
  have hnn : 0 ≤ emitIndic Φ x n := emitIndic_nonneg Φ x n
  nlinarith

lemma slotCount_nonneg (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) : 0 ≤ slotCount Φ x w p := by
  refine Finset.sum_nonneg fun n _ => ?_
  refine mul_nonneg (emitIndic_nonneg Φ x n) ?_
  exact Set.indicator_nonneg (by intro _ _; norm_num) _

end MapState

section Audit

#print axioms MapState.blockHitCount_run_eq
#print axioms MapState.sum_blockHitCount_eq_slotCount
#print axioms MapState.blockAverageBound_iff_slot
#print axioms MapState.slotCount_le_runClock

end Audit

end NormalNumbers.VandeheyS7
