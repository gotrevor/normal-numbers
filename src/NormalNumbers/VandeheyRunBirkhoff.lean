/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyRunCount

/-!
# The emitted RUN count is a Birkhoff sum (the clock of Lemma 6.1)

`VandeheyRunCount` records the structural finding: the rescaling between the transducer's clock
and the image's CF index must go through the number of emitted **runs**, never the number of
emitted **letters** (the Gauss measure has infinite digit mean, so the letter count per input
digit diverges a.e.).

The run count is `numAlt (lrWord …) + 1`, and `numAlt` of a concatenation splits at the seam —
*provided one remembers the last emitted letter*.  So augment the state with that letter:

    `lrB (M, b) j = (lrDelta M j, last letter of lrOut M j, defaulting to b)`
    `altOut (M, b) j = numAlt (b :: lrOut M j)`     (≤ 2D + 1, Lemma 2.2)

and then

    `numAlt (b₀ :: lrWord hD s₀ x n) = Σ_{i<n} altOut (stateAt lrB (s₀,b₀) x i) (cfDigit x i)`

(`numAlt_lrWord_eq_sum`).  That is exactly the shape `VandeheyOut.tendsto_wCount_div` eats: the
run count is a state-restricted weighted count at window length `1` with a bounded weight, so
Lemma 6.1 for the true clock is a corollary of `JointStateFreq` for the augmented automaton,
just as `VandeheyOutLen.tendsto_outLen_div` is for the letter clock.
-/

namespace NormalNumbers.VandeheyLR

open Mat2 VandeheyOut VandeheyAut

variable {α : Type*} [DecidableEq α]

/-- **The seam identity.**  `numAlt` is additive over concatenation once the left word's last
letter is prepended to the right word. -/
lemma numAlt_append_eq : ∀ (u v : List α) (b : α), u.getLast? = some b →
    numAlt (u ++ v) = numAlt u + numAlt (b :: v)
  | [], _, _, h => by simp at h
  | [x], v, b, h => by
      have hb : x = b := by simpa using h
      subst hb
      simp
  | (x :: y :: t), v, b, h => by
      have h' : (y :: t).getLast? = some b := by simpa using h
      have ih := numAlt_append_eq (y :: t) v b h'
      rw [List.cons_append, List.cons_append] at *
      rw [numAlt, numAlt, ih]
      omega

variable {D : ℕ}

/-- The state augmented with the last emitted letter. -/
noncomputable def lrB (hD : 0 < D) (s : RState D × Bool) (j : ℕ) : RState D × Bool :=
  (lrDelta hD s.1 j, ((lrOut hD s.1 j).getLast?).getD s.2)

/-- The number of runs COMPLETED while ingesting one digit — the increment of the image's CF
index.  Bounded by `2D + 1` (Lemma 2.2). -/
noncomputable def altOut (hD : 0 < D) (s : RState D × Bool) (j : ℕ) : ℕ :=
  numAlt (s.2 :: lrOut hD s.1 j)

lemma altOut_le (hD : 0 < D) (s : RState D × Bool) (j : ℕ) : altOut hD s j ≤ 2 * D + 1 := by
  have h1 : numAlt (s.2 :: lrOut hD s.1 j) ≤ numAlt (lrOut hD s.1 j) + 1 :=
    numAlt_cons_le _ _
  have h2 := numAlt_lrOut_le_two_mul hD s.1 j
  rw [altOut]
  omega

/-- The augmented automaton's first coordinate is the plain Raney state. -/
lemma runState_lrB_fst (hD : 0 < D) (s : RState D × Bool) (w : List ℕ) :
    (runState (lrB hD) s w).1 = runState (lrDelta hD) s.1 w := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih => rw [runState_cons, runState_cons, ih]; rfl

lemma stateAt_lrB_fst (hD : 0 < D) (s : RState D × Bool) (x : ℝ) (i : ℕ) :
    (stateAt (lrB hD) s x i).1 = stateAt (lrDelta hD) s.1 x i :=
  runState_lrB_fst hD s (cfWord x i)

/-- **The augmented Bool IS the last emitted letter.** -/
lemma stateAt_lrB_snd (hD : 0 < D) (s₀ : RState D) (b₀ : Bool) (x : ℝ) (n : ℕ) :
    ((b₀ :: lrWord hD s₀ x n).getLast?).getD b₀ = (stateAt (lrB hD) (s₀, b₀) x n).2 := by
  induction n with
  | zero => simp [lrWord, stateAt, cfWord]
  | succ n ih =>
    have hstep : stateAt (lrB hD) (s₀, b₀) x (n + 1)
        = lrB hD (stateAt (lrB hD) (s₀, b₀) x n) (cfDigit x n) := by
      rw [stateAt, stateAt, cfWord_succ'', runState_append]
      simp [runState]
    rw [hstep, lrB, lrWord_succ, ← List.cons_append]
    have hfst : (stateAt (lrB hD) (s₀, b₀) x n).1 = stateAt (lrDelta hD) s₀ x n :=
      stateAt_lrB_fst hD (s₀, b₀) x n
    rw [hfst]
    cases hlast : (lrOut hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n)).getLast? with
    | none =>
        have : lrOut hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n) = [] :=
          List.getLast?_eq_none_iff.mp hlast
        rw [this]
        simpa using ih
    | some c =>
        simp only [Option.getD_some]
        rw [List.getLast?_append_of_ne_nil, hlast]
        · rfl
        · exact fun hnil => by simp [hnil] at hlast

/-- **The run count is a Birkhoff sum of a bounded window/state function.**  This is the true
clock of Vandehey's Lemma 6.1, and it puts it in the exact shape of
`VandeheyOut.tendsto_wCount_div`. -/
theorem numAlt_lrWord_eq_sum (hD : 0 < D) (s₀ : RState D) (b₀ : Bool) (x : ℝ) (n : ℕ) :
    numAlt (b₀ :: lrWord hD s₀ x n)
      = ∑ i ∈ Finset.range n, altOut hD (stateAt (lrB hD) (s₀, b₀) x i) (cfDigit x i) := by
  induction n with
  | zero => simp [lrWord]
  | succ n ih =>
    rw [lrWord_succ, ← List.cons_append, Finset.sum_range_succ, ← ih]
    have hlast : (b₀ :: lrWord hD s₀ x n).getLast?
        = some ((stateAt (lrB hD) (s₀, b₀) x n).2) := by
      have h := stateAt_lrB_snd hD s₀ b₀ x n
      rcases hc : (b₀ :: lrWord hD s₀ x n).getLast? with _ | c
      · simp at hc
      · rw [hc] at h; rw [← h]; rfl
    rw [numAlt_append_eq _ _ _ hlast, altOut, stateAt_lrB_fst hD (s₀, b₀) x n]

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms numAlt_append_eq
#print axioms stateAt_lrB_snd
#print axioms numAlt_lrWord_eq_sum
end
