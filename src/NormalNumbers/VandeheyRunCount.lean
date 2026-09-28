/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyRunBound
import NormalNumbers.VandeheyLRPattern

/-!
# The emitted CF-digit count is at most linear (the upper half of Lemma 6.1)

## The structural finding this file records

The rescaling between the transducer's clock (input CF digits, `n`) and the image's CF index
must be done through the number of emitted **runs**, never the number of emitted **letters**.
The letter count is `Σ_{i<n} cfDigit`-shaped, and the Gauss measure has INFINITE digit mean, so
for a.e. input the letter count per input digit diverges:

  `(lrPos w n)/n → ∞`  a.e.,   while   `(runs of the emitted word)/n → c ∈ (0,∞)`.

That is why Vandehey's Lemma 6.1 is about CF digits, and why `VandeheyLRPattern`'s bijection is
the right interface: it converts a count of `L/R` pattern occurrences into a count of CF INDICES,
and the only rescaling left is by the run count.

## What is proved here

`numAlt_lrWord_le`: the emitted word has at most `(2D+1)·n` alternations after `n` input digits,
so at most `(2D+1)·n + 1` runs.  This is Lemma 2.2 summed over the blocks, and it is the upper
half of Lemma 6.1.  The lower bound — that the run count grows at least linearly — is the one
remaining analytic leaf; see `PENDING_WORK.md`.
-/

namespace NormalNumbers.VandeheyLR

open Mat2 VandeheyOut VandeheyAut

variable {α : Type*} [DecidableEq α]

/-- Concatenation can create at most one new alternation, at the seam. -/
lemma numAlt_append_le : ∀ (u v : List α), numAlt (u ++ v) ≤ numAlt u + numAlt v + 1
  | [], v => by simp
  | [x], v => by simpa using numAlt_cons_le x v
  | (x :: y :: u), v => by
      have ih := numAlt_append_le (y :: u) v
      rw [List.cons_append] at ih
      rw [List.cons_append, List.cons_append, numAlt, numAlt]
      split <;> omega

variable {D : ℕ}

/-- **The upper half of Lemma 6.1.**  After `n` input digits the emitted `L/R` word has at most
`(2D+1)·n` alternations — hence at most that many emitted CF digits, up to one.  The bound is
Lemma 2.2 (`numAlt_lrOut_le_two_mul`) summed over the blocks, with one alternation per seam. -/
theorem numAlt_lrWord_le (hD : 0 < D) (s₀ : RState D) (x : ℝ) (n : ℕ) :
    numAlt (lrWord hD s₀ x n) ≤ (2 * D + 1) * n := by
  induction n with
  | zero => simp [lrWord]
  | succ n ih =>
    rw [lrWord_succ]
    have h1 := numAlt_append_le (lrWord hD s₀ x n)
      (lrOut hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n))
    have h2 := numAlt_lrOut_le_two_mul hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n)
    have h3 : (2 * D + 1) * (n + 1) = (2 * D + 1) * n + (2 * D + 1) := by ring
    omega

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms numAlt_append_le
#print axioms numAlt_lrWord_le
end
