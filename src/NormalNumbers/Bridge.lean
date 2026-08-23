/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# The sequence ↔ real bridge

A digit sequence that does not eventually stick at `b − 1` is recovered
exactly by the digit map of the real number it sums to.  This is the lemma
that upgrades any *sequence*-normality theorem (e.g. Champernowne's) to a
statement about the corresponding *real number*.
-/

namespace NormalNumbers

/-- A digit sequence is **proper** if it does not eventually stick at
`b − 1`: past every index there is a digit `≠ b − 1`.  (The improper
expansion `0.d₁…dₖ(b−1)(b−1)…` denotes the same real as a terminating one,
and the digit map recovers the terminating form instead.) -/
def ProperDigits (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1

theorem realOfDigits_mem_Ico (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) :
    realOfDigits b s ∈ Set.Ico (0 : ℝ) 1 := by
  sorry

/-- **The bridge**: the digit map inverts `realOfDigits` on proper digit
sequences. -/
theorem digitOf_realOfDigits (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) :
    digitOf b (realOfDigits b s) = s := by
  sorry

/-- Sequence normality upgrades to real-number normality along the bridge. -/
theorem isNormal_realOfDigits (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s)
    (hn : IsNormalSequence b s) : IsNormal b (realOfDigits b s) := by
  sorry

end NormalNumbers
