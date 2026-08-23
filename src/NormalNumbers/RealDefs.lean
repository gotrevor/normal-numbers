/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SeqDefs

/-!
# Real-number normality and equidistribution

The digit map `digitOf b x i = ⌊b^(i+1)·x⌋ mod b` reads off the standard
base-`b` expansion of `x ∈ [0,1)` (the expansion that does not end in an
infinite tail of `b − 1`s).  A real is *normal in base `b`* when the digit
sequence of its fractional part is a normal sequence.

`Equidistributed` is equidistribution mod 1 stated with interval visit
frequencies (Weyl); `orbit b x` is the multiply-by-`b` orbit `b^n·x mod 1`
that Wall's theorem connects to normality.
-/

namespace NormalNumbers

/-- The `i`-th digit (0-indexed) of the standard base-`b` expansion of
`x ∈ [0,1)`: `⌊b^(i+1)·x⌋ mod b`.  Total function; junk values outside
`[0,1)` (normality of `x` is always read through `Int.fract x`). -/
noncomputable def digitOf (b : ℕ) (x : ℝ) (i : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (i + 1)⌋).toNat % b

/-- A real number is **normal in base `b`** iff the digit sequence of its
fractional part is a normal sequence. -/
def IsNormal (b : ℕ) (x : ℝ) : Prop :=
  IsNormalSequence b (digitOf b (Int.fract x))

/-- The real number in `[0,1]` whose base-`b` digit sequence is `s`. -/
noncomputable def realOfDigits (b : ℕ) (s : ℕ → ℕ) : ℝ :=
  ∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)

open Classical in
/-- Visits of the first `n` terms of `u` to the interval `[a, c)`. -/
noncomputable def visitCount (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k => u k ∈ Set.Ico a c).card

/-- Equidistribution mod 1 of a sequence (intended for sequences valued in
`[0,1)`): the visit frequency of every subinterval `[a, c) ⊆ [0, 1)` tends
to its length. -/
def Equidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    Filter.Tendsto (fun n => (visitCount u a c n : ℝ) / n)
      Filter.atTop (nhds (c - a))

/-- The multiply-by-`b` orbit of `x` on the circle: `n ↦ b^n·x mod 1`. -/
noncomputable def orbit (b : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  Int.fract (x * (b : ℝ) ^ n)

end NormalNumbers
