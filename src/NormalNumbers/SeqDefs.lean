/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Sequence-level normality

Normality of an abstract digit sequence `s : ℕ → ℕ` in base `b`: every
nonempty block of digits `< b` occurs with asymptotic frequency `b⁻ᵏ`.

These two definitions are aligned, by design, with
`OldMathematician/ChampernowneNormality` (Apache 2.0), which proves
`IsNormalSequence b (champDigit b)` for every `b ≥ 2` — keeping the shapes
identical makes results interoperable across the two projects.
-/

namespace NormalNumbers

/-- Number of (overlapping) occurrences of `w` as a contiguous block of `l`.

`l.tails` yields the suffixes starting at positions `0, 1, …, l.length`; a
tail shorter than `w` never satisfies `w.isPrefixOf`, so the windows counted
are exactly the start positions `0 … l.length - w.length`.  Callers always
pass `w ≠ []` (the empty word is a prefix of every tail). -/
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)

/-- Comparator non-vacuity anchor: overlapping occurrences are counted separately. -/
theorem countOccurrences_overlap_anchor :
    countOccurrences [0, 0] [0, 0, 0] = 2 := by
  decide +kernel

/-- Normality of a digit sequence in base `b`: every nonempty block of
length `k` (entries `< b`, leading zeros allowed) occurs among the first `n`
terms with frequency tending to `b⁻ᵏ`. -/
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)

end NormalNumbers
