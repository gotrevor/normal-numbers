/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFBlockFreq
import NormalNumbers.Counting

/-!
# W5 groundwork — orbit block counts vs digit-word window counts

`chebyshev_blockCount_brick` (W4) controls the *orbit* count
`blockCount (cfCylinder v) n (T^s x)`; the refinement discrepancy of
Definition 11 is about the *finite digit word* via `countOccurrences`.
This file bridges the two for points whose Gauss orbit stays in `(0,1)`:

* `blockCount_eq_card_matches` — the orbit count is the number of matched
  windows of `v` in the digit stream starting at offset `s`;
* `blockCount_sub_countOccurrences_bounds` — the orbit count and the
  fitting-window count of `v` in the length-`n` digit word differ by at
  most `|v|` boundary windows.

Everything is pointwise counting; the only analytic fact used is that
cylinder membership is digit-defined.
-/

namespace NormalNumbers

open Finset

/-- On a full orbit, membership of `T^m x` in a cylinder is a digit-window
match at offset `m`. -/
theorem iterate_mem_cfCylinder_iff {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (m : ℕ) :
    gaussMap^[m] x ∈ cfCylinder v ↔ MatchesAt (cfDigit x) v m := by
  rw [cfCylinder]
  constructor
  · rintro ⟨-, hdig⟩ j hj
    have := hdig j hj
    rwa [cfDigit, ← Function.iterate_add_apply, Nat.add_comm j m] at this
  · intro hmatch
    refine ⟨horb m, fun j hj => ?_⟩
    have := hmatch j hj
    rwa [cfDigit, ← Function.iterate_add_apply, Nat.add_comm j m]

/-- The orbit block count is a cardinality of matched windows in the digit
stream. -/
theorem blockCount_eq_card_matches {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (s n : ℕ) :
    blockCount (cfCylinder v) n (gaussMap^[s] x)
      = (((Finset.range n).filter
          (fun j => MatchesAt (cfDigit x) v (s + j))).card : ℝ) := by
  rw [blockCount_apply]
  have hterm : ∀ k : ℕ,
      blockIndic (cfCylinder v) (gaussMap^[k] (gaussMap^[s] x))
        = if MatchesAt (cfDigit x) v (s + k) then (1 : ℝ) else 0 := by
    intro k
    rw [← Function.iterate_add_apply, Nat.add_comm k s]
    rw [blockIndic]
    by_cases h : gaussMap^[s + k] x ∈ cfCylinder v
    · rw [Set.indicator_of_mem h,
        if_pos ((iterate_mem_cfCylinder_iff horb v (s + k)).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        if_neg (fun hm => h ((iterate_mem_cfCylinder_iff horb v (s + k)).2 hm))]
  simp only [hterm]
  rw [Finset.sum_boole]

/-- **The bridge**: for a full orbit, the orbit block count at offset `s`
and the fitting-window count of `v` in the digit word
`(cfDigit x s, …, cfDigit x (s+n−1))` differ by at most `|v|`. -/
theorem blockCount_sub_countOccurrences_bounds {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (hv : v ≠ []) (s n : ℕ) :
    (countOccurrences v
        ((List.range n).map (fun i => cfDigit x (s + i))) : ℝ)
      ≤ blockCount (cfCylinder v) n (gaussMap^[s] x) ∧
    blockCount (cfCylinder v) n (gaussMap^[s] x)
      ≤ countOccurrences v
          ((List.range n).map (fun i => cfDigit x (s + i))) + v.length := by
  set s' : ℕ → ℕ := fun i => cfDigit x (s + i) with hs'
  have hshift : ∀ j, MatchesAt s' v j ↔ MatchesAt (cfDigit x) v (s + j) := by
    intro j
    constructor <;> intro h i hi
    · have hthis := h i hi
      simp only [hs'] at hthis
      rwa [← Nat.add_assoc] at hthis
    · show cfDigit x (s + (j + i)) = v.getD i 0
      rw [← Nat.add_assoc]
      exact h i hi
  have hcards : ((Finset.range n).filter (fun j => MatchesAt s' v j)).card
      = ((Finset.range n).filter
          (fun j => MatchesAt (cfDigit x) v (s + j))).card := by
    congr 1
    apply Finset.filter_congr
    intro j _
    simp [hshift j]
  obtain ⟨h1, h2⟩ := card_filter_matchesAt_le s' v hv n
  rw [blockCount_eq_card_matches horb v s n, ← hcards]
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

end NormalNumbers
