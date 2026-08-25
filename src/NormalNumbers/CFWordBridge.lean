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

/-- **Orbit block-count splits at a pinned prefix** (z-transfer conditional core).  For a
full-orbit real `x` and `L ≤ n`, the length-`n` orbit count of `cfCylinder v` from `x` equals
the count of `v`-matches in the FIRST `L` digit windows plus the length-`(n−L)` orbit count from
the SHIFTED orbit `gaussMap^[L] x`.  Pure partition of the window index set `range n = range L ⊎
[L,n)`.  This is the exact decomposition behind the ψ-conditional z-Chebyshev: within a cylinder
that pins the first `L` z-digits, the prefix count is COMMON to all points, so the discrepancy at
scale `n` is driven by the shifted count at scale `n−L` — which `chebyshev_blockCount_brick`
controls with density `O(1/(n−L))` (relative), not the too-weak absolute `O(1/n)`. -/
theorem blockCount_split {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (L n : ℕ) (hLn : L ≤ n) :
    blockCount (cfCylinder v) n x
      = (((Finset.range L).filter (fun j => MatchesAt (cfDigit x) v j)).card : ℝ)
        + blockCount (cfCylinder v) (n - L) (gaussMap^[L] x) := by
  have hx0 : blockCount (cfCylinder v) n x = blockCount (cfCylinder v) n (gaussMap^[0] x) := by
    rw [Function.iterate_zero_apply]
  rw [hx0, blockCount_eq_card_matches horb v 0 n, blockCount_eq_card_matches horb v L (n - L)]
  simp only [Nat.zero_add]
  have hn : n = L + (n - L) := by omega
  have hdisj : Disjoint (Finset.range L) ((Finset.range (n - L)).map (addLeftEmbedding L)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hb
    obtain ⟨k, _, rfl⟩ := hb
    omega
  rw [← Nat.cast_add]
  congr 1
  conv_lhs => rw [hn, Finset.range_add, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_map, Finset.card_map]
  simp only [Function.comp, addLeftEmbedding_apply]

end NormalNumbers
