/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SeqDefs

/-!
# Occurrence counts as index-set cardinalities

`countOccurrences w l` is defined by scanning `l.tails`.  For Wall's theorem
we need it as the cardinality of a set of *starting positions*, so that block
occurrences in a digit sequence can be compared with orbit visits to a b-adic
interval.  `MatchesAt s w i` is the window-match predicate; the two headline
results are `countOccurrences_range_map` (the exact reindexing) and the
two-sided comparison with the unclipped count (`card_filter_matchesAt`
bounds), whose gap is at most `w.length` boundary windows.
-/

namespace NormalNumbers

/-- The block `w` occurs in the sequence `s` starting at position `i`. -/
def MatchesAt (s : ℕ → ℕ) (w : List ℕ) (i : ℕ) : Prop :=
  ∀ j < w.length, s (i + j) = w.getD j 0

instance MatchesAt.decidable (s : ℕ → ℕ) (w : List ℕ) (i : ℕ) :
    Decidable (MatchesAt s w i) :=
  Nat.decidableBallLT _ _

/-- `tails` is `drop` at every index. -/
theorem tails_eq_map_drop {α : Type*} (l : List α) :
    l.tails = (List.range (l.length + 1)).map l.drop := by
  apply List.ext_getElem
  · simp [List.length_tails]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← List.get_tails l ⟨i, h1⟩]
    rfl

/-- `countOccurrences` as a cardinality of starting positions. -/
theorem countOccurrences_eq_card (w l : List ℕ) :
    countOccurrences w l
      = ((Finset.range (l.length + 1)).filter
          (fun i => w.isPrefixOf (l.drop i))).card := by
  rw [countOccurrences, tails_eq_map_drop, List.countP_map]
  rw [List.countP_eq_length_filter]
  rw [Finset.card_filter]
  induction (l.length + 1) with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, List.range_succ, List.filter_append,
        List.length_append, ih]
      by_cases h : w <+: List.drop n l <;>
        simp [List.isPrefixOf_iff_prefix, h]

/-- Window match through `map` over `range`: `w` is a prefix of the digits
from position `i` iff the window fits and matches pointwise. -/
theorem isPrefixOf_range_map {s : ℕ → ℕ} {w : List ℕ} {n i : ℕ} (hi : i ≤ n) :
    w.isPrefixOf (((List.range n).map s).drop i)
      ↔ i + w.length ≤ n ∧ MatchesAt s w i := by
  rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  constructor
  · intro h
    have hlen : w.length ≤ n - i := by
      have := congrArg List.length h
      simp only [List.length_take, List.length_drop, List.length_map,
        List.length_range] at this
      omega
    refine ⟨by omega, ?_⟩
    intro j hj
    have hin : i + j < n := by omega
    have hval : w.getD j 0 = s (i + j) := by
      conv_lhs => rw [h]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
        List.getElem?_drop]
      simp [hin]
    exact hval.symm
  · rintro ⟨hfit, hmatch⟩
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_map,
        List.length_range]
      omega
    · intro j h1 h2
      rw [List.getElem_take, List.getElem_drop]
      have hin : i + j < n := by omega
      have hj : j < w.length := h1
      simp only [List.getElem_map, List.getElem_range]
      rw [hmatch j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl

/-- The exact reindexing: occurrences of `w` in the first `n` digits of `s`
are the fitting matched windows. -/
theorem countOccurrences_range_map (s : ℕ → ℕ) (w : List ℕ) (n : ℕ) :
    countOccurrences w ((List.range n).map s)
      = ((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ MatchesAt s w i)).card := by
  rw [countOccurrences_eq_card]
  simp only [List.length_map, List.length_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [isPrefixOf_range_map hi']

/-- Clipped vs unclipped window counts differ by at most `w.length`
boundary windows. -/
theorem card_filter_matchesAt_le (s : ℕ → ℕ) (w : List ℕ) (hw : w ≠ [])
    (n : ℕ) :
    countOccurrences w ((List.range n).map s)
        ≤ ((Finset.range n).filter (MatchesAt s w)).card ∧
      ((Finset.range n).filter (MatchesAt s w)).card
        ≤ countOccurrences w ((List.range n).map s) + w.length := by
  have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  rw [countOccurrences_range_map]
  constructor
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, hi.2.2⟩
  · have hsplit : (Finset.range n).filter (MatchesAt s w)
        ⊆ ((Finset.range (n + 1)).filter
            (fun i => i + w.length ≤ n ∧ MatchesAt s w i))
          ∪ Finset.Ico (n + 1 - w.length) n := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
        Finset.mem_Ico] at hi ⊢
      by_cases hfit : i + w.length ≤ n
      · exact Or.inl ⟨by omega, hfit, hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    calc ((Finset.range n).filter (MatchesAt s w)).card
        ≤ (((Finset.range (n + 1)).filter
              (fun i => i + w.length ≤ n ∧ MatchesAt s w i))
            ∪ Finset.Ico (n + 1 - w.length) n).card :=
          Finset.card_le_card hsplit
      _ ≤ ((Finset.range (n + 1)).filter
              (fun i => i + w.length ≤ n ∧ MatchesAt s w i)).card
            + (Finset.Ico (n + 1 - w.length) n).card :=
          Finset.card_union_le _ _
      _ ≤ ((Finset.range (n + 1)).filter
              (fun i => i + w.length ≤ n ∧ MatchesAt s w i)).card
            + w.length := by
          rw [Nat.card_Ico]
          omega

/-- Counts that differ by a bounded number of boundary windows have the same
asymptotic frequency. -/
theorem tendsto_div_of_bounded_diff {A B : ℕ → ℕ} {C : ℕ} {L : ℝ}
    (hAB : ∀ n, A n ≤ B n) (hBA : ∀ n, B n ≤ A n + C)
    (h : Filter.Tendsto (fun n => (A n : ℝ) / n) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => (B n : ℝ) / n) Filter.atTop (nhds L) := by
  have hupper : Filter.Tendsto (fun n : ℕ => (A n : ℝ) / n + C / n)
      Filter.atTop (nhds L) := by
    have hC : Filter.Tendsto (fun n : ℕ => (C : ℝ) / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
    simpa using h.add hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h hupper ?_ ?_
  · intro n
    dsimp only
    gcongr
    exact_mod_cast hAB n
  · intro n
    dsimp only
    rw [← add_div]
    gcongr
    exact_mod_cast hBA n

end NormalNumbers
