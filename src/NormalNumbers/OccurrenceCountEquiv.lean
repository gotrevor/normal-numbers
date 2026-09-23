/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SeqDefs

/-!
# The two ways of counting block occurrences agree in the limit

`countOccurrences w l = l.tails.countP (w.isPrefixOf ·)` counts the **suffixes** of `l` that
carry `w` as a prefix, i.e. the start positions `i` with `i + |w| ≤ |l|`.  The other natural
convention — the one used by the independent formalization of Theorem C′ archived under
`archive/findings/` — counts the start positions `i < |l|` whose block matches, reading digits
of the underlying sequence *past* the end of `l`.

These are genuinely different natural numbers, so the faithfulness of the normality statement
depends on them having the same frequency limit.  They do: the counts differ by at most `|w|`
(`countOccurrences_le_occStart`, `occStart_le_countOccurrences_add`), a constant, so dividing
by `n` kills the discrepancy (`tendsto_occStart_iff`).
-/

open Filter Topology

namespace NormalNumbers

/-- Start-position count: the `i < n` at which the block of `|w|` terms of `s` beginning at `i`
equals `w`.  Positions near the right end read `s` beyond index `n`. -/
noncomputable def occStart (w : List ℕ) (s : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => w = (List.range' i w.length).map s)).card

/-- The block starting at `i` written with an explicit offset, for readability. -/
theorem map_range'_eq (s : ℕ → ℕ) (m : ℕ) : ∀ i : ℕ,
    (List.range' i m).map s = (List.range m).map (fun j => s (i + j)) := by
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    simp only [List.range'_succ, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    refine congrArg (List.cons (s i)) ?_
    refine List.ext_getElem (by simp) ?_
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    congr 1
    omega

theorem finset_card_filter_range (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range m).filter p).card
      = ((List.range m).filter (fun i => decide (p i))).length := by
  simp [Finset.filter, Finset.range, Finset.card, Multiset.filter, Multiset.range]
  rfl

theorem tails_eq_map_drop {α : Type*} (l : List α) :
    l.tails = (List.range (l.length + 1)).map (fun i => l.drop i) := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp [List.getElem_tails]

theorem take_range' (k : ℕ) : ∀ i n : ℕ,
    List.take k (List.range' i n) = List.range' i (min k n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro i n
    cases n with
    | zero => simp
    | succ n => simp [List.range'_succ, ih, Nat.succ_min_succ]

theorem take_drop_map_range (n i k : ℕ) (s : ℕ → ℕ) :
    (((List.range n).map s).drop i).take k = (List.range' i (min k (n - i))).map s := by
  rw [← List.map_drop, ← List.map_take, List.range_eq_range', List.drop_range']
  congr 1
  simpa using take_range' k i (n - i)

/-- `w` is a prefix of the `i`-th suffix exactly when the block fits inside `(range n)` and
matches there. -/
theorem prefix_drop_iff (w : List ℕ) (s : ℕ → ℕ) (n i : ℕ) (hi : i ≤ n) :
    w <+: ((List.range n).map s).drop i
      ↔ (i + w.length ≤ n ∧ w = (List.range' i w.length).map s) := by
  rw [List.prefix_iff_eq_take, take_drop_map_range]
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_map, List.length_range'] at hl
    have hfit : w.length ≤ n - i := le_of_eq_of_le hl (min_le_right _ _)
    exact ⟨by omega, by rwa [min_eq_left hfit] at h⟩
  · rintro ⟨hfit, hm⟩
    rwa [min_eq_left (by omega : w.length ≤ n - i)]

theorem countOccurrences_eq (w : List ℕ) (s : ℕ → ℕ) (n : ℕ) :
    countOccurrences w ((List.range n).map s)
      = ((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ w = (List.range' i w.length).map s)).card := by
  classical
  rw [countOccurrences, tails_eq_map_drop, List.countP_map, finset_card_filter_range,
    List.countP_eq_length_filter]
  simp only [List.length_map, List.length_range]
  congr 1
  refine List.filter_congr ?_
  intro i hi
  simp only [List.mem_range] at hi
  have h := prefix_drop_iff w s n i (by omega)
  rw [← List.isPrefixOf_iff_prefix] at h
  simp only [Function.comp_apply]
  refine Bool.eq_iff_iff.mpr ?_
  rw [decide_eq_true_eq]
  exact h

theorem countOccurrences_le_occStart (w : List ℕ) (hw : w ≠ []) (s : ℕ → ℕ) (n : ℕ) :
    countOccurrences w ((List.range n).map s) ≤ occStart w s n := by
  classical
  have hwpos : 0 < w.length := List.length_pos_iff.2 hw
  rw [countOccurrences_eq, occStart]
  refine Finset.card_le_card ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨by omega, hi.2.2⟩

theorem occStart_le_countOccurrences_add (w : List ℕ) (hw : w ≠ []) (s : ℕ → ℕ) (n : ℕ) :
    occStart w s n ≤ countOccurrences w ((List.range n).map s) + w.length := by
  classical
  have hwpos : 0 < w.length := List.length_pos_iff.2 hw
  rw [countOccurrences_eq, occStart]
  set S : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => i + w.length ≤ n ∧ w = (List.range' i w.length).map s) with hS
  set T : Finset ℕ := (Finset.range n).filter
    (fun i => w = (List.range' i w.length).map s) with hT
  have hTn : T.card ≤ n := le_trans (Finset.card_le_card (Finset.filter_subset _ _))
    (by simp)
  by_cases hwn : w.length ≤ n
  · have hsub : S ⊆ T := by
      intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hi
      simp only [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi.2.2⟩
    have hdiff : T \ S ⊆ Finset.Ico (n - w.length + 1) n := by
      intro i hi
      simp only [Finset.mem_sdiff, hT, hS, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨hin, hpi⟩, hnot⟩ := hi
      simp only [Finset.mem_Ico]
      refine ⟨?_, hin⟩
      by_contra hc
      exact hnot ⟨by omega, by omega, hpi⟩
    have hcard : (T \ S).card ≤ w.length := by
      refine le_trans (Finset.card_le_card hdiff) ?_
      simp only [Nat.card_Ico]
      omega
    have hsplit : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card hsub
    omega
  · omega

/-- **The frequency limits agree.** -/
theorem tendsto_occStart_iff (w : List ℕ) (hw : w ≠ []) (s : ℕ → ℕ) (L : ℝ) :
    Tendsto (fun n : ℕ => (occStart w s n : ℝ) / n) atTop (𝓝 L)
      ↔ Tendsto (fun n : ℕ =>
          (countOccurrences w ((List.range n).map s) : ℝ) / n) atTop (𝓝 L) := by
  have hkey : Tendsto (fun n : ℕ =>
      (occStart w s n : ℝ) / n - (countOccurrences w ((List.range n).map s) : ℝ) / n)
      atTop (𝓝 0) := by
    have hbd : ∀ᶠ n : ℕ in atTop, ‖(occStart w s n : ℝ) / n
        - (countOccurrences w ((List.range n).map s) : ℝ) / n‖ ≤ (w.length : ℝ) / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have h1r : (countOccurrences w ((List.range n).map s) : ℝ) ≤ (occStart w s n : ℝ) := by
        exact_mod_cast countOccurrences_le_occStart w hw s n
      have h2r : (occStart w s n : ℝ)
          ≤ (countOccurrences w ((List.range n).map s) : ℝ) + (w.length : ℝ) := by
        exact_mod_cast occStart_le_countOccurrences_add w hw s n
      rw [div_sub_div_same, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (by linarith) hnr.le
    refine squeeze_zero_norm' hbd ?_
    simpa using tendsto_const_div_atTop_nhds_zero_nat (w.length : ℝ)
  constructor
  · intro h; simpa using h.sub hkey
  · intro h; simpa using h.add hkey

end NormalNumbers
