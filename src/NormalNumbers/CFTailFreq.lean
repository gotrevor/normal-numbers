/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.OccurrenceCountEquiv

/-!
# Window frequencies only see the tail

The engine the Serret half of Vandehey 2017 Theorem 1.1 needs: if two digit sequences
agree after finite shifts (`s (n + M) = r (n + N)` for all `n`) then every window has the
same frequency in both.  Everything is counted with `occStart` — start positions — where
the shift is an honest index bijection off a set of size `M + N`;
`tendsto_occStart_iff` transfers the conclusion back to `countOccurrences`.
-/

namespace NormalNumbers

open Filter Topology

variable {w : List ℕ} {s r : ℕ → ℕ} {M N : ℕ}

/-- Off the first `M` positions, the `s`-window at `i` is the `r`-window at `i - M + N`. -/
lemma window_shift (h : ∀ n, s (n + M) = r (n + N)) {i : ℕ} (hi : M ≤ i) :
    (w = (List.range' i w.length).map s) ↔ (w = (List.range' (i - M + N) w.length).map r) := by
  rw [map_range'_eq, map_range'_eq]
  have hfun : (fun j => s (i + j)) = (fun j => r (i - M + N + j)) := by
    funext j
    have he : i + j = (i - M + j) + M := by omega
    rw [he, h]
    congr 1
    omega
  rw [hfun]

/-- The shifted start-position counts differ by at most `M + N`. -/
lemma occStart_shift_le (h : ∀ n, s (n + M) = r (n + N)) (p : ℕ) :
    occStart w s (p + M) ≤ M + occStart w r (p + N) := by
  classical
  set A := (Finset.range (p + M)).filter (fun i => w = (List.range' i w.length).map s) with hA
  set B := A.filter (fun i => M ≤ i) with hB
  have hsub : A ⊆ Finset.range M ∪ B := by
    intro i hi
    rcases lt_or_ge i M with hiM | hiM
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hiM)
    · exact Finset.mem_union_right _ (by rw [hB]; exact Finset.mem_filter.mpr ⟨hi, hiM⟩)
  have hsplit : occStart w s (p + M) ≤ M + B.card := by
    calc occStart w s (p + M) = A.card := by rw [occStart, hA]
      _ ≤ (Finset.range M ∪ B).card := Finset.card_le_card hsub
      _ ≤ (Finset.range M).card + B.card := Finset.card_union_le _ _
      _ = M + B.card := by rw [Finset.card_range]
  refine le_trans hsplit ?_
  have hmemB : ∀ i ∈ B, M ≤ i ∧ i < p + M ∧ w = (List.range' i w.length).map s := by
    intro i hi
    rw [hB, Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.2, hi.1.1, hi.1.2⟩
  have hinj : B.card ≤ occStart w r (p + N) := by
    rw [occStart]
    refine Finset.card_le_card_of_injOn (fun i => i - M + N) ?_ ?_
    · intro i hi
      obtain ⟨hMi, hlt, hpred⟩ := hmemB i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · show i - M + N < p + N
        omega
      · exact (window_shift h hMi).mp hpred
    · intro i hi j hj hij
      have hMi := (hmemB i (by simpa using hi)).1
      have hMj := (hmemB j (by simpa using hj)).1
      have hij' : i - M + N = j - M + N := hij
      omega
  omega

/-- The frequency limit transfers across a finite shift. -/
theorem tendsto_occStart_of_shift (hw : w ≠ []) (h : ∀ n, s (n + M) = r (n + N)) {L : ℝ}
    (hr : Tendsto (fun n : ℕ => (occStart w r n : ℝ) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (occStart w s n : ℝ) / n) atTop (𝓝 L) := by
  have hsymm : ∀ n, r (n + N) = s (n + M) := fun n => (h n).symm
  -- the two-sided bound
  have hbd : ∀ p : ℕ, (|(occStart w s (p + M) : ℝ) - (occStart w r (p + N) : ℝ)|)
      ≤ (M : ℝ) + N := by
    intro p
    have h1 := occStart_shift_le (w := w) h p
    have h2 := occStart_shift_le (w := w) hsymm p
    have h1' : (occStart w s (p + M) : ℝ) ≤ (M : ℝ) + occStart w r (p + N) := by
      exact_mod_cast h1
    have h2' : (occStart w r (p + N) : ℝ) ≤ (N : ℝ) + occStart w s (p + M) := by
      exact_mod_cast h2
    rw [abs_le]
    constructor <;> [linarith; linarith]
  -- `occStart w r (p + N) / p → L`
  have hq : Tendsto (fun p : ℕ => (occStart w r (p + N) : ℝ) / p) atTop (𝓝 L) := by
    have hshift : Tendsto (fun p : ℕ => (occStart w r (p + N) : ℝ) / (p + N : ℕ)) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat N).mpr hr
    have hratio : Tendsto (fun p : ℕ => ((p : ℝ) + N) / p) atTop (𝓝 1) := by
      have : ∀ᶠ p : ℕ in atTop, ((p : ℝ) + N) / p = 1 + (N : ℝ) / p := by
        filter_upwards [eventually_gt_atTop 0] with p hp
        have : (0 : ℝ) < p := by exact_mod_cast hp
        field_simp
      rw [tendsto_congr' this]
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ))
    have := hshift.mul hratio
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hpn : ((p : ℝ) + N) ≠ 0 := by positivity
    push_cast
    field_simp
  -- so `occStart w s (p + M) / p → L`
  have hs' : Tendsto (fun p : ℕ => (occStart w s (p + M) : ℝ) / p) atTop (𝓝 L) := by
    have hdiff : Tendsto (fun p : ℕ =>
        (occStart w s (p + M) : ℝ) / p - (occStart w r (p + N) : ℝ) / p) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by
        simpa using tendsto_const_div_atTop_nhds_zero_nat ((M : ℝ) + N))
      filter_upwards [eventually_gt_atTop 0] with p hp
      have hp' : (0 : ℝ) < p := by exact_mod_cast hp
      rw [div_sub_div_same, Real.norm_eq_abs, abs_div, abs_of_pos hp']
      exact div_le_div_of_nonneg_right (hbd p) hp'.le
    simpa using hdiff.add hq
  -- undo the `+ M` shift
  have hfinal : Tendsto (fun p : ℕ => (occStart w s (p + M) : ℝ) / (p + M : ℕ)) atTop (𝓝 L) := by
    have hratio : Tendsto (fun p : ℕ => (p : ℝ) / ((p : ℝ) + M)) atTop (𝓝 1) := by
      have heq : ∀ᶠ p : ℕ in atTop, (p : ℝ) / ((p : ℝ) + M) = 1 - (M : ℝ) / ((p : ℝ) + M) := by
        filter_upwards [eventually_gt_atTop 0] with p hp
        have hp' : (0 : ℝ) < p := by exact_mod_cast hp
        have : ((p : ℝ) + M) ≠ 0 := by positivity
        field_simp
        ring
      rw [tendsto_congr' heq]
      have : Tendsto (fun p : ℕ => (M : ℝ) / ((p : ℝ) + M)) atTop (𝓝 0) := by
        refine Filter.Tendsto.const_div_atTop ?_ _
        exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa using tendsto_const_nhds.sub this
    have := hs'.mul hratio
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : ((p : ℝ) + M) ≠ 0 := by positivity
    push_cast
    field_simp
  exact (tendsto_add_atTop_iff_nat M).mp hfinal

end NormalNumbers
