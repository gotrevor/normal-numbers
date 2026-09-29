/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-PF: the orbit's pair frequency is at most the pair's Gauss mass

S7-CK priced what the goal would still owe if one wanted the crux back: *window concentration* and
*local clock regularity*.  The first is a statement about the Gauss system alone, and its analytic
input is the pair correlation of a cylinder with its own shift (S7-PC).  Turning that input into a
statement about a CF-NORMAL ORBIT needs one combinatorial step, which is this module: the orbit's
frequency of the pair event is at most the pair's Gauss mass.

    limsup (1/p) · #{m < p : Gᵐy ∈ I_w  and  G^{m+g}y ∈ I_w}  ≤  γ(I_w ∩ G^{-g} I_w)

The pair event is not a cylinder — it is a countable union of them, one for each middle word — so
CF-normality does not apply to it directly.  The proof splits each occurrence by its middle word:
those with all middle digits `≤ B` are cylinder events of depth `|w| + d + |w|` and CF-normality
computes them (and their masses sum to at most the pair's mass, since the cylinders are disjoint
subsets of it); those with a large middle digit are counted by the digit tail, which S7-PC bounds
by `ε` per position along a CF-normal orbit.

With `variance_blockCount_le` (already in the repo) this gives the window-concentration estimate at
scale `T` with rate `O(1/√T)` — the input half of the crux's locality.

## Guard rule

**Content locator.**  `cfCylinder_append_subset_pairSet` is where the shift is checked (the middle
word's length is what lines the second copy of `w` up with the shift `g`); everything else is
counting.  With `d = 0` the middle word is empty, the family is the single cylinder `w ++ w`, and
the statement is CF-normality of one cylinder.

**Degenerate cases.**  `w = []` makes `pairSet = (0,1)` and both sides `1`.  `B = 0` makes the
bounded family empty and the bound trivially `d · (tail)`, which is `≥ 1` for `d ≥ 1`.
-/
import NormalNumbers.VandeheyS7PairCorr

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers Finset

/-- The pair event: in `I_w` now and in `I_w` again after `g` steps. -/
noncomputable def pairSet (w : List ℕ) (g : ℕ) : Set ℝ :=
  cfCylinder w ∩ (gaussMap^[g]) ⁻¹' cfCylinder w

lemma measurableSet_pairSet (w : List ℕ) (g : ℕ) : MeasurableSet (pairSet w g) :=
  (measurableSet_cfCylinder w).inter ((measurable_gaussMap.iterate g) (measurableSet_cfCylinder w))

/-- A genuine orbit point of a cylinder with a genuine first digit stays in `(0,1)`. -/
lemma mem_Ioo_of_cfDigit_pos {z : ℝ} (hz : 0 < z) (h1 : z < 1) : z ∈ Set.Ioo (0:ℝ) 1 := ⟨hz, h1⟩

lemma getD_append_left {w u : List ℕ} {i : ℕ} (hi : i < w.length) :
    (w ++ u).getD i 0 = w.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {w u : List ℕ} {i : ℕ} (hi : w.length ≤ i) :
    (w ++ u).getD i 0 = u.getD (i - w.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right hi]

/-- **The middle-word cylinders sit inside the pair event.** -/
theorem cfCylinder_append_subset_pairSet {w u : List ℕ} (hw : w ≠ []) (hwpos : ∀ a ∈ w, 1 ≤ a) :
    cfCylinder (w ++ u ++ w) ⊆ pairSet w (w.length + u.length) := by
  intro x hx
  obtain ⟨hx01, hdig⟩ := hx
  set g := w.length + u.length with hg
  have hlen : (w ++ u ++ w).length = w.length + u.length + w.length := by
    simp [List.length_append]
    omega
  refine ⟨⟨hx01, fun i hi => ?_⟩, ?_⟩
  · -- the first copy of `w`
    have := hdig i (by rw [hlen]; omega)
    rw [this, getD_append_left (by rw [List.length_append]; try omega), getD_append_left hi]
  · -- after `g` steps the second copy of `w` shows up
    have hw0 : 0 < w.length := List.length_pos_iff.2 hw
    have hfirst : 1 ≤ w.getD 0 0 := by
      have h0 : w.getD 0 0 = w[0]'(hw0) := List.getD_eq_getElem _ _ hw0
      rw [h0]
      exact hwpos _ (List.getElem_mem _)
    -- the digit at position `g` is `w`'s first digit, so the orbit point is genuine there
    have hdg : cfDigit x g = w.getD 0 0 := by
      have hd := hdig g (by rw [hlen]; omega)
      rw [hd, getD_append_right (by rw [List.length_append]; try omega)]
      try (congr 1; rw [List.length_append]; omega)
    have hinv : (1:ℝ) ≤ (gaussMap^[g] x)⁻¹ := by
      have h1 : 1 ≤ ⌊(gaussMap^[g] x)⁻¹⌋₊ := by
        rw [← cfDigit, hdg]; exact hfirst
      exact_mod_cast (Nat.one_le_floor_iff _).1 h1
    have hgpos : 0 < gaussMap^[g] x := by
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · have hneg : (gaussMap^[g] x)⁻¹ < 0 := inv_lt_zero.2 hlt
        linarith
      · rw [heq, inv_zero] at hinv
        linarith
    have hglt : gaussMap^[g] x < 1 := by
      have hgpos' : 0 < g := by omega
      have hrw : gaussMap^[g] x = gaussMap (gaussMap^[g - 1] x) := by
        conv_lhs => rw [show g = (g - 1) + 1 from by omega]
        rw [Function.iterate_succ_apply']
      rw [hrw]
      exact (gaussMap_mem_Ico01 _).2
    refine ⟨⟨hgpos, hglt⟩, fun i hi => ?_⟩
    have hshift : cfDigit (gaussMap^[g] x) i = cfDigit x (g + i) := by
      rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm]
    rw [hshift]
    have := hdig (g + i) (by rw [hlen]; omega)
    rw [this, getD_append_right (by rw [List.length_append]; try omega)]
    try (congr 1; rw [List.length_append]; omega)

/-- The cylinders of distinct middle words are disjoint. -/
lemma cfCylinder_append_disjoint {w u u' : List ℕ} (hlen : u.length = u'.length) (hne : u ≠ u') :
    Disjoint (cfCylinder (w ++ u ++ w)) (cfCylinder (w ++ u' ++ w)) := by
  refine cfCylinder_disjoint (by simp [List.length_append, hlen]) ?_
  intro h
  apply hne
  have h1 : w ++ (u ++ w) = w ++ (u' ++ w) := by
    simpa [List.append_assoc] using h
  have h2 : u ++ w = u' ++ w := List.append_cancel_left h1
  exact List.append_cancel_right h2

/-! ## The mass of the bounded-middle family -/

/-- The bounded-middle cylinders' masses sum to at most the pair's mass. -/
theorem sum_gaussMeasure_append_le {w : List ℕ} (hw : w ≠ []) (hwpos : ∀ a ∈ w, 1 ≤ a)
    (B d : ℕ) :
    ∑ u ∈ boundedWords B d, (gaussMeasure (cfCylinder (w ++ u ++ w))).toReal
      ≤ (gaussMeasure (pairSet w (w.length + d))).toReal := by
  classical
  have hdisj : ∀ u ∈ boundedWords B d, ∀ u' ∈ boundedWords B d, u ≠ u' →
      Disjoint (cfCylinder (w ++ u ++ w)) (cfCylinder (w ++ u' ++ w)) := by
    intro u hu u' hu' hne
    have h1 : u.length = d := (mem_boundedWords.1 hu).1
    have h2 : u'.length = d := (mem_boundedWords.1 hu').1
    exact cfCylinder_append_disjoint (by rw [h1, h2]) hne
  have hsub : (⋃ u ∈ boundedWords B d, cfCylinder (w ++ u ++ w))
      ⊆ pairSet w (w.length + d) := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 hz
    have hlen : u.length = d := (mem_boundedWords.1 hu).1
    have := cfCylinder_append_subset_pairSet (u := u) hw hwpos hzu
    rwa [hlen] at this
  have hsum : gaussMeasure (⋃ u ∈ boundedWords B d, cfCylinder (w ++ u ++ w))
      = ∑ u ∈ boundedWords B d, gaussMeasure (cfCylinder (w ++ u ++ w)) :=
    measure_biUnion_finset hdisj (fun u _ => measurableSet_cfCylinder _)
  have hmono : gaussMeasure (⋃ u ∈ boundedWords B d, cfCylinder (w ++ u ++ w))
      ≤ gaussMeasure (pairSet w (w.length + d)) := measure_mono hsub
  rw [hsum] at hmono
  have hfin : (∑ u ∈ boundedWords B d, gaussMeasure (cfCylinder (w ++ u ++ w))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hmono ?_)
    exact lt_of_le_of_ne le_top (measure_ne_top _ _)
  rw [← ENNReal.toReal_sum (fun u _ => measure_ne_top _ _)]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmono

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.cfCylinder_append_subset_pairSet
#print axioms NormalNumbers.VandeheyS7.sum_gaussMeasure_append_le

end Audit
