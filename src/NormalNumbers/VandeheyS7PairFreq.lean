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
import NormalNumbers.VandeheyS7CFRun

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

/-! ## The pointwise decomposition -/

/-- The middle word of `z` at depth `|w|`, length `d`. -/
noncomputable def midWord (w : List ℕ) (d : ℕ) (z : ℝ) : List ℕ :=
  (List.range d).map fun j => cfDigit z (w.length + j)

@[simp] lemma midWord_length (w : List ℕ) (d : ℕ) (z : ℝ) : (midWord w d z).length = d := by
  simp [midWord]

lemma midWord_getD {w : List ℕ} {d : ℕ} {z : ℝ} {j : ℕ} (hj : j < d) :
    (midWord w d z).getD j 0 = cfDigit z (w.length + j) := by
  rw [midWord, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- **The occurrence is a cylinder event when its middle digits are small.** -/
theorem mem_cfCylinder_midWord {w : List ℕ} (hw : w ≠ []) {d : ℕ} {z : ℝ}
    (hz : z ∈ pairSet w (w.length + d)) :
    z ∈ cfCylinder (w ++ midWord w d z ++ w) := by
  obtain ⟨⟨hz01, hdig1⟩, hz2⟩ := hz
  obtain ⟨hz2mem, hdig2⟩ := hz2
  refine ⟨hz01, fun i hi => ?_⟩
  have hlen : (w ++ midWord w d z ++ w).length = w.length + d + w.length := by
    simp [List.length_append]
    omega
  rw [hlen] at hi
  rcases lt_or_ge i w.length with h1 | h1
  · rw [getD_append_left (by rw [List.length_append]; simp; omega), getD_append_left h1]
    exact hdig1 i h1
  rcases lt_or_ge i (w.length + d) with h2 | h2
  · -- the middle segment: the digit is the one `midWord` recorded
    rw [getD_append_left (by rw [List.length_append]; simp; omega),
      getD_append_right h1, midWord_getD (by omega)]
    congr 1
    omega
  · -- the second copy of `w`, reached through the shift
    rw [getD_append_right (by rw [List.length_append]; simp; omega)]
    have hshift : cfDigit (gaussMap^[w.length + d] z) (i - (w.length + d))
        = cfDigit z (w.length + d + (i - (w.length + d))) := by
      rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm]
    have hval := hdig2 (i - (w.length + d)) (by omega)
    rw [hshift] at hval
    rw [show w.length + d + (i - (w.length + d)) = i from by omega] at hval
    rw [hval]
    have hll : (w ++ midWord w d z).length = w.length + d := by
      rw [List.length_append, midWord_length]
    rw [hll]

/-- The middle word is a legitimate bounded word when all its digits are at most `B`. -/
theorem midWord_mem_boundedWords {w : List ℕ} {d B : ℕ} {z : ℝ}
    (hz : ∀ k : ℕ, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1)
    (hsmall : ∀ j < d, cfDigit z (w.length + j) ≤ B) :
    midWord w d z ∈ boundedWords B d := by
  rw [mem_boundedWords]
  refine ⟨by simp, fun a ha => ?_⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < d ∧ cfDigit z (w.length + j) = a := by
    simp only [midWord, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, hj, rfl⟩
  exact ⟨MapState.one_le_cfDigit hz _, hsmall j hj⟩

/-! ## The counting bound -/

open Classical in
/-- The number of times before `p` at which the digit exceeds `B`, shifted by `c`. -/
noncomputable def tailCount (y : ℝ) (B c p : ℕ) : ℝ :=
  (((range p).filter fun m => B < cfDigit y (m + c)).card : ℝ)

/-- **The pointwise decomposition.**  An occurrence of the pair event is either a bounded-middle
cylinder event, or one of its middle digits is large. -/
theorem blockIndic_pairSet_le {w : List ℕ} (hw : w ≠ []) {d B : ℕ} {y : ℝ}
    (hy : ∀ k : ℕ, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) (m : ℕ) :
    blockIndic (pairSet w (w.length + d)) (gaussMap^[m] y)
      ≤ (∑ u ∈ boundedWords B d, blockIndic (cfCylinder (w ++ u ++ w)) (gaussMap^[m] y))
        + ∑ j ∈ range d, (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := by
  classical
  set z := gaussMap^[m] y with hz
  have hznorm : ∀ k : ℕ, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1 := by
    intro k; rw [hz, ← Function.iterate_add_apply]; exact hy _
  have hdshift : ∀ j : ℕ, cfDigit z (w.length + j) = cfDigit y (m + (w.length + j)) := by
    intro j
    rw [hz, cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm]
  by_cases hmem : z ∈ pairSet w (w.length + d)
  · by_cases hsmall : ∀ j < d, cfDigit z (w.length + j) ≤ B
    · -- the bounded-middle branch
      have hu : midWord w d z ∈ boundedWords B d := midWord_mem_boundedWords hznorm hsmall
      have hzc : z ∈ cfCylinder (w ++ midWord w d z ++ w) := mem_cfCylinder_midWord hw hmem
      have hone : blockIndic (cfCylinder (w ++ midWord w d z ++ w)) z = 1 :=
        blockIndic_eq_one' hzc
      have hle : blockIndic (cfCylinder (w ++ midWord w d z ++ w)) z
          ≤ ∑ u ∈ boundedWords B d, blockIndic (cfCylinder (w ++ u ++ w)) z :=
        Finset.single_le_sum (f := fun u => blockIndic (cfCylinder (w ++ u ++ w)) z)
          (fun u _ => blockIndic_nonneg _ _) hu
      have htail : (0:ℝ) ≤ ∑ j ∈ range d,
          (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := by
        refine Finset.sum_nonneg fun j _ => ?_
        by_cases h : B < cfDigit y (m + (w.length + j)) <;> simp [h]
      rw [blockIndic_eq_one' hmem]
      rw [hone] at hle
      linarith
    · -- the large-digit branch
      push_neg at hsmall
      obtain ⟨j, hj, hjb⟩ := hsmall
      have hpos : (1:ℝ) ≤ ∑ j ∈ range d,
          (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := by
        have hterm : (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) = 1 := by
          rw [if_pos]
          rw [← hdshift j]; exact hjb
        calc (1:ℝ) = (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := hterm.symm
          _ ≤ ∑ j ∈ range d, (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := by
              refine Finset.single_le_sum
                (f := fun j => if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0)
                (fun j _ => ?_) (Finset.mem_range.2 hj)
              by_cases h : B < cfDigit y (m + (w.length + j)) <;> simp [h]
      have hsum0 : (0:ℝ) ≤ ∑ u ∈ boundedWords B d, blockIndic (cfCylinder (w ++ u ++ w)) z :=
        Finset.sum_nonneg fun u _ => blockIndic_nonneg _ _
      rw [blockIndic_eq_one' hmem]
      linarith
  · rw [blockIndic_eq_zero' hmem]
    have h1 : (0:ℝ) ≤ ∑ u ∈ boundedWords B d, blockIndic (cfCylinder (w ++ u ++ w)) z :=
      Finset.sum_nonneg fun u _ => blockIndic_nonneg _ _
    have h2 : (0:ℝ) ≤ ∑ j ∈ range d,
        (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) := by
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases h : B < cfDigit y (m + (w.length + j)) <;> simp [h]
    linarith

/-- **The summed decomposition.** -/
theorem blockCount_pairSet_le {w : List ℕ} (hw : w ≠ []) {d B : ℕ} {y : ℝ}
    (hy : ∀ k : ℕ, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) (p : ℕ) :
    blockCount (pairSet w (w.length + d)) p y
      ≤ (∑ u ∈ boundedWords B d, blockCount (cfCylinder (w ++ u ++ w)) p y)
        + ∑ j ∈ range d, tailCount y B (w.length + j) p := by
  classical
  rw [blockCount_apply]
  have hterm : ∀ m ∈ range p,
      blockIndic (pairSet w (w.length + d)) (gaussMap^[m] y)
        ≤ (∑ u ∈ boundedWords B d, blockIndic (cfCylinder (w ++ u ++ w)) (gaussMap^[m] y))
          + ∑ j ∈ range d, (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0) :=
    fun m _ => blockIndic_pairSet_le hw hy m
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib]
  have e1 : ∑ m ∈ range p, ∑ u ∈ boundedWords B d,
        blockIndic (cfCylinder (w ++ u ++ w)) (gaussMap^[m] y)
      = ∑ u ∈ boundedWords B d, blockCount (cfCylinder (w ++ u ++ w)) p y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => (blockCount_apply _ _ _).symm
  have e2 : ∑ m ∈ range p, ∑ j ∈ range d,
        (if B < cfDigit y (m + (w.length + j)) then (1:ℝ) else 0)
      = ∑ j ∈ range d, tailCount y B (w.length + j) p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tailCount, Finset.card_filter]
    push_cast
    rfl
  rw [e1, e2]

/-! ## The frequency limit -/

/-- The shifted digit tail is controlled by the unshifted one. -/
theorem tailCount_le_shift (y : ℝ) (B c p : ℕ) :
    tailCount y B c p ≤ (((range (p + c)).filter fun m => B < cfDigit y m).card : ℝ) := by
  classical
  have hsub : ((range p).filter fun m => B < cfDigit y (m + c))
      ⊆ Finset.image (fun m => m - c) ((range (p + c)).filter fun m => B < cfDigit y m) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    refine Finset.mem_image.2 ⟨m + c, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hm.2⟩
  have hcard := Finset.card_le_card hsub
  have hcard' := Finset.card_image_le (s := ((range (p + c)).filter fun m => B < cfDigit y m))
    (f := fun m => m - c)
  rw [tailCount]
  exact_mod_cast le_trans hcard hcard'

/-- **S7-PF.**  The orbit's pair frequency is at most the pair's Gauss mass, up to any tolerance:
for every `ε > 0` the count of times at which the orbit is in `I_w` and again in `I_w` after `g`
steps is eventually at most `(γ(pairSet) + ε)·p`. -/
theorem blockCount_pairSet_le_mass {w : List ℕ} (hw : w ≠ []) (hwpos : ∀ a ∈ w, 1 ≤ a)
    {y : ℝ} (hy : IsCFNormal y) (hyorb : ∀ k : ℕ, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (pairSet w (w.length + d)) p y
        ≤ ((gaussMeasure (pairSet w (w.length + d))).toReal + ε) * (p : ℝ) := by
  classical
  -- choose the digit bound so that each of the `d` tail terms costs at most `ε/(2d+2)`
  set δ : ℝ := ε / (4 * (d : ℝ) + 4) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; positivity
  obtain ⟨B, hB⟩ := exists_digitTail_freq_le hy hyorb hδpos
  -- the bounded-middle family's frequencies converge to their masses
  have hfam : Tendsto (fun p => ∑ u ∈ boundedWords B d,
      blockCount (cfCylinder (w ++ u ++ w)) p y / (p : ℝ)) atTop
      (nhds (∑ u ∈ boundedWords B d, (gaussMeasure (cfCylinder (w ++ u ++ w))).toReal)) := by
    refine tendsto_finsetSum _ fun u hu => ?_
    have hne : w ++ u ++ w ≠ [] := by
      intro h
      exact hw (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).1
    have hpos : ∀ a ∈ w ++ u ++ w, 1 ≤ a := by
      intro a ha
      rcases List.mem_append.1 ha with ha' | ha'
      · rcases List.mem_append.1 ha' with ha'' | ha''
        · exact hwpos a ha''
        · exact ((mem_boundedWords.1 hu).2 a ha'').1
      · exact hwpos a ha'
    exact blockCount_tendsto_of_isCFNormal hy hyorb _ hne hpos
  have hmass := sum_gaussMeasure_append_le (B := B) (d := d) hw hwpos
  have hfamev := hfam.eventually (eventually_lt_nhds
    (show (∑ u ∈ boundedWords B d, (gaussMeasure (cfCylinder (w ++ u ++ w))).toReal)
      < (∑ u ∈ boundedWords B d, (gaussMeasure (cfCylinder (w ++ u ++ w))).toReal) + ε / 2 by
      linarith))
  -- the `d` tail terms
  have htail : ∀ᶠ p : ℕ in atTop, ∀ j ∈ range d,
      tailCount y B (w.length + j) p ≤ δ * ((p : ℝ) + ((w.length + j : ℕ) : ℝ)) := by
    rw [Filter.eventually_all_finset]
    intro j _
    have hshift : ∀ᶠ p : ℕ in atTop,
        (((range (p + (w.length + j))).filter fun m => B < cfDigit y m).card : ℝ)
          ≤ δ * ((p : ℝ) + ((w.length + j : ℕ) : ℝ)) := by
      have := (Filter.tendsto_add_atTop_nat (w.length + j)).eventually hB
      filter_upwards [this] with p hp
      have hc : ((p + (w.length + j) : ℕ) : ℝ) = (p : ℝ) + ((w.length + j : ℕ) : ℝ) := by
        push_cast; ring
      rw [hc] at hp
      exact hp
    filter_upwards [hshift] with p hp
    exact le_trans (tailCount_le_shift y B (w.length + j) p) hp
  have hbig : ∀ᶠ p : ℕ in atTop,
      (d : ℝ) * (δ * (w.length + d : ℕ)) ≤ (ε / 4) * (p : ℝ) := by
    have hlim : Tendsto (fun p : ℕ => ((d : ℝ) * (δ * (w.length + d : ℕ))) / (p : ℝ)) atTop
        (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hlim.eventually (eventually_lt_nhds (show (0:ℝ) < ε / 4 by linarith)),
      eventually_gt_atTop 0] with p hp hp0
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
    rw [div_lt_iff₀ hpR] at hp
    linarith
  filter_upwards [hfamev, htail, hbig, eventually_gt_atTop 0] with p hfam' htail' hbig' hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hdec := blockCount_pairSet_le (w := w) (d := d) (B := B) hw hyorb p
  -- the family part
  have hfam'' : (∑ u ∈ boundedWords B d, blockCount (cfCylinder (w ++ u ++ w)) p y)
      ≤ ((gaussMeasure (pairSet w (w.length + d))).toReal + ε / 2) * (p : ℝ) := by
    have hsplit : ∑ u ∈ boundedWords B d, blockCount (cfCylinder (w ++ u ++ w)) p y
        = (∑ u ∈ boundedWords B d, blockCount (cfCylinder (w ++ u ++ w)) p y / (p : ℝ))
            * (p : ℝ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => (div_mul_cancel₀ _ hpR.ne').symm
    rw [hsplit]
    refine mul_le_mul_of_nonneg_right ?_ hpR.le
    linarith
  -- the tail part
  have htailsum : ∑ j ∈ range d, tailCount y B (w.length + j) p ≤ (ε / 2) * (p : ℝ) := by
    have hbound : ∀ j ∈ range d,
        tailCount y B (w.length + j) p ≤ δ * (p : ℝ) + δ * ((w.length + d : ℕ) : ℝ) := by
      intro j hj
      have hjd : j < d := Finset.mem_range.1 hj
      refine le_trans (htail' j hj) ?_
      have : ((w.length + j : ℕ) : ℝ) ≤ ((w.length + d : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_left hjd.le _
      nlinarith [hδpos]
    have hsum := Finset.sum_le_sum hbound
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hδp : (d : ℝ) * (δ * (p : ℝ)) ≤ (ε / 4) * (p : ℝ) := by
      have hd : (d : ℝ) * δ ≤ ε / 4 := by
        have hd0 : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
        nlinarith [hd0, hε.le]
      have h2 : (d : ℝ) * δ * (p : ℝ) ≤ (ε / 4) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hd hpR.le
      calc (d : ℝ) * (δ * (p : ℝ)) = (d : ℝ) * δ * (p : ℝ) := by ring
        _ ≤ (ε / 4) * (p : ℝ) := h2
    nlinarith [hsum, hbig']
  linarith [hdec, hfam'', htailsum]

/-! ## The pair frequency against the product bound -/

/-- **The pair frequency, against the independent value.**  Combining S7-PF with S7-PC's mixing
bound: the orbit's pair frequency at gap `|w| + h` is eventually at most
`γ(I_w)² + 4(9/10)^h + ε`. -/
theorem blockCount_pairSet_le_sq {w : List ℕ} (hw : w ≠ []) (hwpos : ∀ a ∈ w, 1 ≤ a)
    {y : ℝ} (hy : IsCFNormal y) (hyorb : ∀ k : ℕ, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1)
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (pairSet w (w.length + h)) p y
        ≤ ((gaussMeasure (cfCylinder w)).toReal ^ 2 + 4 * (9 / 10 : ℝ) ^ h + ε) * (p : ℝ) := by
  have hmix := abs_gaussMeasure_pair_sub_sq_le w hwpos h
  have hmixle : (gaussMeasure (pairSet w (w.length + h))).toReal
      ≤ (gaussMeasure (cfCylinder w)).toReal ^ 2 + 4 * (9 / 10 : ℝ) ^ h := by
    have := (abs_le.1 hmix).2
    rw [pairSet]
    linarith
  filter_upwards [blockCount_pairSet_le_mass hw hwpos hy hyorb h hε,
    eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  refine le_trans hp ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hpR.le

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.cfCylinder_append_subset_pairSet
#print axioms NormalNumbers.VandeheyS7.sum_gaussMeasure_append_le
#print axioms NormalNumbers.VandeheyS7.mem_cfCylinder_midWord
#print axioms NormalNumbers.VandeheyS7.blockIndic_pairSet_le
#print axioms NormalNumbers.VandeheyS7.blockCount_pairSet_le
#print axioms NormalNumbers.VandeheyS7.blockCount_pairSet_le_mass
#print axioms NormalNumbers.VandeheyS7.blockCount_pairSet_le_sq

end Audit
