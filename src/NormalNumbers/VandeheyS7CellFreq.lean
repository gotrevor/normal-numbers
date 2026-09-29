/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7QuasiBern

/-!
# S7-CF: CF-normality determines CELL frequencies, not just cylinder frequencies

`VandeheyS7Tight2` computed the frequency of the *tail* cell `cellSet [] T` from CF-normality by
a complement argument.  The interval-target route (lap 51's next step) needs the same for every
cell, because `CellCover` covers an interval by cells — exactly, with no exceptional set.

## The identity

Along an irrational orbit the cell is the cylinder minus the finitely many one-digit extensions
below the threshold:

    1_{cellSet w T}(t) = 1_{I_w}(t) − ∑_{1 ≤ a < T} 1_{I_{w++[a]}}(t)      (`blockIndic_cellSet_eq`)

— pointwise, because a point of `I_w` has a genuine digit `d ≥ 1` at position `|w|`, which either
reaches the threshold (cell, no extension matched) or equals exactly one `a < T`.  Summing along
the orbit gives `blockCount_cellSet_eq`, and CF-normality then pins the limit
(`blockCount_freq_cellSet_of_isCFNormal`).

## Guard rule

Content locator: at `T = 1` the correction sum is empty and the statement degenerates to the
cylinder frequency, so all the content is in the finitely many subtracted extensions.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

private lemma blockIndic_zero_of_notMem {A : Set ℝ} {t : ℝ} (h : t ∉ A) :
    blockIndic A t = 0 := by
  rw [blockIndic, Set.indicator_of_notMem h]

/-- **The pointwise identity.**  On irrational points of `(0,1)` the cell indicator is the
cylinder indicator minus the sub-threshold extensions. -/
theorem blockIndic_cellSet_eq {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    (w : List ℕ) (T : ℕ) :
    blockIndic (cellSet w T) t
      = blockIndic (cfCylinder w) t - ∑ a ∈ Finset.Ico 1 T, blockIndic (cfCylinder (w ++ [a])) t := by
  classical
  by_cases hw : t ∈ cfCylinder w
  · have hd1 : 1 ≤ cfDigit t w.length := one_le_cfDigit t hirr hmem _
    have hsnoc : t ∈ cfCylinder (w ++ [cfDigit t w.length]) := mem_cfCylinder_snoc hw
    -- the extension that `t` actually lies in is the one indexed by its digit
    have hmemiff : ∀ a : ℕ, t ∈ cfCylinder (w ++ [a]) ↔ a = cfDigit t w.length := by
      intro a
      constructor
      · intro ha
        have := ha.2 w.length (by simp)
        simpa using this.symm
      · rintro rfl; exact hsnoc
    by_cases hcell : T ≤ cfDigit t w.length
    · -- in the cell: every subtracted term vanishes
      have hzero : ∀ a ∈ Finset.Ico 1 T, blockIndic (cfCylinder (w ++ [a])) t = 0 := by
        intro a ha
        have hlt : a < T := (Finset.mem_Ico.1 ha).2
        refine blockIndic_zero_of_notMem ?_
        intro hc
        have := (hmemiff a).1 hc
        omega
      rw [blockIndic, Set.indicator_of_mem (show t ∈ cellSet w T from ⟨hw, hcell⟩), blockIndic,
        Set.indicator_of_mem hw, Finset.sum_congr rfl hzero]
      simp
    · -- below the threshold: exactly one subtracted term fires
      push Not at hcell
      have hmemIco : cfDigit t w.length ∈ Finset.Ico 1 T := Finset.mem_Ico.2 ⟨hd1, hcell⟩
      have hone : ∑ a ∈ Finset.Ico 1 T, blockIndic (cfCylinder (w ++ [a])) t = 1 := by
        rw [Finset.sum_eq_single (cfDigit t w.length)]
        · rw [blockIndic, Set.indicator_of_mem hsnoc]; rfl
        · intro a _ hne
          refine blockIndic_zero_of_notMem ?_
          intro hc
          exact hne ((hmemiff a).1 hc)
        · intro h; exact absurd hmemIco h
      have hnot : t ∉ cellSet w T := by
        rintro ⟨-, h⟩
        exact absurd h (not_le.2 hcell)
      rw [blockIndic, Set.indicator_of_notMem hnot, blockIndic, Set.indicator_of_mem hw, hone]
      simp
  · have hnotcell : t ∉ cellSet w T := fun h => hw h.1
    have hzero : ∀ a ∈ Finset.Ico 1 T, blockIndic (cfCylinder (w ++ [a])) t = 0 := by
      intro a _
      exact blockIndic_zero_of_notMem fun hc => hw (cfCylinder_append_subset w [a] hc)
    rw [blockIndic, Set.indicator_of_notMem hnotcell, blockIndic,
      Set.indicator_of_notMem hw, Finset.sum_congr rfl hzero]
    simp

/-- The orbit-count form of the identity. -/
theorem blockCount_cellSet_eq {y : ℝ} (hirr : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (w : List ℕ) (T p : ℕ) :
    blockCount (cellSet w T) p y
      = blockCount (cfCylinder w) p y
        - ∑ a ∈ Finset.Ico 1 T, blockCount (cfCylinder (w ++ [a])) p y := by
  classical
  simp only [blockCount_apply]
  calc ∑ k ∈ Finset.range p, blockIndic (cellSet w T) (gaussMap^[k] y)
      = ∑ k ∈ Finset.range p, (blockIndic (cfCylinder w) (gaussMap^[k] y)
          - ∑ a ∈ Finset.Ico 1 T, blockIndic (cfCylinder (w ++ [a])) (gaussMap^[k] y)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        obtain ⟨hirr', hmem'⟩ := irrational_orbit y hirr hmem k
        exact blockIndic_cellSet_eq hirr' hmem' w T
    _ = (∑ k ∈ Finset.range p, blockIndic (cfCylinder w) (gaussMap^[k] y))
          - ∑ k ∈ Finset.range p, ∑ a ∈ Finset.Ico 1 T,
              blockIndic (cfCylinder (w ++ [a])) (gaussMap^[k] y) := by
        rw [Finset.sum_sub_distrib]
    _ = _ := by rw [Finset.sum_comm]

/-- **Cell frequencies from CF-normality.** -/
theorem blockCount_freq_cellSet_of_isCFNormal {y : ℝ} (hirr : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1) (h : IsCFNormal y) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (T : ℕ) :
    Tendsto (fun p => blockCount (cellSet w T) p y / (p:ℝ)) atTop
      (nhds ((gaussMeasure (cfCylinder w)).toReal
        - ∑ a ∈ Finset.Ico 1 T, (gaussMeasure (cfCylinder (w ++ [a]))).toReal)) := by
  classical
  have horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0:ℝ) 1 :=
    fun j => (irrational_orbit y hirr hmem j).2
  have hcyl := blockCount_freq_of_isCFNormal horb h w hw hpos
  have hext : ∀ a ∈ Finset.Ico 1 T,
      Tendsto (fun p => blockCount (cfCylinder (w ++ [a])) p y / (p:ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder (w ++ [a]))).toReal) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Ico.1 ha).1
    refine blockCount_freq_of_isCFNormal horb h _ (by simp) ?_
    intro e he
    rcases List.mem_append.1 he with h' | h'
    · exact hpos e h'
    · simp only [List.mem_singleton] at h'; omega
  have hsum := tendsto_finsetSum (Finset.Ico 1 T) (fun a ha => hext a ha)
  have := hcyl.sub hsum
  refine this.congr fun p => ?_
  rw [blockCount_cellSet_eq hirr hmem w T p, sub_div, Finset.sum_div]

/-! ## The mass form of the identity -/

private lemma gaussMeasure_countable_zero {S : Set ℝ} (hS : S.Countable) :
    gaussMeasure S = 0 := by
  have hm : MeasurableSet S := hS.measurableSet
  have h := gaussMeasure_le_volume S hm
  rw [hS.measure_zero volume, mul_zero] at h
  simpa using h

/-- Points of `(0,1)` whose digit at position `n` vanishes are rational. -/
theorem irrational_of_cfDigit_ne_zero {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    (n : ℕ) : 1 ≤ cfDigit t n := one_le_cfDigit t hirr hmem n

/-- **The mass identity.**  `γ(cellSet w T) = γ(I_w) − ∑_{1≤a<T} γ(I_{w++[a]})`: the cell is the
cylinder minus its sub-threshold extensions, up to the rational null set. -/
theorem gaussMeasure_cellSet_eq (w : List ℕ) {T : ℕ} (hT : 1 ≤ T) :
    (gaussMeasure (cellSet w T)).toReal
      = (gaussMeasure (cfCylinder w)).toReal
        - ∑ a ∈ Finset.Ico 1 T, (gaussMeasure (cfCylinder (w ++ [a]))).toReal := by
  classical
  set E : Set ℝ := ⋃ a ∈ Finset.Ico 1 T, cfCylinder (w ++ [a]) with hE
  have hdisj : (↑(Finset.Ico 1 T) : Set ℕ).PairwiseDisjoint
      (fun a => cfCylinder (w ++ [a])) := by
    intro a _ b _ hab
    exact cfCylinder_disjoint_of_length_eq (by simp) (by simp [hab])
  have hEmeas := measure_biUnion_finset (μ := gaussMeasure) hdisj
    (fun a _ => measurableSet_cfCylinder _)
  -- the cell and the extensions are disjoint, and together they exhaust the cylinder
  have hdisj2 : Disjoint (cellSet w T) E := by
    rw [Set.disjoint_left]
    rintro t ⟨-, hd⟩ ht
    have hd' : T ≤ cfDigit t w.length := hd
    simp only [hE, Set.mem_iUnion, exists_prop] at ht
    obtain ⟨a, ha, hta⟩ := ht
    have : cfDigit t w.length = a := by
      have := hta.2 w.length (by simp)
      simpa using this
    have hlt := (Finset.mem_Ico.1 ha).2
    omega
  have hsub : cellSet w T ∪ E ⊆ cfCylinder w := by
    rintro t (ht | ht)
    · exact ht.1
    · simp only [hE, Set.mem_iUnion, exists_prop] at ht
      obtain ⟨a, -, hta⟩ := ht
      exact cfCylinder_append_subset w [a] hta
  have hsup : cfCylinder w ⊆ cellSet w T ∪ E ∪ Set.range ((↑) : ℚ → ℝ) := by
    intro t ht
    by_cases hirr : Irrational t
    · have hd1 : 1 ≤ cfDigit t w.length := one_le_cfDigit t hirr ht.1 _
      rcases Nat.lt_or_ge (cfDigit t w.length) T with hlt | hge
      · refine Or.inl (Or.inr ?_)
        simp only [hE, Set.mem_iUnion, exists_prop]
        exact ⟨cfDigit t w.length, Finset.mem_Ico.2 ⟨hd1, hlt⟩, mem_cfCylinder_snoc ht⟩
      · exact Or.inl (Or.inl ⟨ht, hge⟩)
    · refine Or.inr ?_
      rw [Irrational, not_not] at hirr
      exact hirr
  have hnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    gaussMeasure_countable_zero (Set.countable_range _)
  have hEm : MeasurableSet E := by
    refine Finset.measurableSet_biUnion _ (fun a _ => measurableSet_cfCylinder _)
  have h1 : gaussMeasure (cellSet w T) + gaussMeasure E = gaussMeasure (cellSet w T ∪ E) :=
    (measure_union hdisj2 hEm).symm
  have hle : gaussMeasure (cfCylinder w) ≤ gaussMeasure (cellSet w T ∪ E) := by
    calc gaussMeasure (cfCylinder w)
        ≤ gaussMeasure ((cellSet w T ∪ E) ∪ Set.range ((↑) : ℚ → ℝ)) := measure_mono hsup
      _ ≤ gaussMeasure (cellSet w T ∪ E) + gaussMeasure (Set.range ((↑) : ℚ → ℝ)) :=
          measure_union_le _ _
      _ = gaussMeasure (cellSet w T ∪ E) := by rw [hnull, add_zero]
  have hge : gaussMeasure (cellSet w T ∪ E) ≤ gaussMeasure (cfCylinder w) := measure_mono hsub
  have heq : gaussMeasure (cellSet w T) + gaussMeasure E = gaussMeasure (cfCylinder w) := by
    rw [h1]; exact le_antisymm hge hle
  -- pass to real numbers
  have hfin : ∀ s : Set ℝ, gaussMeasure s ≠ ⊤ := fun s => measure_ne_top gaussMeasure s
  have hreal : (gaussMeasure (cellSet w T)).toReal + (gaussMeasure E).toReal
      = (gaussMeasure (cfCylinder w)).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _), heq]
  have hEreal : (gaussMeasure E).toReal
      = ∑ a ∈ Finset.Ico 1 T, (gaussMeasure (cfCylinder (w ++ [a]))).toReal := by
    rw [hE, hEmeas, ENNReal.toReal_sum (fun a _ => hfin _)]
  rw [hEreal] at hreal
  linarith

/-- The cell-frequency limit, in the form downstream consumers want. -/
theorem blockCount_freq_cellSet_mass {y : ℝ} (hirr : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1) (h : IsCFNormal y) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) {T : ℕ} (hT : 1 ≤ T) :
    Tendsto (fun p => blockCount (cellSet w T) p y / (p:ℝ)) atTop
      (nhds (gaussMeasure (cellSet w T)).toReal) := by
  rw [gaussMeasure_cellSet_eq w hT]
  exact blockCount_freq_cellSet_of_isCFNormal hirr hmem h w hw hpos T


section Audit

#print axioms blockIndic_cellSet_eq
#print axioms blockCount_cellSet_eq
#print axioms blockCount_freq_cellSet_of_isCFNormal
#print axioms gaussMeasure_cellSet_eq
#print axioms blockCount_freq_cellSet_mass

end Audit

end NormalNumbers.VandeheyS7
