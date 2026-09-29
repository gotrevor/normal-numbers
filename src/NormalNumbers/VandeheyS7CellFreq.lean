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

section Audit

#print axioms blockIndic_cellSet_eq
#print axioms blockCount_cellSet_eq
#print axioms blockCount_freq_cellSet_of_isCFNormal

end Audit

end NormalNumbers.VandeheyS7
