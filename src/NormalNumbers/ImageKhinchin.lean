/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFAffineFamily
import NormalNumbers.CFAeKhinchin

/-!
# The image-Khinchin headline

Combines the B6 Tier-2 affine-family measure witness
(`exists_cfNormal_and_affine_family_cfNormal'`) with the a.e. Khinchin-typicality
`ae_khinchinTypical` (the discharged tail-average SLLN): a single `x ∈ (0,1)`
that is CF-normal, Khinchin-typical, AND whose every affine image `q·x + r`
(`q > 0`, `r ∈ ℝ`) is CF-normal.  All three properties hold on co-null sets, so
their intersection meets `(0,1)`.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- **Image-Khinchin headline.**  For any countable set `Q` of pairs `(q, r)`
with `q > 0` (arbitrary real shift `r`), there is a single `x ∈ (0,1)` that is
CF-normal, Khinchin-typical, and whose affine image `q·x + r` is CF-normal for
every `(q, r) ∈ Q` simultaneously. -/
theorem exists_cfNormal_khinchinTypical_and_affine_family_cfNormal
    (Q : Set (ℝ × ℝ)) (hQ : Q.Countable) (hq : ∀ p ∈ Q, 0 < p.1) :
    ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ IsCFNormal x ∧ KhinchinTypical x ∧
      ∀ p ∈ Q, IsCFNormal (affineMap p.1 p.2 x) := by
  set A : Set ℝ := {x | ¬ IsCFNormal x} ∩ Set.Ioo (0 : ℝ) 1 with hA
  set Kbad : Set ℝ := {x | ¬ KhinchinTypical x} ∩ Set.Ioo (0 : ℝ) 1 with hKbad
  set Bad : ∀ _ : ℝ × ℝ, Set ℝ :=
    fun p => {x | ¬ IsCFNormal (affineMap p.1 p.2 x)} ∩ Set.Ioo (0 : ℝ) 1 with hBad
  have hA0 : gaussMeasure A = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_left)
      (le_of_eq gaussMeasure_notCFNormal)) (zero_le)
  have hK0 : gaussMeasure Kbad = 0 := by
    have hnull : gaussMeasure {x | ¬ KhinchinTypical x} = 0 :=
      MeasureTheory.ae_iff.mp ae_khinchinTypical
    exact le_antisymm (le_trans (measure_mono Set.inter_subset_left)
      (le_of_eq hnull)) (zero_le)
  have hBad0 : ∀ p ∈ Q, gaussMeasure (Bad p) = 0 :=
    fun p hp => gaussMeasure_notCFNormal_affine_Ioo01' (hq p hp) p.2
  have hBadU0 : gaussMeasure (⋃ p ∈ Q, Bad p) = 0 :=
    (measure_biUnion_null_iff hQ).mpr hBad0
  set BadAll : Set ℝ := A ∪ Kbad ∪ ⋃ p ∈ Q, Bad p with hBadAll
  have hBadAll0 : gaussMeasure BadAll = 0 := by
    refine le_antisymm (le_trans (measure_union_le _ _) ?_) (zero_le)
    rw [hBadU0, add_zero]
    exact le_trans (measure_union_le _ _) (by rw [hA0, hK0, add_zero])
  have hgood : gaussMeasure (Set.Ioo (0 : ℝ) 1 \ BadAll) = gaussMeasure (Set.Ioo (0 : ℝ) 1) :=
    measure_sdiff_null hBadAll0
  obtain ⟨x, hxIoo, hxBad⟩ := nonempty_of_measure_ne_zero
    (by rw [hgood]; exact gaussMeasure_Ioo01_pos.ne')
  have hxN : IsCFNormal x := by
    by_contra hxc; exact hxBad (Or.inl (Or.inl ⟨hxc, hxIoo⟩))
  have hxK : KhinchinTypical x := by
    by_contra hxc; exact hxBad (Or.inl (Or.inr ⟨hxc, hxIoo⟩))
  refine ⟨x, hxIoo, hxN, hxK, ?_⟩
  intro p hp
  by_contra hxc
  exact hxBad (Or.inr (Set.mem_biUnion hp ⟨hxc, hxIoo⟩))

end NormalNumbers
