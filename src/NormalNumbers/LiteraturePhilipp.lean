/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.CFPsiPin

/-!
# Philipp 1967: the continued-fraction digits are exponentially ψ-mixing

Discharges the cited `Literature.philipp_psi_mixing` (side quest, 2026-09-27) —
**proved**, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`.

The analytic content is `CFPsiPin.lean`: measuring the regularity of the
horizon integrals `G_k` in the **log metric** `|log(1+t) − log(1+t')|` (in which
the Gauss measure on the tail parameter is uniform) turns the Gauss–Kuzmin–Lévy
contraction into a *constant-free* geometric pin
`|G_k(t) − γ(A)| ≤ (79/100)^k·γ(A)`, which is exactly the ψ-mixing inequality
once pushed through the cylinder mixture (`gaussMeasure_cylinder_psi_mixing`).

What remains here is bookkeeping:

* `cfCylinderFrom m w` and `(0,1) ∩ T^{-m}(I_w)` differ only inside the
  rationals (an irrational orbit never leaves `(0,1)`), hence have the same
  `γ`-measure — `gaussMeasure_inter_cfCylinderFrom`;
* a word containing the digit `0` names a `γ`-null cylinder, so the inequality
  is `0 ≤ 0` there — `gaussMeasure_cfCylinder_eq_zero`.
-/

namespace NormalNumbers

open MeasureTheory

/-- A cylinder whose word carries the junk digit `0` is `γ`-null: it meets only
rationals, since every digit of an irrational in `(0,1)` is `≥ 1`. -/
lemma gaussMeasure_cfCylinder_eq_zero {w : List ℕ} (h : ¬ ∀ a ∈ w, 1 ≤ a) :
    gaussMeasure (cfCylinder w) = 0 := by
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have ha0' : a = 0 := by omega
  subst ha0'
  obtain ⟨i, hi, hiw⟩ : ∃ i, ∃ h : i < w.length, w[i] = 0 := by
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem ha
    exact ⟨i, hi, hiw⟩
  refine measure_mono_null (t := Set.range ((↑) : ℚ → ℝ)) ?_
    (gaussMeasure_countable_null (Set.countable_range _))
  intro x hx
  by_contra hirr
  have hirr' : Irrational x := hirr
  have hd := one_le_cfDigit x hirr' hx.1 i
  have := hx.2 i hi
  rw [List.getD_eq_getElem w 0 hi, hiw] at this
  omega

/-- `cfCylinderFrom m w` and `(0,1) ∩ T^{-m}(I_w)` differ only inside the
rationals, hence agree after intersecting with anything and measuring. -/
lemma gaussMeasure_inter_cfCylinderFrom (S : Set ℝ) (m : ℕ) (w : List ℕ) :
    gaussMeasure (S ∩ cfCylinderFrom m w) =
      gaussMeasure (S ∩ (Set.Ioo (0 : ℝ) 1 ∩ (gaussMap^[m]) ⁻¹' cfCylinder w)) := by
  set D : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ (gaussMap^[m]) ⁻¹' cfCylinder w with hD
  have hdigit : ∀ (x : ℝ) (i : ℕ), cfDigit (gaussMap^[m] x) i = cfDigit x (m + i) := by
    intro x i
    rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm i m]
  have hsub : D ⊆ cfCylinderFrom m w := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    intro i hi
    rw [← hdigit x i]
    exact hx2.2 i hi
  have hdiff : (cfCylinderFrom m w) \ D ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro x hx
    by_contra hirr
    have hirr' : Irrational x := hirr
    obtain ⟨hx1, hx2⟩ := hx.1
    obtain ⟨-, hTm⟩ := irrational_orbit x hirr' hx1 m
    exact hx.2 ⟨hx1, hTm, fun i hi => by rw [hdigit x i]; exact hx2 i hi⟩
  have hnull : gaussMeasure (((S ∩ cfCylinderFrom m w) \ (S ∩ D))) = 0 := by
    refine measure_mono_null (t := Set.range ((↑) : ℚ → ℝ)) ?_
      (gaussMeasure_countable_null (Set.countable_range _))
    intro x hx
    exact hdiff ⟨hx.1.2, fun hxD => hx.2 ⟨hx.1.1, hxD⟩⟩
  refine le_antisymm ?_ (measure_mono (Set.inter_subset_inter_right _ hsub))
  calc gaussMeasure (S ∩ cfCylinderFrom m w)
      ≤ gaussMeasure ((S ∩ D) ∪ (((S ∩ cfCylinderFrom m w) \ (S ∩ D)))) :=
        measure_mono (by intro x hx; by_cases h : x ∈ S ∩ D
                         · exact Or.inl h
                         · exact Or.inr ⟨hx, h⟩)
    _ ≤ gaussMeasure (S ∩ D) + gaussMeasure (((S ∩ cfCylinderFrom m w) \ (S ∩ D))) :=
        measure_union_le _ _
    _ = gaussMeasure (S ∩ D) := by rw [hnull, add_zero]

/-- `γ(cfCylinderFrom m w) = γ(I_w)` (Gauss-map invariance). -/
lemma gaussMeasure_cfCylinderFrom (m : ℕ) (w : List ℕ) :
    gaussMeasure (cfCylinderFrom m w) = gaussMeasure (cfCylinder w) := by
  have h := gaussMeasure_inter_cfCylinderFrom Set.univ m w
  rw [Set.univ_inter, Set.univ_inter] at h
  rw [h, gaussMeasure_inter_Ioo ((measurable_gaussMap.iterate m) (measurableSet_cfCylinder w)),
    gaussMeasure_preimage_iterate (measurableSet_cfCylinder w) m]

namespace Literature

/-- **Philipp 1967, Satz 3**: exponential ψ-mixing of the CF digits under
Gauss measure, with rate `ρ = 79/100 < 0.8`. -/
theorem philipp_psi_mixing_holds : philipp_psi_mixing := by
  refine ⟨79 / 100, by norm_num, by norm_num, ?_⟩
  intro u v n _hn
  set m : ℕ := u.length + n with hm
  set A : Set ℝ := cfCylinder v with hA
  have hAmeas : MeasurableSet A := measurableSet_cfCylinder v
  have hA1 : A ⊆ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo v
  have hBmeas : gaussMeasure (cfCylinderFrom m v) = gaussMeasure A :=
    gaussMeasure_cfCylinderFrom m v
  have hinter : gaussMeasure (cfCylinder u ∩ cfCylinderFrom m v)
      = gaussMeasure (cfCylinder u ∩ (gaussMap^[m]) ⁻¹' A) := by
    rw [gaussMeasure_inter_cfCylinderFrom (cfCylinder u) m v]
    congr 1
    rw [← Set.inter_assoc, Set.inter_eq_self_of_subset_left (cfCylinder_subset_Ioo u)]
  rw [hinter, hBmeas]
  by_cases hpos : ∀ a ∈ u, 1 ≤ a
  · have h := gaussMeasure_cylinder_psi_mixing u hpos n hAmeas hA1
    rw [← hm] at h
    calc |(gaussMeasure (cfCylinder u ∩ (gaussMap^[m]) ⁻¹' A)).toReal -
            (gaussMeasure (cfCylinder u)).toReal * (gaussMeasure A).toReal|
        ≤ (79 / 100 : ℝ) ^ n * (gaussMeasure A).toReal *
            (gaussMeasure (cfCylinder u)).toReal := h
      _ = (79 / 100 : ℝ) ^ n * (gaussMeasure (cfCylinder u)).toReal *
            (gaussMeasure A).toReal := by ring
  · have hzero : gaussMeasure (cfCylinder u) = 0 := gaussMeasure_cfCylinder_eq_zero hpos
    have hzero' : gaussMeasure (cfCylinder u ∩ (gaussMap^[m]) ⁻¹' A) = 0 :=
      measure_mono_null Set.inter_subset_left hzero
    rw [hzero, hzero']
    simp

end Literature

end NormalNumbers
