/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyClass
import NormalNumbers.CFPsiPin

/-!
# ψ-mixing against a whole family of cylinders

The class cocycle's equidistribution (`VandeheyClass.lean`) needs to decouple a *past* event
from a *future* event, where the past event is "the class after `n` digits is `d`".  That event
is **not** a single cylinder: it is a union of length-`n` cylinders, and that is precisely the
obstruction `PENDING_WORK.md` recorded for the renewal arguments —
`gaussMeasure_cylinder_psi_mixing` takes an arbitrary measurable *future* set but only
a single cylinder in front.

The obstruction dissolves because the repo's mixing bound is **multiplicative** (`ψ`-mixing,
error `ρ^g · γ(A) · γ(I_v)`) rather than additive (`α`-mixing, error `ρ^g`): a multiplicative
error summed over a disjoint family of same-length cylinders reproduces itself with the family's
total mass in place of the single cylinder's.  So the bound upgrades for free:

> `|γ(E ∩ T^{-(n+g)}A) − γ(E)·γ(A)| ≤ ρ^g · γ(A) · γ(E)`  for `E` any finite union of
> length-`n` cylinders.

Finite families suffice downstream because the digit truncation is already available
(`VandeheyAut.boundedWords`, `card_unbounded_window_le`, `digitTail_le`), and finiteness keeps
the additivity elementary.
-/

namespace NormalNumbers

namespace VandeheyMix

open MeasureTheory

/-- The union of the cylinders of a finite family of words. -/
noncomputable def familySet (F : Finset (List ℕ)) : Set ℝ := ⋃ w ∈ F, cfCylinder w

lemma measurableSet_familySet (F : Finset (List ℕ)) : MeasurableSet (familySet F) := by
  refine Set.Finite.measurableSet_biUnion F.finite_toSet fun w _ => measurableSet_cfCylinder w

/-- Same-length cylinders are pairwise disjoint, so a family's mass is the sum of its
cylinders' masses. -/
theorem gaussMeasure_familySet (F : Finset (List ℕ)) {n : ℕ}
    (hlen : ∀ w ∈ F, w.length = n) :
    gaussMeasure (familySet F) = ∑ w ∈ F, gaussMeasure (cfCylinder w) := by
  have hdisj : (↑F : Set (List ℕ)).PairwiseDisjoint (fun w => cfCylinder w) :=
    fun w hw w' hw' hne => cfCylinder_disjoint (by rw [hlen w hw, hlen w' hw']) hne
  exact measure_biUnion_finset hdisj (fun w _ => measurableSet_cfCylinder w)

/-- Intersecting a family union with any set distributes over the family. -/
lemma familySet_inter (F : Finset (List ℕ)) (P : Set ℝ) :
    familySet F ∩ P = ⋃ w ∈ F, (cfCylinder w ∩ P) := by
  rw [familySet, Set.iUnion₂_inter]

/-- The masses of the intersected cylinders also add. -/
theorem gaussMeasure_familySet_inter (F : Finset (List ℕ)) {n : ℕ}
    (hlen : ∀ w ∈ F, w.length = n) {P : Set ℝ} (hP : MeasurableSet P) :
    gaussMeasure (familySet F ∩ P) = ∑ w ∈ F, gaussMeasure (cfCylinder w ∩ P) := by
  have hdisj : (↑F : Set (List ℕ)).PairwiseDisjoint (fun w => cfCylinder w ∩ P) := by
    intro w hw w' hw' hne
    exact (cfCylinder_disjoint (by rw [hlen w hw, hlen w' hw']) hne).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [familySet_inter]
  exact measure_biUnion_finset hdisj
    (fun w _ => (measurableSet_cfCylinder w).inter hP)

/-- **ψ-mixing against a family.**  The multiplicative error of
`gaussMeasure_cylinder_psi_mixing` survives summation over a disjoint family of
same-length cylinders, so an arbitrary finite union of length-`n` cylinders decouples from the
future exactly as a single cylinder does.

This is the brick that unblocks the class-cocycle renewal: the event "the class after `n`
digits is `d`" is such a union, never a single cylinder. -/
theorem gaussMeasure_familySet_psi_mixing (F : Finset (List ℕ)) (n : ℕ)
    (hlen : ∀ w ∈ F, w.length = n) (hpos : ∀ w ∈ F, ∀ a ∈ w, 1 ≤ a)
    (g : ℕ) {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    |(gaussMeasure (familySet F ∩ (gaussMap^[n + g]) ⁻¹' A)).toReal
        - (gaussMeasure (familySet F)).toReal * (gaussMeasure A).toReal|
      ≤ (79 / 100) ^ g * (gaussMeasure A).toReal
          * (gaussMeasure (familySet F)).toReal := by
  classical
  set P : Set ℝ := (gaussMap^[n + g]) ⁻¹' A with hP
  have hPmeas : MeasurableSet P := (measurable_gaussMap.iterate (n + g)) hA
  have hAr : (0 : ℝ) ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
  -- write both sides as sums over the family
  have hsum₁ : (gaussMeasure (familySet F ∩ P)).toReal
      = ∑ w ∈ F, (gaussMeasure (cfCylinder w ∩ P)).toReal := by
    rw [gaussMeasure_familySet_inter F hlen hPmeas,
      ENNReal.toReal_sum (fun w _ => measure_ne_top _ _)]
  have hsum₂ : (gaussMeasure (familySet F)).toReal
      = ∑ w ∈ F, (gaussMeasure (cfCylinder w)).toReal := by
    rw [gaussMeasure_familySet F hlen, ENNReal.toReal_sum (fun w _ => measure_ne_top _ _)]
  rw [hsum₁, hsum₂, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun w hw => ?_)
  have hterm := gaussMeasure_cylinder_psi_mixing w (hpos w hw) g hA hA1
  rw [hlen w hw] at hterm
  exact le_trans hterm (le_of_eq (by ring))

/-! ## The countable version, which is the one the class renewal actually needs

The event "the class after `n` digits is `d`" is the union of the cylinders of **all** length-`n`
words `w` with `σ_w(d) = e` — countably many, not finitely many, since CF digits are unbounded.
The multiplicative error survives countable summation for exactly the same reason it survives
finite summation, so no digit truncation is needed here at all. -/

/-- The union of the cylinders of a countable family of words. -/
noncomputable def familySetC (S : Set (List ℕ)) : Set ℝ := ⋃ w ∈ S, cfCylinder w

lemma measurableSet_familySetC {S : Set (List ℕ)} (hct : S.Countable) :
    MeasurableSet (familySetC S) :=
  MeasurableSet.biUnion hct fun w _ => measurableSet_cfCylinder w

lemma pairwiseDisjoint_cfCylinder {S : Set (List ℕ)} {n : ℕ} (hlen : ∀ w ∈ S, w.length = n) :
    S.PairwiseDisjoint (fun w => cfCylinder w) :=
  fun w hw w' hw' hne => cfCylinder_disjoint (by rw [hlen w hw, hlen w' hw']) hne

/-- Masses add over a countable same-length family. -/
theorem gaussMeasure_familySetC {S : Set (List ℕ)} (hct : S.Countable) {n : ℕ}
    (hlen : ∀ w ∈ S, w.length = n) :
    gaussMeasure (familySetC S) = ∑' w : S, gaussMeasure (cfCylinder (w : List ℕ)) :=
  measure_biUnion hct (pairwiseDisjoint_cfCylinder hlen)
    (fun w _ => measurableSet_cfCylinder w)

/-- Masses of the *intersected* cylinders add too. -/
theorem gaussMeasure_familySetC_inter {S : Set (List ℕ)} (hct : S.Countable) {n : ℕ}
    (hlen : ∀ w ∈ S, w.length = n) {P : Set ℝ} (hP : MeasurableSet P) :
    gaussMeasure (familySetC S ∩ P)
      = ∑' w : S, gaussMeasure (cfCylinder (w : List ℕ) ∩ P) := by
  have hdisj : S.PairwiseDisjoint (fun w => cfCylinder w ∩ P) := by
    intro w hw w' hw' hne
    exact (cfCylinder_disjoint (by rw [hlen w hw, hlen w' hw']) hne).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [familySetC, Set.iUnion₂_inter]
  exact measure_biUnion hct hdisj (fun w _ => (measurableSet_cfCylinder w).inter hP)

/-- **ψ-mixing against a countable family of same-length cylinders.**  This is the form the
class renewal needs: `{x : σ_{W_n(x)}(d) = e}` is such a family. -/
theorem gaussMeasure_familySetC_psi_mixing {S : Set (List ℕ)} (hct : S.Countable) (n : ℕ)
    (hlen : ∀ w ∈ S, w.length = n) (hpos : ∀ w ∈ S, ∀ a ∈ w, 1 ≤ a)
    (g : ℕ) {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    |(gaussMeasure (familySetC S ∩ (gaussMap^[n + g]) ⁻¹' A)).toReal
        - (gaussMeasure (familySetC S)).toReal * (gaussMeasure A).toReal|
      ≤ (79 / 100) ^ g * (gaussMeasure A).toReal
          * (gaussMeasure (familySetC S)).toReal := by
  classical
  set P : Set ℝ := (gaussMap^[n + g]) ⁻¹' A with hP
  have hPmeas : MeasurableSet P := (measurable_gaussMap.iterate (n + g)) hA
  have hAr : (0 : ℝ) ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
  set ρ : ℝ := (79 / 100) ^ g with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := by positivity
  -- real-valued term families
  set b : S → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ))).toReal with hbdef
  set a : S → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ) ∩ P)).toReal with hadef
  have hb0 : ∀ w, 0 ≤ b w := fun w => ENNReal.toReal_nonneg
  have ha0 : ∀ w, 0 ≤ a w := fun w => ENNReal.toReal_nonneg
  -- the two totals, as real tsums
  have htotb : (gaussMeasure (familySetC S)).toReal = ∑' w : S, b w := by
    rw [gaussMeasure_familySetC hct hlen, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have htota : (gaussMeasure (familySetC S ∩ P)).toReal = ∑' w : S, a w := by
    rw [gaussMeasure_familySetC_inter hct hlen hPmeas,
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  -- summability, from finiteness of the total masses
  have hsumb : Summable b := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC hct hlen]
    exact measure_ne_top _ _
  have hsuma : Summable a := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC_inter hct hlen hPmeas]
    exact measure_ne_top _ _
  -- the termwise ψ bound
  have hterm : ∀ w : S, |a w - b w * (gaussMeasure A).toReal| ≤ ρ * (gaussMeasure A).toReal * b w := by
    intro w
    have h := gaussMeasure_cylinder_psi_mixing (w : List ℕ) (hpos _ w.2) g hA hA1
    rw [hlen _ w.2] at h
    exact le_trans h (le_of_eq (by simp only [hρ, hbdef]))
  -- assemble
  have hsumdiff : Summable fun w : S => a w - b w * (gaussMeasure A).toReal :=
    hsuma.sub (hsumb.mul_right _)
  have hsumbnd : Summable fun w : S => ρ * (gaussMeasure A).toReal * b w :=
    hsumb.mul_left _
  have habs : Summable fun w : S => ‖a w - b w * (gaussMeasure A).toReal‖ := by
    simpa [Real.norm_eq_abs] using hsumdiff.abs
  have hstep₁ : |∑' w : S, (a w - b w * (gaussMeasure A).toReal)|
      ≤ ∑' w : S, |a w - b w * (gaussMeasure A).toReal| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun w : S => a w - b w * (gaussMeasure A).toReal) habs
  have hstep₂ : (∑' w : S, |a w - b w * (gaussMeasure A).toReal|)
      ≤ ∑' w : S, ρ * (gaussMeasure A).toReal * b w :=
    Summable.tsum_le_tsum hterm hsumdiff.abs hsumbnd
  rw [htota, htotb, ← tsum_mul_right,
    ← Summable.tsum_sub hsuma (hsumb.mul_right _), ← tsum_mul_left]
  exact le_trans hstep₁ hstep₂

end VandeheyMix

end NormalNumbers
