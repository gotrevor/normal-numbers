/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4B: the torus projection does not increase volume

`torusProj : (g → ℝ) → (g → UnitAddCircle)` is the coordinatewise covering map.  For a measurable
`S ⊆ ℝ^g` whose image is measurable (e.g. `S` compact),

  `volume (torusProj '' S) ≤ volume S`   (`volume_image_torusProj_le`).

Route: `torusProj` is measure-preserving from the restriction to the fundamental box
`fund g = (0,1]^g` (product of `AddCircle.measurePreserving_mk`), the preimage of the image is
`⋃_{k ∈ ℤ^g} (S + k)`, and the translates `{y | y + k ∈ fund}` partition `ℝ^g`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace NormalNumbers.G4

variable {g : Type*} [Fintype g]

/-- The coordinatewise covering map `ℝ^g → 𝕋^g`. -/
def torusProj (x : g → ℝ) : g → UnitAddCircle := fun i => (x i : UnitAddCircle)

lemma continuous_torusProj : Continuous (torusProj (g := g)) :=
  continuous_pi fun i => (AddCircle.continuous_mk' _).comp (continuous_apply i)

/-- The fundamental box `(0,1]^g`. -/
def fund (g : Type*) : Set (g → ℝ) := Set.pi Set.univ fun _ => Ioc (0 : ℝ) 1

lemma measurableSet_fund : MeasurableSet (fund g) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem measurePreserving_torusProj :
    MeasurePreserving (torusProj (g := g)) (volume.restrict (fund g)) volume := by
  have h := measurePreserving_pi (fun _ : g => (volume : Measure ℝ).restrict (Ioc 0 (0 + 1)))
    (fun _ : g => (volume : Measure UnitAddCircle))
    (fun _ => AddCircle.measurePreserving_mk (T := 1) 0)
  rw [volume_pi, volume_pi, fund, Measure.restrict_pi_pi]
  simp only [zero_add] at h
  exact h

/-- The integer vector `k` with `y + k ∈ fund`. -/
noncomputable def kap (y : g → ℝ) : g → ℤ := fun i => ⌊1 - y i⌋

omit [Fintype g] in
lemma add_mem_fund_iff (y : g → ℝ) (k : g → ℤ) :
    y + (fun i => (k i : ℝ)) ∈ fund g ↔ kap y = k := by
  simp only [fund, Set.mem_pi, Set.mem_univ, true_implies, Pi.add_apply, mem_Ioc, kap,
    funext_iff, Int.floor_eq_iff]
  constructor
  · intro h i; obtain ⟨h1, h2⟩ := h i; constructor <;> linarith
  · intro h i; obtain ⟨h1, h2⟩ := h i; constructor <;> linarith

lemma coe_int_eq_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff 1).mpr ⟨n, by simp⟩

omit [Fintype g] in
lemma preimage_image_torusProj (S : Set (g → ℝ)) :
    torusProj ⁻¹' (torusProj '' S) = ⋃ k : g → ℤ, {x | x - (fun i => (k i : ℝ)) ∈ S} := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have : ∀ i, ∃ n : ℤ, x i - s i = n := fun i => by
      have h := congrFun hsx i
      simp only [torusProj] at h
      rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa using hn.symm⟩
    choose n hn using this
    refine ⟨n, ?_⟩
    convert hs using 1
    funext i; simp only [Pi.sub_apply]; linarith [hn i]
  · rintro ⟨k, hk⟩
    refine ⟨x - fun i => (k i : ℝ), hk, ?_⟩
    funext i
    simp only [torusProj, Pi.sub_apply, AddCircle.coe_sub, coe_int_eq_zero, sub_zero]

/-- **Torus projection does not increase volume.** -/
theorem volume_image_torusProj_le {S : Set (g → ℝ)} (hS : MeasurableSet S)
    (hB : MeasurableSet (torusProj '' S)) :
    volume (torusProj '' S) ≤ volume S := by
  rw [← measurePreserving_torusProj.measure_preimage hB.nullMeasurableSet,
    Measure.restrict_apply' measurableSet_fund, preimage_image_torusProj, Set.iUnion_inter]
  have hpiece : ∀ k : g → ℤ, {x | x - (fun i => (k i : ℝ)) ∈ S} ∩ fund g
      = (fun y => y + (fun i => ((-k) i : ℝ))) ⁻¹' (S ∩ {y | y + (fun i => (k i : ℝ)) ∈ fund g}) := by
    intro k; ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, Pi.neg_apply, Int.cast_neg]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by convert h1 using 2; funext i; simp [sub_eq_add_neg], ?_⟩
      convert h2 using 1; funext i; simp
    · rintro ⟨h1, h2⟩
      refine ⟨by convert h1 using 2; funext i; simp [sub_eq_add_neg], ?_⟩
      convert h2 using 1; funext i; simp
  have hmeas : ∀ k : g → ℤ, MeasurableSet {y : g → ℝ | y + (fun i => (k i : ℝ)) ∈ fund g} :=
    fun k => measurableSet_fund.preimage (measurable_add_const _)
  calc volume (⋃ k : g → ℤ, {x | x - (fun i => (k i : ℝ)) ∈ S} ∩ fund g)
      ≤ ∑' k : g → ℤ, volume ({x | x - (fun i => (k i : ℝ)) ∈ S} ∩ fund g) := measure_iUnion_le _
    _ = ∑' k : g → ℤ, volume (S ∩ {y | y + (fun i => (k i : ℝ)) ∈ fund g}) := by
        refine tsum_congr fun k => ?_
        rw [hpiece, measure_preimage_add_right]
    _ = volume (⋃ k : g → ℤ, S ∩ {y | y + (fun i => (k i : ℝ)) ∈ fund g}) := by
        refine (measure_iUnion ?_ fun k => hS.inter (hmeas k)).symm
        intro k k' hkk'
        rw [Function.onFun, Set.disjoint_left]
        rintro y ⟨-, h1⟩ ⟨-, h2⟩
        rw [mem_ofPred_eq, add_mem_fund_iff] at h1 h2
        exact hkk' (h1.symm.trans h2)
    _ = volume S := by
        rw [← Set.inter_iUnion, Set.iUnion_eq_univ_iff.mpr, Set.inter_univ]
        intro y
        exact ⟨kap y, (add_mem_fund_iff y (kap y)).mpr rfl⟩

end NormalNumbers.G4
