/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CV: the cylinder cover of a target interval, with its mass

S7-WD/WD′ reduced the §7 crux to *producing* a finite family `S` of input windows covering the
state-dependent target, with total Gauss mass close to the target's.  This module supplies the
covering half, unconditionally:

* `dist_le_of_mem_cfCylinder` — a genuine cylinder of length `M` has diameter `≤ 2/2^M`
  (from `cfCylinder_endpoints`'s endpoint gap and the Fibonacci growth of `cfK`).
* `sum_gaussMeasure_cover_le` — if `S` is a family of pairwise disjoint level-`M` cylinders each
  meeting `Ioo α β`, then `Σ_{v∈S} γ(I_v) ≤ (β − α + 2δ)/log 2` with `δ = 2/2^M`.

The proof is the thickening argument, not an endpoint count: a set of diameter `≤ δ` meeting
`(α, β)` is contained in `(α−δ, β+δ)`, and disjointness turns the sum into the mass of a subset of
that thickened interval.  So no "at most two straddling cylinders" bookkeeping is needed, and the
statement holds for ANY subfamily of level-`M` cylinders that meet the target.

## Where it plugs in

The crux's target at time `n` is `mapBlockSet s w 0 = s.mob⁻¹(I_w) ∩ (0,1)`, an interval when `s`
is a Möbius state and `I_w` an interval; S7-PB bounds its mass by `(2K₀/η)·γ(I_w)`.  Feeding that
bound to `sum_gaussMeasure_cover_le` gives a cover of mass `≤ (2K₀/η)·γ(I_w) + O(2^{-M})`, which
is exactly what S7-WD′ consumes.  What this module does NOT supply — and what remains the sole
open point of the route — is uniformity of the cover in the far-past state (fact (δ)).

## Guard rule

Content locator: `δ` enters twice, once at each end, which is why the bound is `+2δ` and not
`+δ`; with `δ = 0` the statement degenerates to "disjoint subsets of an interval have total mass
at most the interval's", which is true but useless, since no cylinder has diameter `0`.
Degenerate case: `β ≤ α` makes the family empty (nothing meets `∅`) but the bound stays true
because `2δ ≥ 0`.
-/
import NormalNumbers.VandeheyS7Cell
import NormalNumbers.GaussErgodic

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

/-- **Cylinder diameter decay.**  Two points of a genuine level-`M` cylinder are within
`2/2^M`. -/
theorem dist_le_of_mem_cfCylinder {w : List ℕ} (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    {u v : ℝ} (hu : u ∈ cfCylinder w) (hv : v ∈ cfCylinder w) :
    |u - v| ≤ 2 / 2 ^ w.length := by
  obtain ⟨P, P', hgap, hIcc, -⟩ := cfCylinder_endpoints w hw hpos
  set E0 : ℝ := (P : ℝ) / (cfK w : ℝ) with hE0
  set E1 : ℝ := (P' : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) with hE1
  have hlen : (volume (cfCylinder w)).toReal
      = 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) := by
    rw [volume_cfCylinder w hw hpos]
    refine ENNReal.toReal_ofReal ?_
    have h1 : (1:ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
    have h2 : (0:ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
    positivity
  have hbound : 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) ≤ 2 / 2 ^ w.length := by
    rw [← hlen]; exact volume_cfCylinder_le_two_div w hw hpos
  have huv : u ∈ Set.uIcc E0 E1 := hIcc hu
  have hvv : v ∈ Set.uIcc E0 E1 := hIcc hv
  have hd : |u - v| ≤ |E1 - E0| := by
    rw [Set.uIcc, Set.mem_Icc] at huv hvv
    have hkey : E0 ⊔ E1 - E0 ⊓ E1 = |E1 - E0| := by
      rcases le_total E0 E1 with h | h
      · rw [sup_eq_right.2 h, inf_eq_left.2 h, abs_of_nonneg (by linarith)]
      · rw [sup_eq_left.2 h, inf_eq_right.2 h, abs_of_nonpos (by linarith)]; ring
    rw [abs_le]
    constructor <;> linarith [huv.1, huv.2, hvv.1, hvv.2]
  rw [hgap] at hd
  linarith

/-- A set of diameter `≤ δ` meeting `Ioo α β` sits inside the thickened interval. -/
lemma subset_Ioo_thicken {C : Set ℝ} {α β δ : ℝ} (_hδ : 0 ≤ δ)
    (hdiam : ∀ u ∈ C, ∀ v ∈ C, |u - v| ≤ δ) (hmeet : ∃ t ∈ C, t ∈ Set.Ioo α β) :
    C ⊆ Set.Ioo (α - δ - 1) (β + δ + 1) := by
  obtain ⟨t, htC, htI⟩ := hmeet
  intro u huC
  have h := hdiam u huC t htC
  rw [abs_le] at h
  exact ⟨by linarith [htI.1], by linarith [htI.2]⟩

/-- **S7-CV.**  A disjoint family of level-`M` cylinders meeting `Ioo α β` has total Gauss mass at
most that of the thickened interval. -/
theorem sum_gaussMeasure_cover_le {M : ℕ} {S : Finset (List ℕ)}
    (hlen : ∀ v ∈ S, v.length = M) (_hpos : ∀ v ∈ S, ∀ a ∈ v, 1 ≤ a)
    {α β δ : ℝ} (hδ : 0 ≤ δ) (hα : 0 ≤ α - δ) (hβ : β + δ ≤ 1) (hab : α ≤ β)
    (hdiam : ∀ v ∈ S, ∀ u ∈ cfCylinder v, ∀ t ∈ cfCylinder v, |u - t| ≤ δ)
    (hmeet : ∀ v ∈ S, ∃ t ∈ cfCylinder v, t ∈ Set.Ioo α β) :
    (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal) ≤ (β - α + 2 * δ) / Real.log 2 := by
  classical
  have hsub : ∀ v ∈ S, cfCylinder v ⊆ Set.Ioo (α - δ) (β + δ) := by
    intro v hv u huC
    obtain ⟨t, htC, htI⟩ := hmeet v hv
    have h := hdiam v hv u huC t htC
    rw [abs_le] at h
    exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hdisj : (S : Set (List ℕ)).PairwiseDisjoint (fun v => cfCylinder v) :=
    fun u hu v hv hne => cfCylinder_disjoint (by rw [hlen u hu, hlen v hv]) hne
  have hmeas : ∀ v ∈ S, MeasurableSet (cfCylinder v) := fun v _ => measurableSet_cfCylinder v
  have hunion : ∑ v ∈ S, gaussMeasure (cfCylinder v) = gaussMeasure (⋃ v ∈ S, cfCylinder v) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hle : gaussMeasure (⋃ v ∈ S, cfCylinder v) ≤ gaussMeasure (Set.Ioo (α - δ) (β + δ)) :=
    measure_mono (Set.iUnion₂_subset hsub)
  have hfin : gaussMeasure (Set.Ioo (α - δ) (β + δ)) ≠ ⊤ :=
    (measure_lt_top gaussMeasure _).ne
  have hreal : (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal)
      ≤ (gaussMeasure (Set.Ioo (α - δ) (β + δ))).toReal := by
    have hsum : (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal)
        = (∑ v ∈ S, gaussMeasure (cfCylinder v)).toReal := by
      rw [ENNReal.toReal_sum]
      intro v _
      exact (measure_lt_top gaussMeasure _).ne
    rw [hsum, hunion]
    exact ENNReal.toReal_mono hfin hle
  refine hreal.trans ?_
  have hmass := gaussMeasure_Ioo_toReal_le hα (by linarith) hβ
  calc (gaussMeasure (Set.Ioo (α - δ) (β + δ))).toReal ≤ (β + δ - (α - δ)) / Real.log 2 := hmass
    _ = (β - α + 2 * δ) / Real.log 2 := by ring_nf

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.dist_le_of_mem_cfCylinder
#print axioms NormalNumbers.VandeheyS7.sum_gaussMeasure_cover_le

end Audit
