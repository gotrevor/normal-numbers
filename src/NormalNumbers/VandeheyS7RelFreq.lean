/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RQ: RELATIVE equidistribution — a cylinder times a pulled-back interval

Route A's remaining scalar input is `RefCesaro` (S7-BF): the Cesàro average of
`blockAvg refState T w` along a CF-normal orbit converges to an `x`-independent limit.  That
observable is, after the digit truncation, a finite combination of the events

    `z ∈ I_v`  and  `G^{|v|} z ∈ J`        (`J` an interval — the state-after-`v` target)

— a cylinder times a *pulled-back interval*.  S7-EQ handles `J` alone (`v = []`); this module
handles the joint event, which is what the reference observable actually tests.

## The statement

    tendsto_blockCount_relSet_Ioo :
      blockCount (I_v ∩ G^{-|v|}(Ioo α β)) p x / p → γ (I_v ∩ G^{-|v|}(Ioo α β))

for every CF-normal `x` whose orbit stays in `(0,1)`, every word `v` and every `α, β`.

## The proof, and why it needs no distortion input

Run S7-EQ's two-sided cylinder squeeze *inside the fibre*: cover `Ioo α β` by the level-`M`,
digit-`≤B` cylinders `I_u` it meets, and note

    `I_v ∩ G^{-|v|}(I_u) ⊆ I_{v ++ u}`,      with equality at every point whose `|v|`-th
                                              iterate lies in `(0,1)` (`relSet_eq_append`),

so CF-normality of `x` evaluates the frequency of each piece EXACTLY (S7-WN), and the masses add
because same-length cylinders are disjoint.  The two edge corrections are paid by

    `relMass v E ≤ γ E`      (`relMass_le_gauss`)

— monotonicity plus `G`-invariance of `γ` (`gaussMeasure_preimage_iterate`).  That single
inequality is what replaces a bounded-distortion estimate: the *relative* mass of a thin annulus
is at most its *absolute* mass, with no constant.  Route B needed a `w`-uniform distortion constant
and provably could not have one (directive fact (ε)); the relative squeeze needs none.

## Guard rule

**Content locator.**  With `v = []` the statement degenerates to S7-EQ (`relSet [] A = Ioo 0 1 ∩ A`),
so all the new content is the interaction of the two coordinates, and it is consumed exactly once,
in `blockCount_relSet_eq_append` (the identification of the joint event with a longer cylinder) —
delete that step and the frequency of the joint event is not computable from normality at all.

**Degenerate cases.**  `β ≤ α` gives the empty set, `blockCount = 0 = γ`, and every bound is
`0 ≤ 0`.  `v = []` is allowed (and gives S7-EQ).  The exceptional (unbounded-digit) family is
never empty because `B` is chosen after `ε`.  `p = 0` makes both sides `0`.
-/
import NormalNumbers.VandeheyS7IntervalFreq
import NormalNumbers.VandeheyS7BlockForget

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

attribute [local instance] Classical.propDecidable

/-! ## The relative set and its mass -/

lemma cfDigit_iter_shift (x : ℝ) (n k : ℕ) : cfDigit (gaussMap^[n] x) k = cfDigit x (n + k) := by
  rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm]

/-- The event "`z` is in the cylinder `I_v`, and the point `G^{|v|}z` seen after reading `v`
lies in `A`". -/
noncomputable def relSet (v : List ℕ) (A : Set ℝ) : Set ℝ :=
  cfCylinder v ∩ gaussMap^[v.length] ⁻¹' A

lemma relSet_mono (v : List ℕ) {A B : Set ℝ} (h : A ⊆ B) : relSet v A ⊆ relSet v B :=
  Set.inter_subset_inter_right _ (Set.preimage_mono h)

lemma measurableSet_relSet (v : List ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (relSet v A) :=
  (measurableSet_cfCylinder v).inter ((measurable_gaussMap.iterate v.length) hA)

/-- The relative mass, as a real number. -/
noncomputable def relMass (v : List ℕ) (A : Set ℝ) : ℝ := (gaussMeasure (relSet v A)).toReal

lemma relMass_nonneg (v : List ℕ) (A : Set ℝ) : 0 ≤ relMass v A := ENNReal.toReal_nonneg

lemma relMass_mono (v : List ℕ) {A B : Set ℝ} (h : A ⊆ B) : relMass v A ≤ relMass v B :=
  ENNReal.toReal_mono (gaussMeasure_ne_top _) (measure_mono (relSet_mono v h))

/-- **The key inequality.**  The relative mass of a set is at most its absolute mass: the `G`
-invariance of `γ` alone, with no distortion constant. -/
lemma relMass_le_gauss (v : List ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    relMass v A ≤ (gaussMeasure A).toReal := by
  refine ENNReal.toReal_mono (gaussMeasure_ne_top _) ?_
  exact (measure_mono (Set.inter_subset_right)).trans
    (le_of_eq (gaussMeasure_preimage_iterate v.length hA))

lemma relMass_union_le (v : List ℕ) (A B : Set ℝ) :
    relMass v (A ∪ B) ≤ relMass v A + relMass v B := by
  have hsub : relSet v (A ∪ B) ⊆ relSet v A ∪ relSet v B := by
    rintro z ⟨hz, hzp⟩
    rcases hzp with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have h := (measure_mono hsub).trans (measure_union_le (μ := gaussMeasure) (relSet v A)
    (relSet v B))
  have := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.2 ⟨gaussMeasure_ne_top _, gaussMeasure_ne_top _⟩) h
  rwa [ENNReal.toReal_add (gaussMeasure_ne_top _) (gaussMeasure_ne_top _)] at this

/-! ## The relative set of a cylinder is a longer cylinder -/

lemma relSet_subset_append (v u : List ℕ) : relSet v (cfCylinder u) ⊆ cfCylinder (v ++ u) := by
  rintro z ⟨⟨hz01, hzd⟩, hzu⟩
  refine ⟨hz01, fun i hi => ?_⟩
  rw [List.length_append] at hi
  by_cases hiv : i < v.length
  · rw [List.getD_append _ _ _ _ hiv]
    exact hzd i hiv
  · have hle : v.length ≤ i := not_lt.1 hiv
    have hiu : i - v.length < u.length := by omega
    have hdig : cfDigit z i = cfDigit (gaussMap^[v.length] z) (i - v.length) := by
      rw [cfDigit_iter_shift]
      congr 1
      omega
    rw [List.getD_append_right _ _ _ _ hle, hdig]
    exact hzu.2 (i - v.length) hiu

lemma mem_relSet_of_mem_append {v u : List ℕ} {z : ℝ} (hz : z ∈ cfCylinder (v ++ u))
    (horb : gaussMap^[v.length] z ∈ Set.Ioo (0:ℝ) 1) : z ∈ relSet v (cfCylinder u) := by
  obtain ⟨hz01, hzd⟩ := hz
  refine ⟨⟨hz01, fun i hi => ?_⟩, ⟨horb, fun i hi => ?_⟩⟩
  · have h := hzd i (by rw [List.length_append]; omega)
    rwa [List.getD_append _ _ _ _ hi] at h
  · have h := hzd (v.length + i) (by rw [List.length_append]; omega)
    rw [List.getD_append_right _ _ _ _ (by omega)] at h
    simp only [Nat.add_sub_cancel_left] at h
    rw [cfDigit_iter_shift]
    exact h

/-- At every point whose `|v|`-th iterate is in `(0,1)`, the joint event and the longer cylinder
agree. -/
lemma relSet_mem_iff_append {v u : List ℕ} {z : ℝ}
    (horb : gaussMap^[v.length] z ∈ Set.Ioo (0:ℝ) 1) :
    z ∈ relSet v (cfCylinder u) ↔ z ∈ cfCylinder (v ++ u) :=
  ⟨fun h => relSet_subset_append v u h, fun h => mem_relSet_of_mem_append h horb⟩

/-- The two sets differ inside the rationals only, so they have the same mass. -/
lemma relMass_cfCylinder (v u : List ℕ) :
    relMass v (cfCylinder u) = (gaussMeasure (cfCylinder (v ++ u))).toReal := by
  have hsub : relSet v (cfCylinder u) ⊆ cfCylinder (v ++ u) := relSet_subset_append v u
  have hdiff : cfCylinder (v ++ u) \ relSet v (cfCylinder u)
      ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro z hz
    by_contra hzr
    have hirr : Irrational z := by
      rw [Irrational]; exact hzr
    have h01 : z ∈ Set.Ioo (0:ℝ) 1 := hz.1.1
    have horb := (irrational_orbit z hirr h01 v.length).2
    exact hz.2 (mem_relSet_of_mem_append hz.1 horb)
  have hnull : gaussMeasure (cfCylinder (v ++ u) \ relSet v (cfCylinder u)) = 0 :=
    measure_mono_null hdiff gaussMeasure_range_rat'
  have heq : gaussMeasure (relSet v (cfCylinder u)) = gaussMeasure (cfCylinder (v ++ u)) := by
    refine le_antisymm (measure_mono hsub) ?_
    calc gaussMeasure (cfCylinder (v ++ u))
        ≤ gaussMeasure (relSet v (cfCylinder u))
          + gaussMeasure (cfCylinder (v ++ u) \ relSet v (cfCylinder u)) :=
          by
            have h := measure_inter_add_sdiff (μ := gaussMeasure) (cfCylinder (v ++ u))
              (measurableSet_relSet v (measurableSet_cfCylinder u))
            rw [Set.inter_eq_self_of_subset_right hsub] at h
            exact h.ge
      _ = gaussMeasure (relSet v (cfCylinder u)) := by rw [hnull, add_zero]
  rw [relMass, heq]

/-! ## Additivity of the relative mass over a same-length family -/

lemma relSet_biUnion (v : List ℕ) (S : Finset (List ℕ)) :
    relSet v (⋃ u ∈ S, cfCylinder u) = ⋃ u ∈ S, relSet v (cfCylinder u) := by
  ext z
  simp only [relSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion₂, exists_prop]
  constructor
  · rintro ⟨hz, u, hu, hzu⟩; exact ⟨u, hu, hz, hzu⟩
  · rintro ⟨u, hu, hz, hzu⟩; exact ⟨hz, u, hu, hzu⟩

lemma relMass_biUnion_eq_sum (v : List ℕ) {S : Finset (List ℕ)} {M : ℕ}
    (hlen : ∀ u ∈ S, u.length = M) :
    relMass v (⋃ u ∈ S, cfCylinder u) = ∑ u ∈ S, relMass v (cfCylinder u) := by
  have hdisj : (S : Set (List ℕ)).PairwiseDisjoint (fun u => relSet v (cfCylinder u)) := by
    intro u hu u' hu' hne
    have hd : Disjoint (cfCylinder u) (cfCylinder u') :=
      cfCylinder_disjoint (by rw [hlen u hu, hlen u' hu']) hne
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    exact Set.disjoint_left.1 hd hz.2 hz'.2
  have h := measure_biUnion_finset (μ := gaussMeasure) hdisj
    (fun u _ => measurableSet_relSet v (measurableSet_cfCylinder u))
  rw [relMass, relSet_biUnion, h, ENNReal.toReal_sum (fun u _ => gaussMeasure_ne_top _)]
  rfl

/-! ## The orbit count of a relative cylinder -/

/-- At the orbit points of a full orbit the joint event IS the longer cylinder, so its counts
agree and CF-normality evaluates them. -/
lemma blockCount_relSet_eq_append {x : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (v u : List ℕ) (p : ℕ) :
    blockCount (relSet v (cfCylinder u)) p x = blockCount (cfCylinder (v ++ u)) p x := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmem : gaussMap^[v.length] (gaussMap^[m] x) ∈ Set.Ioo (0:ℝ) 1 := by
    rw [← Function.iterate_add_apply]
    exact horb _
  by_cases hz : gaussMap^[m] x ∈ relSet v (cfCylinder u)
  · rw [blockIndic_eq_one' hz, blockIndic_eq_one' ((relSet_mem_iff_append hmem).1 hz)]
  · rw [blockIndic_eq_zero' hz,
      blockIndic_eq_zero' (fun h => hz ((relSet_mem_iff_append hmem).2 h))]

/-- The frequency of a relative cylinder is its mass — exactly, from CF-normality. -/
theorem tendsto_blockCount_relSet_cfCylinder {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v u : List ℕ}
    (hpv : ∀ a ∈ v, 1 ≤ a) (hu : u ≠ []) (hpu : ∀ a ∈ u, 1 ≤ a) :
    Tendsto (fun p => blockCount (relSet v (cfCylinder u)) p x / (p : ℝ)) atTop
      (nhds (relMass v (cfCylinder u))) := by
  have hne : v ++ u ≠ [] := by
    intro h
    exact hu (List.append_eq_nil_iff.1 h).2
  have hpos : ∀ a ∈ v ++ u, 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hpv a h
    · exact hpu a h
  have h := blockCount_tendsto_of_isCFNormal hx horb (v ++ u) hne hpos
  rw [relMass_cfCylinder]
  exact h.congr (fun p => by rw [blockCount_relSet_eq_append horb v u p])

/-! ## The two mass bounds -/

/-- Every meeting bounded-digit cylinder lies inside the thickened interval. -/
lemma cfCylinder_subset_thick {B M : ℕ} (hM : 0 < M) {α β : ℝ} {u : List ℕ}
    (hu : u ∈ meetWords B M α β) :
    cfCylinder u ⊆ Set.Ioo (α - 2 / 2 ^ M) (β + 2 / 2 ^ M) := by
  obtain ⟨hub, t, htu, htI⟩ := Finset.mem_filter.1 hu
  intro y hy
  have hd := boundedWords_diam hM hub hy htu
  rw [abs_le] at hd
  exact ⟨by linarith [htI.1], by linarith [htI.2]⟩

lemma Ioo_thick_subset (α β δ : ℝ) :
    Set.Ioo (α - δ) (β + δ) ⊆ Set.Ioo α β ∪ (Set.Icc (α - δ) α ∪ Set.Icc β (β + δ)) := by
  intro y hy
  by_cases h1 : y ≤ α
  · exact Or.inr (Or.inl ⟨hy.1.le, h1⟩)
  · by_cases h2 : β ≤ y
    · exact Or.inr (Or.inr ⟨h2, hy.2.le⟩)
    · exact Or.inl ⟨not_le.1 h1, not_le.1 h2⟩

/-- **Outer mass bound**, relative version: the meeting family's relative mass exceeds the
target's by at most the two edge masses — and those are bounded ABSOLUTELY, by `G`-invariance. -/
lemma sum_relMass_meetWords_le {B M : ℕ} (hM : 0 < M) (v : List ℕ) (α β : ℝ) :
    ∑ u ∈ meetWords B M α β, relMass v (cfCylinder u)
      ≤ relMass v (Set.Ioo α β) + 2 * (2 / 2 ^ M) / Real.log 2 := by
  set δ : ℝ := 2 / 2 ^ M with hδ
  have hδ0 : (0:ℝ) ≤ δ := by rw [hδ]; positivity
  have hsum : ∑ u ∈ meetWords B M α β, relMass v (cfCylinder u)
      = relMass v (⋃ u ∈ meetWords B M α β, cfCylinder u) :=
    (relMass_biUnion_eq_sum v (M := M)
      (fun u hu => boundedWords_len (Finset.mem_filter.1 hu).1)).symm
  have hsub : (⋃ u ∈ meetWords B M α β, cfCylinder u) ⊆ Set.Ioo (α - δ) (β + δ) :=
    Set.iUnion₂_subset fun u hu => cfCylinder_subset_thick hM hu
  have hE1 : relMass v (Set.Icc (α - δ) α) ≤ δ / Real.log 2 :=
    le_trans (relMass_le_gauss v measurableSet_Icc) (gaussMeasure_Icc_toReal_le hδ0 (by linarith))
  have hE2 : relMass v (Set.Icc β (β + δ)) ≤ δ / Real.log 2 :=
    le_trans (relMass_le_gauss v measurableSet_Icc) (gaussMeasure_Icc_toReal_le hδ0 (by linarith))
  have hstep : relMass v (Set.Ioo (α - δ) (β + δ))
      ≤ relMass v (Set.Ioo α β) + (relMass v (Set.Icc (α - δ) α) + relMass v (Set.Icc β (β + δ)))
        := by
    refine le_trans (relMass_mono v (Ioo_thick_subset α β δ)) ?_
    refine le_trans (relMass_union_le v _ _) ?_
    have := relMass_union_le v (Set.Icc (α - δ) α) (Set.Icc β (β + δ))
    linarith
  have hmono := relMass_mono v hsub
  have harith : 2 * δ / Real.log 2 = δ / Real.log 2 + δ / Real.log 2 := by ring
  rw [hsum]
  rw [hδ] at harith ⊢
  linarith

/-- **Inner mass bound**, relative version. -/
lemma relMass_le_sum_insideWords {B M : ℕ} (hM : 0 < M) (v : List ℕ) (α β : ℝ) :
    relMass v (Set.Ioo α β)
      ≤ (∑ u ∈ insideWords B M α β, relMass v (cfCylinder u))
        + 2 * (2 / 2 ^ M) / Real.log 2
        + (1 - ∑ u ∈ boundedWords B M, (gaussMeasure (cfCylinder u)).toReal) := by
  set δ : ℝ := 2 / 2 ^ M with hδ
  have hδ0 : (0:ℝ) ≤ δ := by rw [hδ]; positivity
  set E : Set ℝ := ⋃ u ∈ boundedWords B M, cfCylinder u with hE
  have hcover : Set.Ioo α β
      ⊆ (⋃ u ∈ insideWords B M α β, cfCylinder u)
        ∪ ((Set.Icc α (α + δ) ∪ Set.Icc (β - δ) β) ∪ Eᶜ) := by
    intro y hy
    by_cases hyE : y ∈ E
    · obtain ⟨u, hu, hyu⟩ := Set.mem_iUnion₂.1 hyE
      by_cases hthin : y ∈ Set.Ioo (α + δ) (β - δ)
      · refine Or.inl (Set.mem_iUnion₂.2 ⟨u, Finset.mem_filter.2 ⟨hu, ?_⟩, hyu⟩)
        intro t ht
        have hd := boundedWords_diam hM hu ht hyu
        rw [abs_le] at hd
        exact ⟨by linarith [hthin.1], by linarith [hthin.2]⟩
      · simp only [Set.mem_Ioo, not_and_or, not_lt] at hthin
        rcases hthin with h | h
        · exact Or.inr (Or.inl (Or.inl ⟨hy.1.le, h⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨h, hy.2.le⟩))
    · exact Or.inr (Or.inr hyE)
  have hins : ∑ u ∈ insideWords B M α β, relMass v (cfCylinder u)
      = relMass v (⋃ u ∈ insideWords B M α β, cfCylinder u) :=
    (relMass_biUnion_eq_sum v (M := M)
      (fun u hu => boundedWords_len (Finset.mem_filter.1 hu).1)).symm
  have hE1 : relMass v (Set.Icc α (α + δ)) ≤ δ / Real.log 2 :=
    le_trans (relMass_le_gauss v measurableSet_Icc) (gaussMeasure_Icc_toReal_le hδ0 (by linarith))
  have hE2 : relMass v (Set.Icc (β - δ) β) ≤ δ / Real.log 2 :=
    le_trans (relMass_le_gauss v measurableSet_Icc) (gaussMeasure_Icc_toReal_le hδ0 (by linarith))
  have hEc : relMass v Eᶜ
      ≤ 1 - ∑ u ∈ boundedWords B M, (gaussMeasure (cfCylinder u)).toReal := by
    refine le_trans (relMass_le_gauss v (measurableSet_biUnion_cfCylinder _).compl) ?_
    rw [hE, gaussMeasure_compl_boundedWords_toReal]
  have hchain : relMass v (Set.Ioo α β)
      ≤ relMass v (⋃ u ∈ insideWords B M α β, cfCylinder u)
        + ((relMass v (Set.Icc α (α + δ)) + relMass v (Set.Icc (β - δ) β)) + relMass v Eᶜ) := by
    refine le_trans (relMass_mono v hcover) ?_
    refine le_trans (relMass_union_le v _ _) ?_
    have h1 := relMass_union_le v (Set.Icc α (α + δ) ∪ Set.Icc (β - δ) β) Eᶜ
    have h2 := relMass_union_le v (Set.Icc α (α + δ)) (Set.Icc (β - δ) β)
    linarith
  have harith : 2 * δ / Real.log 2 = δ / Real.log 2 + δ / Real.log 2 := by ring
  rw [hins]
  rw [hδ] at harith ⊢
  linarith

/-! ## The two count bounds -/

/-- Pointwise domination, relative version. -/
lemma blockIndic_relSet_le_cover (B M : ℕ) (v : List ℕ) (α β : ℝ) (z : ℝ) :
    blockIndic (relSet v (Set.Ioo α β)) z
      ≤ (∑ u ∈ meetWords B M α β, blockIndic (relSet v (cfCylinder u)) z)
        + (1 - blockIndic (gaussMap^[v.length] ⁻¹' (⋃ u ∈ boundedWords B M, cfCylinder u)) z) := by
  set E : Set ℝ := ⋃ u ∈ boundedWords B M, cfCylinder u with hE
  have hnn : 0 ≤ ∑ u ∈ meetWords B M α β, blockIndic (relSet v (cfCylinder u)) z :=
    Finset.sum_nonneg fun u _ => blockIndic_nonneg _ _
  have hle1 := blockIndic_le_one (gaussMap^[v.length] ⁻¹' E) z
  by_cases hz : z ∈ relSet v (Set.Ioo α β)
  · by_cases hw : gaussMap^[v.length] z ∈ E
    · obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 hw
      have humeet : u ∈ meetWords B M α β :=
        Finset.mem_filter.2 ⟨hu, ⟨gaussMap^[v.length] z, hzu, hz.2⟩⟩
      have hzrel : z ∈ relSet v (cfCylinder u) := ⟨hz.1, hzu⟩
      have hterm : (1:ℝ) ≤ ∑ u' ∈ meetWords B M α β, blockIndic (relSet v (cfCylinder u')) z := by
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun u' => blockIndic (relSet v (cfCylinder u')) z)
          (fun u' _ => blockIndic_nonneg _ _) humeet)
        rw [blockIndic_eq_one' hzrel]
      have hone : blockIndic (gaussMap^[v.length] ⁻¹' E) z = 1 :=
        blockIndic_eq_one' (by exact hw)
      rw [blockIndic_eq_one' hz, hone]
      linarith
    · rw [blockIndic_eq_one' hz, blockIndic_eq_zero' (show z ∉ gaussMap^[v.length] ⁻¹' E from hw)]
      linarith
  · rw [blockIndic_eq_zero' hz]
    linarith

lemma blockCount_relSet_le_cover (B M : ℕ) (v : List ℕ) (α β : ℝ) (p : ℕ) (x : ℝ) :
    blockCount (relSet v (Set.Ioo α β)) p x
      ≤ (∑ u ∈ meetWords B M α β, blockCount (relSet v (cfCylinder u)) p x)
        + ((p : ℝ)
          - blockCount (gaussMap^[v.length] ⁻¹' (⋃ u ∈ boundedWords B M, cfCylinder u)) p x) := by
  simp only [blockCount_apply]
  have hswap : ∑ u ∈ meetWords B M α β,
        ∑ k ∈ range p, blockIndic (relSet v (cfCylinder u)) (gaussMap^[k] x)
      = ∑ k ∈ range p,
        ∑ u ∈ meetWords B M α β, blockIndic (relSet v (cfCylinder u)) (gaussMap^[k] x) :=
    Finset.sum_comm
  rw [show ((p : ℝ)) = ∑ _k ∈ range p, (1:ℝ) by simp, ← Finset.sum_sub_distrib, hswap,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => blockIndic_relSet_le_cover B M v α β _

/-- The pulled-back exceptional family's count differs from the family's own by at most the
shift. -/
lemma abs_blockCount_preimage_sub_le {A : Set ℝ} (j p : ℕ) (x : ℝ) :
    |blockCount (gaussMap^[j] ⁻¹' A) p x - blockCount A p x| ≤ (j : ℝ) := by
  set f : ℕ → ℝ := fun n => blockIndic A (gaussMap^[n] x) with hf
  have h1 : blockCount (gaussMap^[j] ⁻¹' A) p x = ∑ m ∈ range p, f (m + j) := by
    rw [blockCount_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hf]
    simp only
    rw [← blockIndic_iterate, ← Function.iterate_add_apply]
    congr 2
    omega
  have h2 : blockCount A p x = ∑ n ∈ range p, f n := rfl
  rw [h1, h2]
  exact MapState.abs_sum_shift_sub_le (f := f) (fun n => blockIndic_nonneg _ _)
    (fun n => blockIndic_le_one _ _) p j

/-! ## The squeeze -/

/-- **Upper half.** -/
theorem eventually_blockCount_relSet_div_le {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    {α β : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (relSet v (Set.Ioo α β)) p x / (p : ℝ) ≤ relMass v (Set.Ioo α β) + ε := by
  obtain ⟨M, hM0, hMε⟩ := exists_level (show (0:ℝ) < ε / 5 by linarith)
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt M (show (0:ℝ) < ε / 5 by linarith)
  set E : Set ℝ := ⋃ u ∈ boundedWords B M, cfCylinder u with hE
  set mG := ∑ u ∈ boundedWords B M, (gaussMeasure (cfCylinder u)).toReal with hmG
  set mS := ∑ u ∈ meetWords B M α β, relMass v (cfCylinder u) with hmS
  have hmass : mS ≤ relMass v (Set.Ioo α β) + ε / 5 := by
    refine le_trans (sum_relMass_meetWords_le hM0 v α β) ?_
    linarith
  -- the meeting family's frequency
  have hfS : Tendsto (fun p => ∑ u ∈ meetWords B M α β,
      blockCount (relSet v (cfCylinder u)) p x / (p : ℝ)) atTop (nhds mS) := by
    refine tendsto_finsetSum _ fun u hu => ?_
    exact tendsto_blockCount_relSet_cfCylinder hx horb hpv
      (boundedWords_ne_nil hM0 (Finset.mem_filter.1 hu).1)
      (boundedWords_pos (Finset.mem_filter.1 hu).1)
  -- the exceptional family's frequency
  have hfG : Tendsto (fun p => blockCount E p x / (p : ℝ)) atTop (nhds mG) := by
    rw [hE, hmG]
    exact tendsto_windowFreq (S := boundedWords B M) hx horb hM0
      (fun u hu => boundedWords_len hu) (fun u hu => boundedWords_pos hu)
  have hshift : ∀ᶠ p : ℕ in atTop, ((v.length : ℝ)) / (p : ℝ) ≤ ε / 5 := by
    have := (tendsto_const_div_atTop_nhds_zero_nat ((v.length : ℝ))).eventually
      (eventually_lt_nhds (show (0:ℝ) < ε / 5 by linarith))
    filter_upwards [this] with p hp using hp.le
  have hevS := hfS.eventually (eventually_lt_nhds (show mS < mS + ε / 5 by linarith))
  have hevG := hfG.eventually (eventually_gt_nhds (show mG - ε / 5 < mG by linarith))
  filter_upwards [hevS, hevG, hshift, eventually_gt_atTop 0] with p hpS hpG hpshift hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hcover := blockCount_relSet_le_cover B M v α β p x
  have hpre : blockCount E p x - (v.length : ℝ)
      ≤ blockCount (gaussMap^[v.length] ⁻¹' E) p x := by
    have h := abs_blockCount_preimage_sub_le (A := E) v.length p x
    rw [abs_le] at h
    linarith [h.1]
  have hdiv : blockCount (relSet v (Set.Ioo α β)) p x / (p : ℝ)
      ≤ (∑ u ∈ meetWords B M α β, blockCount (relSet v (cfCylinder u)) p x / (p : ℝ))
        + (1 - blockCount E p x / (p : ℝ)) + (v.length : ℝ) / (p : ℝ) := by
    rw [div_le_iff₀ hpR]
    have hexp : ((∑ u ∈ meetWords B M α β, blockCount (relSet v (cfCylinder u)) p x / (p : ℝ))
        + (1 - blockCount E p x / (p : ℝ)) + (v.length : ℝ) / (p : ℝ)) * (p : ℝ)
        = (∑ u ∈ meetWords B M α β, blockCount (relSet v (cfCylinder u)) p x)
          + ((p : ℝ) - blockCount E p x) + (v.length : ℝ) := by
      rw [add_mul, add_mul, Finset.sum_mul]
      have h1 : ∀ u : List ℕ, blockCount (relSet v (cfCylinder u)) p x / (p : ℝ) * (p : ℝ)
          = blockCount (relSet v (cfCylinder u)) p x := fun u => div_mul_cancel₀ _ hpR.ne'
      simp only [h1]
      field_simp
    rw [hexp]
    linarith
  have hmG' : 1 - blockCount E p x / (p : ℝ) ≤ 1 - mG + ε / 5 := by linarith
  have hbnd : (1:ℝ) - mG ≤ ε / 5 := by rw [hmG] at hB ⊢; linarith
  linarith

/-- **Lower half.** -/
theorem eventually_le_blockCount_relSet_div {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    {α β : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      relMass v (Set.Ioo α β) - ε ≤ blockCount (relSet v (Set.Ioo α β)) p x / (p : ℝ) := by
  obtain ⟨M, hM0, hMε⟩ := exists_level (show (0:ℝ) < ε / 4 by linarith)
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt M (show (0:ℝ) < ε / 4 by linarith)
  set mG := ∑ u ∈ boundedWords B M, (gaussMeasure (cfCylinder u)).toReal with hmG
  set mI := ∑ u ∈ insideWords B M α β, relMass v (cfCylinder u) with hmI
  have hmass : relMass v (Set.Ioo α β) ≤ mI + ε / 4 + (1 - mG) := by
    refine le_trans (relMass_le_sum_insideWords (B := B) hM0 v α β) ?_
    rw [← hmI, ← hmG]
    linarith
  have hfI : Tendsto (fun p => ∑ u ∈ insideWords B M α β,
      blockCount (relSet v (cfCylinder u)) p x / (p : ℝ)) atTop (nhds mI) := by
    refine tendsto_finsetSum _ fun u hu => ?_
    exact tendsto_blockCount_relSet_cfCylinder hx horb hpv
      (boundedWords_ne_nil hM0 (Finset.mem_filter.1 hu).1)
      (boundedWords_pos (Finset.mem_filter.1 hu).1)
  have hevI := hfI.eventually (eventually_gt_nhds (show mI - ε / 4 < mI by linarith))
  filter_upwards [hevI, eventually_gt_atTop 0] with p hpI hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- the inside family's relative sets are disjoint and contained in the target
  have hsub : (⋃ u ∈ insideWords B M α β, cfCylinder u) ⊆ Set.Ioo α β :=
    Set.iUnion₂_subset fun u hu => (Finset.mem_filter.1 hu).2
  have hmono : blockCount (relSet v (⋃ u ∈ insideWords B M α β, cfCylinder u)) p x
      ≤ blockCount (relSet v (Set.Ioo α β)) p x :=
    blockCount_mono (relSet_mono v hsub) p x
  have hadd : blockCount (relSet v (⋃ u ∈ insideWords B M α β, cfCylinder u)) p x
      = ∑ u ∈ insideWords B M α β, blockCount (relSet v (cfCylinder u)) p x := by
    simp only [blockCount_apply]
    have hswap : ∑ u ∈ insideWords B M α β,
          ∑ k ∈ range p, blockIndic (relSet v (cfCylinder u)) (gaussMap^[k] x)
        = ∑ k ∈ range p,
          ∑ u ∈ insideWords B M α β, blockIndic (relSet v (cfCylinder u)) (gaussMap^[k] x) :=
      Finset.sum_comm
    rw [hswap]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [relSet_biUnion]
    have hdisj : ∀ u ∈ insideWords B M α β, ∀ u' ∈ insideWords B M α β, u ≠ u' →
        Disjoint (relSet v (cfCylinder u)) (relSet v (cfCylinder u')) := by
      intro u hu u' hu' hne
      have hd : Disjoint (cfCylinder u) (cfCylinder u') :=
        cfCylinder_disjoint (by
          rw [boundedWords_len (Finset.mem_filter.1 hu).1,
            boundedWords_len (Finset.mem_filter.1 hu').1]) hne
      exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 hd hz.2 hz'.2
    by_cases hz : ∃ u ∈ insideWords B M α β, gaussMap^[k] x ∈ relSet v (cfCylinder u)
    · obtain ⟨u, hu, hzu⟩ := hz
      have hmem : gaussMap^[k] x ∈ ⋃ u' ∈ insideWords B M α β, relSet v (cfCylinder u') :=
        Set.mem_iUnion₂.2 ⟨u, hu, hzu⟩
      have hsingle : ∑ u' ∈ insideWords B M α β,
            blockIndic (relSet v (cfCylinder u')) (gaussMap^[k] x)
          = blockIndic (relSet v (cfCylinder u)) (gaussMap^[k] x) := by
        refine Finset.sum_eq_single_of_mem u hu fun u' hu' hne => ?_
        exact blockIndic_eq_zero' fun h => Set.disjoint_left.1 (hdisj u' hu' u hu hne) h hzu
      rw [blockIndic_eq_one' hmem, hsingle, blockIndic_eq_one' hzu]
    · push_neg at hz
      have hmem : gaussMap^[k] x ∉ ⋃ u' ∈ insideWords B M α β, relSet v (cfCylinder u') := by
        intro h
        obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 h
        exact hz u hu hzu
      rw [blockIndic_eq_zero' hmem, Finset.sum_eq_zero]
      intro u hu
      exact blockIndic_eq_zero' (hz u hu)
  have hbnd : (1:ℝ) - mG ≤ ε / 4 := by rw [hmG] at hB ⊢; linarith
  have hdiv : (∑ u ∈ insideWords B M α β, blockCount (relSet v (cfCylinder u)) p x) / (p : ℝ)
      ≤ blockCount (relSet v (Set.Ioo α β)) p x / (p : ℝ) := by
    rw [div_le_div_iff_of_pos_right hpR, ← hadd]
    exact hmono
  have hsplit : (∑ u ∈ insideWords B M α β, blockCount (relSet v (cfCylinder u)) p x) / (p : ℝ)
      = ∑ u ∈ insideWords B M α β, blockCount (relSet v (cfCylinder u)) p x / (p : ℝ) :=
    Finset.sum_div _ _ _
  rw [hsplit] at hdiv
  linarith

/-- **S7-RQ.**  RELATIVE equidistribution: the joint event "`z ∈ I_v` and `G^{|v|}z ∈ (α,β)`" has
orbit frequency equal to its Gauss mass, for every CF-normal `x` with a full orbit.  No absolute
continuity, no distortion constant, no ergodic theorem. -/
theorem tendsto_blockCount_relSet_Ioo {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    (α β : ℝ) :
    Tendsto (fun p => blockCount (relSet v (Set.Ioo α β)) p x / (p : ℝ)) atTop
      (nhds (relMass v (Set.Ioo α β))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU := eventually_blockCount_relSet_div_le hx horb hpv (α := α) (β := β)
    (show (0:ℝ) < ε / 2 by linarith)
  have hL := eventually_le_blockCount_relSet_div hx horb hpv (α := α) (β := β)
    (show (0:ℝ) < ε / 2 by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hU.and hL)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hu, hl⟩ := hN n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Robustness: the target only matters up to the rationals

The reference observable's actual target is `s.mob ⁻¹' I_w ∩ (0,1)` (`mapBlockSet s w 0`), which is
an interval only up to a countable set: the cylinder `I_w` is `uIoo E₀ E₁` off the rationals.  That
is harmless — a CF-normal orbit is an orbit of irrationals, and `ℚ` is `γ`-null — so the frequency
and the mass of such a target are those of the interval.  This is the bridge from S7-RQ to the
reference observable. -/

lemma gaussMeasure_eq_of_diff_subset_rat {S T : Set ℝ} (hSm : MeasurableSet S)
    (hTm : MeasurableSet T) (hST : S \ T ⊆ Set.range ((↑) : ℚ → ℝ))
    (hTS : T \ S ⊆ Set.range ((↑) : ℚ → ℝ)) : gaussMeasure S = gaussMeasure T := by
  have hnull : ∀ {U V : Set ℝ}, U \ V ⊆ Set.range ((↑) : ℚ → ℝ) → gaussMeasure (U \ V) = 0 :=
    fun h => measure_mono_null h gaussMeasure_range_rat'
  have hle : ∀ {U V : Set ℝ}, MeasurableSet V → U \ V ⊆ Set.range ((↑) : ℚ → ℝ) →
      gaussMeasure U ≤ gaussMeasure V := by
    intro U V hV hUV
    have h := measure_inter_add_sdiff (μ := gaussMeasure) U hV
    rw [hnull hUV, add_zero] at h
    rw [← h]
    exact measure_mono Set.inter_subset_right
  exact le_antisymm (hle hTm hST) (hle hSm hTS)

/-- **Rational-blind counting.**  Along an irrational full orbit, a target may be replaced by any
set agreeing with it at the irrational points of `(0,1)`. -/
lemma blockCount_relSet_congr_of_agree {x : ℝ} (hirr : Irrational x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (v : List ℕ) {A A' : Set ℝ}
    (hagree : ∀ z, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → (z ∈ A ↔ z ∈ A')) (p : ℕ) :
    blockCount (relSet v A) p x = blockCount (relSet v A') p x := by
  have h01 : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using horb 0
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hpt : gaussMap^[v.length] (gaussMap^[m] x) = gaussMap^[m + v.length] x := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hptirr : Irrational (gaussMap^[m + v.length] x) :=
    (irrational_orbit x hirr h01 (m + v.length)).1
  have hiff := hagree _ hptirr (horb (m + v.length))
  have hset : gaussMap^[m] x ∈ relSet v A ↔ gaussMap^[m] x ∈ relSet v A' := by
    simp only [relSet, Set.mem_inter_iff, Set.mem_preimage, hpt]
    exact and_congr_right fun _ => hiff
  by_cases hz : gaussMap^[m] x ∈ relSet v A
  · rw [blockIndic_eq_one' hz, blockIndic_eq_one' (hset.1 hz)]
  · rw [blockIndic_eq_zero' hz, blockIndic_eq_zero' (fun h => hz (hset.2 h))]

/-- A CF-normal number is irrational (`VandeheySmith`), packaged for use here. -/
lemma irrational_of_isCFNormal {x : ℝ} (hx : IsCFNormal x) : Irrational x := by
  by_contra h
  exact Literature.not_isCFNormal_of_not_irrational h hx

/-- **S7-RQ′, the form the reference observable uses.**  A target that is an interval off the
rationals has the frequency, and the mass, of that interval. -/
theorem tendsto_blockCount_relSet_of_agree {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    {A : Set ℝ} (hAm : MeasurableSet A) (hA : A ⊆ Set.Ioo (0:ℝ) 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hagree : ∀ z, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → (z ∈ A ↔ z ∈ Set.Ioo a b)) :
    Tendsto (fun p => blockCount (relSet v A) p x / (p : ℝ)) atTop
      (nhds (relMass v (Set.Ioo a b))) := by
  have hirr := irrational_of_isCFNormal hx
  refine (tendsto_blockCount_relSet_Ioo hx horb hpv a b).congr fun p => ?_
  rw [blockCount_relSet_congr_of_agree hirr horb v hagree p]

/-- And the two masses agree, so the limit can equally be named by the target itself. -/
theorem relMass_eq_of_agree (v : List ℕ) {A : Set ℝ} (hAm : MeasurableSet A)
    (hA : A ⊆ Set.Ioo (0:ℝ) 1) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hagree : ∀ z, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → (z ∈ A ↔ z ∈ Set.Ioo a b)) :
    relMass v A = relMass v (Set.Ioo a b) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0:ℝ) 1 := fun y hy =>
    ⟨lt_of_le_of_lt ha hy.1, lt_of_lt_of_le hy.2 hb⟩
  have hdiff : ∀ {U V : Set ℝ}, U ⊆ Set.Ioo (0:ℝ) 1 →
      (∀ z, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → (z ∈ U → z ∈ V)) →
      U \ V ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro U V hU himp z hz
    by_contra hzr
    exact hz.2 (himp z (by rw [Irrational]; exact hzr) (hU hz.1) hz.1)
  have h1 : relSet v A \ relSet v (Set.Ioo a b) ⊆ gaussMap^[v.length] ⁻¹'
      (A \ Set.Ioo a b) := by
    rintro z ⟨⟨hzv, hzA⟩, hz⟩
    exact ⟨hzA, fun h => hz ⟨hzv, h⟩⟩
  have h2 : relSet v (Set.Ioo a b) \ relSet v A ⊆ gaussMap^[v.length] ⁻¹'
      (Set.Ioo a b \ A) := by
    rintro z ⟨⟨hzv, hzA⟩, hz⟩
    exact ⟨hzA, fun h => hz ⟨hzv, h⟩⟩
  have hnullA : gaussMeasure (gaussMap^[v.length] ⁻¹' (A \ Set.Ioo a b)) = 0 := by
    refine measure_mono_null (Set.preimage_mono
      (hdiff hA fun z hzi hz01 hzA => (hagree z hzi hz01).1 hzA)) ?_
    rw [gaussMeasure_preimage_iterate v.length (by
      exact (Set.countable_range ((↑) : ℚ → ℝ)).measurableSet)]
    exact gaussMeasure_range_rat'
  have hnullB : gaussMeasure (gaussMap^[v.length] ⁻¹' (Set.Ioo a b \ A)) = 0 := by
    refine measure_mono_null (Set.preimage_mono
      (hdiff hsub fun z hzi hz01 hzA => (hagree z hzi hz01).2 hzA)) ?_
    rw [gaussMeasure_preimage_iterate v.length (by
      exact (Set.countable_range ((↑) : ℚ → ℝ)).measurableSet)]
    exact gaussMeasure_range_rat'
  have hSm := measurableSet_relSet v hAm
  have hTm := measurableSet_relSet v (measurableSet_Ioo (a := a) (b := b))
  have heq : gaussMeasure (relSet v A) = gaussMeasure (relSet v (Set.Ioo a b)) := by
    refine le_antisymm ?_ ?_
    · have h := measure_inter_add_sdiff (μ := gaussMeasure) (relSet v A) hTm
      rw [measure_mono_null h1 hnullA, add_zero] at h
      rw [← h]
      exact measure_mono Set.inter_subset_right
    · have h := measure_inter_add_sdiff (μ := gaussMeasure) (relSet v (Set.Ioo a b)) hSm
      rw [measure_mono_null h2 hnullB, add_zero] at h
      rw [← h]
      exact measure_mono Set.inter_subset_right
  rw [relMass, relMass, heq]

/-! ## Robustness at the endpoints: a point has zero frequency

The reference observable's target is an interval off the rationals only when the state's Möbius map
has rational entries; over `ℤ[φ]` it can differ at the TWO preimages of the cylinder's endpoints.
Two points cost nothing either: a CF-normal orbit spends zero frequency at any single point,
because it spends `γ`-mass on every shrinking interval around it. -/

lemma relMass_Ioo_le_width (v : List ℕ) {c δ : ℝ} (hδ : 0 ≤ δ) :
    relMass v (Set.Ioo (c - δ) (c + δ)) ≤ 2 * δ / Real.log 2 := by
  refine le_trans (relMass_mono v (Set.Ioo_subset_Icc_self)) ?_
  refine le_trans (relMass_le_gauss v measurableSet_Icc) ?_
  exact gaussMeasure_Icc_toReal_le (by linarith) (by linarith)

/-- **A point has zero frequency.** -/
theorem tendsto_blockCount_relSet_singleton {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    (c : ℝ) :
    Tendsto (fun p => blockCount (relSet v {c}) p x / (p : ℝ)) atTop (nhds 0) := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε * Real.log 2 / 8 with hδdef
  have hδ0 : (0:ℝ) < δ := by rw [hδdef]; positivity
  have hmass : relMass v (Set.Ioo (c - δ) (c + δ)) ≤ ε / 4 := by
    refine le_trans (relMass_Ioo_le_width v hδ0.le) ?_
    rw [hδdef, div_le_iff₀ hlog]
    ring_nf
    nlinarith [hlog]
  have hfrq := tendsto_blockCount_relSet_Ioo hx horb hpv (c - δ) (c + δ)
  have hev := hfrq.eventually (eventually_lt_nhds
    (show relMass v (Set.Ioo (c - δ) (c + δ)) < relMass v (Set.Ioo (c - δ) (c + δ)) + ε / 4 by
      linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  refine ⟨N, fun p hp => ?_⟩
  obtain ⟨hpev, hp0⟩ := hN p hp
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hsub : ({c} : Set ℝ) ⊆ Set.Ioo (c - δ) (c + δ) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨by linarith [hy ▸ (le_refl c)], by linarith [hy ▸ (le_refl c)]⟩
  have hmono : blockCount (relSet v {c}) p x ≤ blockCount (relSet v (Set.Ioo (c - δ) (c + δ))) p x :=
    blockCount_mono (relSet_mono v hsub) p x
  have hnn : 0 ≤ blockCount (relSet v {c}) p x := by
    rw [blockCount_apply]
    exact Finset.sum_nonneg fun k _ => blockIndic_nonneg _ _
  have hdiv : blockCount (relSet v {c}) p x / (p : ℝ)
      ≤ blockCount (relSet v (Set.Ioo (c - δ) (c + δ))) p x / (p : ℝ) := by
    rw [div_le_div_iff_of_pos_right hpR]; exact hmono
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hnn hpR.le)]
  linarith

/-- **The sandwich form.**  A target squeezed between an open interval and its closure has the
frequency, and the mass, of the interval.  This is the shape the reference observable's target has
(the two endpoint preimages are the only ambiguity). -/
theorem tendsto_blockCount_relSet_of_sandwich {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    {A : Set ℝ} {a b : ℝ} (hlo : Set.Ioo a b ⊆ A) (hhi : A ⊆ Set.Icc a b) :
    Tendsto (fun p => blockCount (relSet v A) p x / (p : ℝ)) atTop
      (nhds (relMass v (Set.Ioo a b))) := by
  have hIcc : Set.Icc a b ⊆ Set.Ioo a b ∪ ({a} ∪ {b}) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · exact Or.inr (Or.inl (by rw [Set.mem_singleton_iff, ← h]))
    · rcases eq_or_lt_of_le hy.2 with h' | h'
      · exact Or.inr (Or.inr (by rw [Set.mem_singleton_iff, h']))
      · exact Or.inl ⟨h, h'⟩
  have hlow := tendsto_blockCount_relSet_Ioo hx horb hpv a b
  have hsa := tendsto_blockCount_relSet_singleton hx horb hpv a
  have hsb := tendsto_blockCount_relSet_singleton hx horb hpv b
  have hup : Tendsto (fun p => (blockCount (relSet v (Set.Ioo a b)) p x
      + (blockCount (relSet v {a}) p x + blockCount (relSet v {b}) p x)) / (p : ℝ)) atTop
      (nhds (relMass v (Set.Ioo a b))) := by
    have h := hlow.add (hsa.add hsb)
    rw [add_zero, add_zero] at h
    refine h.congr fun p => ?_
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun p => ?_) (fun p => ?_)
  · rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    · have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
      rw [div_le_div_iff_of_pos_right hpR]
      exact blockCount_mono (relSet_mono v hlo) p x
  · rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    · have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
      rw [div_le_div_iff_of_pos_right hpR]
      have hstep : blockCount (relSet v A) p x
          ≤ blockCount (relSet v (Set.Ioo a b ∪ ({a} ∪ {b}))) p x :=
        blockCount_mono (relSet_mono v (hhi.trans hIcc)) p x
      refine hstep.trans ?_
      have hle : ∀ (U V : Set ℝ) (q : ℕ),
          blockCount (relSet v (U ∪ V)) q x ≤ blockCount (relSet v U) q x
            + blockCount (relSet v V) q x := by
        intro U V q
        simp only [blockCount_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hU : gaussMap^[k] x ∈ relSet v U
        · have : gaussMap^[k] x ∈ relSet v (U ∪ V) := ⟨hU.1, Or.inl hU.2⟩
          rw [blockIndic_eq_one' this, blockIndic_eq_one' hU]
          linarith [blockIndic_nonneg (relSet v V) (gaussMap^[k] x)]
        · by_cases hV : gaussMap^[k] x ∈ relSet v V
          · have : gaussMap^[k] x ∈ relSet v (U ∪ V) := ⟨hV.1, Or.inr hV.2⟩
            rw [blockIndic_eq_one' this, blockIndic_eq_one' hV]
            linarith [blockIndic_nonneg (relSet v U) (gaussMap^[k] x)]
          · have hnot : gaussMap^[k] x ∉ relSet v (U ∪ V) := by
              rintro ⟨h1, h2⟩
              rcases h2 with h | h
              · exact hU ⟨h1, h⟩
              · exact hV ⟨h1, h⟩
            rw [blockIndic_eq_zero' hnot, blockIndic_eq_zero' hU, blockIndic_eq_zero' hV]
            norm_num
      exact le_trans (hle _ _ p) (by linarith [hle ({a} : Set ℝ) ({b} : Set ℝ) p])

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.relMass_le_gauss
#print axioms NormalNumbers.VandeheyS7.relMass_cfCylinder
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_relSet_cfCylinder
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_relSet_Ioo
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_relSet_of_agree
#print axioms NormalNumbers.VandeheyS7.relMass_eq_of_agree
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_relSet_singleton
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_relSet_of_sandwich

end Audit

section Audit2
#print axioms NormalNumbers.VandeheyS7.eventually_blockCount_relSet_div_le
#print axioms NormalNumbers.VandeheyS7.eventually_le_blockCount_relSet_div
#print axioms NormalNumbers.VandeheyS7.relMass_le_sum_insideWords
#print axioms NormalNumbers.VandeheyS7.sum_relMass_meetWords_le
#print axioms NormalNumbers.VandeheyS7.abs_blockCount_preimage_sub_le
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_Ioo
end Audit2
