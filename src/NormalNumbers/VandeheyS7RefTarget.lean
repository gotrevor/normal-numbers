/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RT: the reference observable's target is order-connected

S7-RQ evaluates the orbit frequency of `I_v ∩ G^{-|v|} A` for an ORDER-CONNECTED `A ⊆ (0,1)`
(`tendsto_blockCount_relSet_of_ordConnected`).  The reference observable of route A tests exactly
one kind of target: `mapBlockSet s w 0 = s.mob ⁻¹' I_w ∩ (0,1)` — "after reading `v`, the state `s`
sends the current point into the cylinder of the word `w`".  This module shows that target IS
order-connected, so S7-RQ applies to it verbatim.

Two ingredients, both elementary and both new here:

* `cfCylinder_ordConnected` — a CF cylinder is order-connected.  Induction on the word: the
  first-digit condition is literally the interval `1/(a+1) < z ≤ 1/a`
  (`cfDigit_zero_eq_iff`), and on that interval `G z = 1/z − a` is monotone (decreasing), so the
  tail condition transfers by the inductive hypothesis.  The `Gz = 0` corner is excluded because a
  genuine word has a positive first digit while `cfDigit 0 0 = 0`.
* `MapState.mob_sub_mob` / `mob_mem_uIcc` — the Möbius map of a state is monotone on `[0,1]` in the
  sense that `mob z₂ − mob z₁ = det · (z₂ − z₁) / (den·den)`, so the image of a point between two
  points lies between their images, whichever way the determinant points.

## Guard rule

**Content locator.**  Order-connectedness is where the *interval* nature of the target is used, and
it is all that S7-RQ needs: no length estimate, no distortion bound.  The trivial instance is
`w = []`, where `mapBlockSet s [] 0 = (0,1)` (`mob` maps `(0,1)` into `[0,1]`) and the statement is
`ordConnected_Ioo`; the content is that a *longer* word still gives an interval.

**Degenerate cases.**  `w = []`: covered (the cylinder is `(0,1)`).  A word containing a `0` digit
is excluded by hypothesis and indeed breaks the statement's proof (not the statement: such a
cylinder is empty for irrational points but may contain junk rationals).  `mapBlockSet` of a state
whose image misses `I_w` entirely is empty, and the empty set is order-connected.
-/
import NormalNumbers.VandeheyS7RelFreq

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

/-! ## A CF cylinder is order-connected -/

lemma one_le_getD_zero {m : List ℕ} (hm : m ≠ []) (hpos : ∀ a ∈ m, 1 ≤ a) :
    1 ≤ m.getD 0 0 := by
  cases m with
  | nil => exact absurd rfl hm
  | cons b l => exact hpos b (by simp)

/-- **A CF cylinder is order-connected.** -/
theorem cfCylinder_ordConnected : ∀ (w : List ℕ), (∀ a ∈ w, 1 ≤ a) →
    (cfCylinder w).OrdConnected := by
  intro w
  induction w with
  | nil =>
      intro _
      rw [cfCylinder_nil]
      exact ordConnected_Ioo
  | cons a m ih =>
      intro hpos
      have ha : 1 ≤ a := hpos a (by simp)
      have hposm : ∀ b ∈ m, 1 ≤ b := fun b hb => hpos b (by simp [hb])
      have hIH := ih hposm
      refine ⟨fun x hx y hy t ht => ?_⟩
      obtain ⟨hx01, hxd, hxrest⟩ := mem_cfCylinder_cons.1 hx
      obtain ⟨hy01, hyd, hyrest⟩ := mem_cfCylinder_cons.1 hy
      have ht01 : t ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_lt_of_le hx01.1 ht.1, lt_of_le_of_lt ht.2 hy01.2⟩
      -- the first digit
      obtain ⟨hxlo, hxhi⟩ := (cfDigit_zero_eq_iff hx01 ha).1 hxd
      obtain ⟨hylo, hyhi⟩ := (cfDigit_zero_eq_iff hy01 ha).1 hyd
      have htd : cfDigit t 0 = a :=
        (cfDigit_zero_eq_iff ht01 ha).2 ⟨lt_of_lt_of_le hxlo ht.1, le_trans ht.2 hyhi⟩
      refine mem_cfCylinder_cons.2 ⟨ht01, htd, fun i hi => ?_⟩
      by_cases hm : m = []
      · subst hm; simp at hi
      -- the Gauss images are ordered the other way
      have hgx : gaussMap x = x⁻¹ - (a:ℝ) := by
        rw [gaussMap_eq_inv_sub hx01, hxd]
      have hgy : gaussMap y = y⁻¹ - (a:ℝ) := by
        rw [gaussMap_eq_inv_sub hy01, hyd]
      have hgt : gaussMap t = t⁻¹ - (a:ℝ) := by
        rw [gaussMap_eq_inv_sub ht01, htd]
      have hle1 : gaussMap y ≤ gaussMap t := by
        rw [hgy, hgt]
        have hyy : 1 / y ≤ 1 / t := one_div_le_one_div_of_le ht01.1 ht.2
        rw [one_div, one_div] at hyy
        linarith
      have hle2 : gaussMap t ≤ gaussMap x := by
        rw [hgt, hgx]
        have hxx : 1 / t ≤ 1 / x := one_div_le_one_div_of_le hx01.1 ht.1
        rw [one_div, one_div] at hxx
        linarith
      -- the Gauss images of the endpoints lie in the tail cylinder
      have hmemG : ∀ {z : ℝ}, z ∈ Set.Ioo (0:ℝ) 1 →
          (∀ i < m.length, cfDigit (gaussMap z) i = m.getD i 0) → gaussMap z ∈ cfCylinder m := by
        intro z hz hzd
        have hIco := gaussMap_mem_Ico01 z
        have hpos0 : 0 < gaussMap z := by
          rcases lt_or_eq_of_le hIco.1 with h | h
          · exact h
          · exfalso
            have hlen : 0 < m.length := List.length_pos_of_ne_nil hm
            have h0 := hzd 0 hlen
            rw [← h] at h0
            have hz0 : cfDigit (0:ℝ) 0 = 0 := by
              simp [cfDigit, gaussMap]
            rw [hz0] at h0
            have := one_le_getD_zero hm hposm
            omega
        exact ⟨⟨hpos0, hIco.2⟩, fun i hi => hzd i hi⟩
      have hGx := hmemG hx01 hxrest
      have hGy := hmemG hy01 hyrest
      have hGt : gaussMap t ∈ cfCylinder m := hIH.out hGy hGx ⟨hle1, hle2⟩
      exact hGt.2 i hi

/-! ## The Möbius map is monotone on `[0,1]` -/

namespace MapState

lemma mob_sub_mob (s : MapState) {z₁ z₂ : ℝ} (h₁ : z₁ ∈ Set.Icc (0:ℝ) 1)
    (h₂ : z₂ ∈ Set.Icc (0:ℝ) 1) :
    s.mob z₂ - s.mob z₁
      = (s.a * s.d - s.b * s.c) * (z₂ - z₁) / ((s.c * z₂ + s.d) * (s.c * z₁ + s.d)) := by
  have hd₁ := s.den_pos h₁
  have hd₂ := s.den_pos h₂
  rw [mob, mob, div_sub_div _ _ hd₂.ne' hd₁.ne']
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The image of a point between two points lies between their images. -/
lemma mob_mem_uIcc_of_between (s : MapState) {z₁ z₂ t : ℝ} (h₁ : z₁ ∈ Set.Icc (0:ℝ) 1)
    (h₂ : z₂ ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc z₁ z₂) :
    s.mob t ∈ Set.uIcc (s.mob z₁) (s.mob z₂) := by
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans h₁.1 ht.1, le_trans ht.2 h₂.2⟩
  have hdt := s.den_pos ht01
  have hd₁ := s.den_pos h₁
  have hd₂ := s.den_pos h₂
  have e₁ : s.mob t - s.mob z₁
      = (s.a * s.d - s.b * s.c) * (t - z₁) / ((s.c * t + s.d) * (s.c * z₁ + s.d)) :=
    s.mob_sub_mob h₁ ht01
  have e₂ : s.mob z₂ - s.mob t
      = (s.a * s.d - s.b * s.c) * (z₂ - t) / ((s.c * z₂ + s.d) * (s.c * t + s.d)) :=
    s.mob_sub_mob ht01 h₂
  rcases lt_trichotomy (s.a * s.d - s.b * s.c) 0 with hdet | hdet | hdet
  · refine Set.mem_uIcc.2 (Or.inr ⟨?_, ?_⟩)
    · have : s.mob z₂ - s.mob t ≤ 0 := by
        rw [e₂]
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg hdet.le (by linarith [ht.2])
        · positivity
      linarith
    · have : s.mob t - s.mob z₁ ≤ 0 := by
        rw [e₁]
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg hdet.le (by linarith [ht.1])
        · positivity
      linarith
  · exact absurd (by linarith : s.a * s.d - s.b * s.c = 0) s.hdet
  · refine Set.mem_uIcc.2 (Or.inl ⟨?_, ?_⟩)
    · have : 0 ≤ s.mob t - s.mob z₁ := by
        rw [e₁]
        apply div_nonneg
        · exact mul_nonneg hdet.le (by linarith [ht.1])
        · positivity
      linarith
    · have : 0 ≤ s.mob z₂ - s.mob t := by
        rw [e₂]
        apply div_nonneg
        · exact mul_nonneg hdet.le (by linarith [ht.2])
        · positivity
      linarith

lemma measurable_mob (s : MapState) : Measurable s.mob := by
  unfold mob
  exact (measurable_const.mul measurable_id).add measurable_const |>.div
    ((measurable_const.mul measurable_id).add measurable_const)

/-! ## The reference target -/

lemma mapBlockSet_subset_Ioo (s : MapState) (w : List ℕ) :
    mapBlockSet s w 0 ⊆ Set.Ioo (0:ℝ) 1 := fun _ hz => hz.2

lemma measurableSet_mapBlockSet (s : MapState) (w : List ℕ) :
    MeasurableSet (mapBlockSet s w 0) := by
  rw [mapBlockSet]
  refine MeasurableSet.inter ?_ measurableSet_Ioo
  refine s.measurable_mob ?_
  exact ((measurable_gaussMap.iterate 0) (measurableSet_cfCylinder w)).inter measurableSet_Ioo

/-- **S7-RT.**  The reference observable's target is order-connected. -/
theorem mapBlockSet_ordConnected (s : MapState) {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    (mapBlockSet s w 0).OrdConnected := by
  have hcyl := cfCylinder_ordConnected w hpos
  refine ⟨fun x hx y hy t ht => ?_⟩
  have hx01 : x ∈ Set.Ioo (0:ℝ) 1 := hx.2
  have hy01 : y ∈ Set.Ioo (0:ℝ) 1 := hy.2
  have ht01 : t ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_lt_of_le hx01.1 ht.1, lt_of_le_of_lt ht.2 hy01.2⟩
  have hxc : s.mob x ∈ cfCylinder w := by
    have := hx.1
    simpa [mapBlockSet, Set.mem_preimage] using this.1
  have hyc : s.mob y ∈ cfCylinder w := by
    have := hy.1
    simpa [mapBlockSet, Set.mem_preimage] using this.1
  have hbetween := s.mob_mem_uIcc_of_between ⟨hx01.1.le, hx01.2.le⟩ ⟨hy01.1.le, hy01.2.le⟩ ht
  have hmem : s.mob t ∈ cfCylinder w := by
    rcases Set.mem_uIcc.1 hbetween with h | h
    · exact hcyl.out hxc hyc h
    · exact hcyl.out hyc hxc h
  refine ⟨?_, ht01⟩
  refine Set.mem_preimage.2 ⟨?_, ?_⟩
  · simpa using hmem
  · exact cfCylinder_subset_Ioo w hmem

/-- **The payoff.**  The orbit frequency of the reference observable's joint test event is its
relative mass — for every CF-normal input, with no cited input. -/
theorem tendsto_blockCount_relSet_mapBlockSet {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {v : List ℕ} (hpv : ∀ a ∈ v, 1 ≤ a)
    (s : MapState) {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    Tendsto (fun p => blockCount (relSet v (mapBlockSet s w 0)) p x / (p : ℝ)) atTop
      (nhds (relMass v (mapBlockSet s w 0))) :=
  tendsto_blockCount_relSet_of_ordConnected hx horb hpv (s.measurableSet_mapBlockSet w)
    (s.mapBlockSet_subset_Ioo w) (s.mapBlockSet_ordConnected hpos)

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.cfCylinder_ordConnected
#print axioms NormalNumbers.VandeheyS7.MapState.mob_mem_uIcc_of_between
#print axioms NormalNumbers.VandeheyS7.MapState.mapBlockSet_ordConnected
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_blockCount_relSet_mapBlockSet

end Audit
