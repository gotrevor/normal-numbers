/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFPsiPin
import NormalNumbers.CFScheduleA
import NormalNumbers.VandeheyAutomaton

/-!
# The `z`-avoidance mass decays geometrically

An analytic input built for the (now retired) synchronizing-word transfer principle
`VandeheyAutomaton.exists_jointFreq_limit` -- see the retirement note in
`VandeheyAutomaton.lean`, and `hall_vandehey_synchronizing_transducer`.  The statement
itself is unconditional and stays: the
Gauss mass of the set of points whose CF expansion avoids a fixed genuine word `z` at the
aligned block positions `0, s, 2s, …` (`s = |z| + 1`) tends to `0`.

The argument is a two-line renewal, and needs **no countable cylinder decomposition** — the
usual sticking point — because the repo's ψ-mixing pin
`CFPsiPin.gaussMeasure_cylinder_psi_mixing` allows an *arbitrary measurable* future set `A`,
not just a cylinder:

* `γ(T^{-s} A) = γ(A)` — Gauss invariance, iterated (`gaussMeasure_preimage_iterate`).
* `(0,1) ∩ T^{-s} A` splits, disjointly, into `I_z ∩ T^{-s}A` and `zFreeSet`'s next stage.
* ψ-mixing with gap `1` gives `γ(I_z ∩ T^{-s}A) ≥ (1 − 79/100)·γ(I_z)·γ(A)`.

Hence `γ(A_{k+1}) ≤ (1 − (21/100)·γ(I_z))·γ(A_k)`, and `γ(I_z) > 0` for a genuine `z`
(`gaussMeasure_cfCylinder_toReal_pos`), so the mass decays geometrically.  No hot-spot
criterion, no ergodicity, no Ryll-Nardzewski.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- `γ` lives on `(0,1)`, so intersecting with `(0,1)` does not change the mass. -/
lemma gaussMeasure_Ioo_inter {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure (Set.Ioo (0 : ℝ) 1 ∩ S) = gaussMeasure S := by
  have hset : Set.Ioo (0 : ℝ) 1 ∩ S ∩ Set.Ioo (0 : ℝ) 1 = S ∩ Set.Ioo (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h2⟩
  rw [gaussMeasure_apply (measurableSet_Ioo.inter hS), gaussMeasure_apply hS, hset]

/-- **The `z`-avoidance sets.**  `zFreeSet z k` is the set of points of `(0,1)` whose CF
expansion does not spell `z` at any of the aligned block positions `0, s, …, (k−1)s`, where
`s = |z| + 1` (one spare digit between blocks, so the ψ-mixing gap is `1`). -/
noncomputable def zFreeSet (z : List ℕ) : ℕ → Set ℝ
  | 0 => Set.Ioo (0 : ℝ) 1
  | (k + 1) => (Set.Ioo (0 : ℝ) 1 \ cfCylinder z) ∩
      (gaussMap^[z.length + 1]) ⁻¹' zFreeSet z k

lemma measurableSet_zFreeSet (z : List ℕ) : ∀ k, MeasurableSet (zFreeSet z k)
  | 0 => measurableSet_Ioo
  | (k + 1) => by
    refine (measurableSet_Ioo.diff (measurableSet_cfCylinder z)).inter ?_
    exact measurable_gaussMap.iterate (z.length + 1) (measurableSet_zFreeSet z k)

lemma zFreeSet_subset_Ioo (z : List ℕ) : ∀ k, zFreeSet z k ⊆ Set.Ioo (0 : ℝ) 1
  | 0 => le_refl _
  | (k + 1) => fun _ hx => hx.1.1

lemma gaussMeasure_zFreeSet_zero (z : List ℕ) :
    gaussMeasure (zFreeSet z 0) = 1 := by
  rw [zFreeSet, gaussMeasure_Ioo (le_refl 0) (by norm_num) (le_refl 1)]
  norm_num

/-- **The renewal step.**  One block of `|z| + 1` digits kills at least the fraction
`(21/100)·γ(I_z)` of the remaining avoidance mass. -/
theorem gaussMeasure_zFreeSet_succ_le (z : List ℕ) (hzpos : ∀ a ∈ z, 1 ≤ a) (k : ℕ) :
    (gaussMeasure (zFreeSet z (k + 1))).toReal
      ≤ (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal)
          * (gaussMeasure (zFreeSet z k)).toReal := by
  set A : Set ℝ := zFreeSet z k with hA
  have hAmeas : MeasurableSet A := measurableSet_zFreeSet z k
  have hA1 : A ⊆ Set.Ioo (0 : ℝ) 1 := zFreeSet_subset_Ioo z k
  set s : ℕ := z.length + 1 with hs
  set P : Set ℝ := (gaussMap^[s]) ⁻¹' A with hP
  have hPmeas : MeasurableSet P := measurable_gaussMap.iterate s hAmeas
  have hZmeas : MeasurableSet (cfCylinder z) := measurableSet_cfCylinder z
  -- the disjoint split
  have hsplit : Set.Ioo (0 : ℝ) 1 ∩ P
      = (cfCylinder z ∩ P) ∪ ((Set.Ioo (0 : ℝ) 1 \ cfCylinder z) ∩ P) := by
    have hzsub := cfCylinder_subset_Ioo z
    ext y
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
    constructor
    · rintro ⟨hy, hyP⟩
      by_cases h : y ∈ cfCylinder z
      · exact Or.inl ⟨h, hyP⟩
      · exact Or.inr ⟨⟨hy, h⟩, hyP⟩
    · rintro (⟨h, hyP⟩ | ⟨⟨hy, -⟩, hyP⟩)
      · exact ⟨hzsub h, hyP⟩
      · exact ⟨hy, hyP⟩
  have hdisj : Disjoint (cfCylinder z ∩ P)
      ((Set.Ioo (0 : ℝ) 1 \ cfCylinder z) ∩ P) := by
    rw [Set.disjoint_left]
    rintro y ⟨hyz, -⟩ ⟨⟨-, hnz⟩, -⟩
    exact hnz hyz
  have hmass : gaussMeasure A
      = gaussMeasure (cfCylinder z ∩ P) + gaussMeasure (zFreeSet z (k + 1)) := by
    rw [show zFreeSet z (k + 1)
        = (Set.Ioo (0 : ℝ) 1 \ cfCylinder z) ∩ P from rfl,
      ← measure_union hdisj ((measurableSet_Ioo.diff hZmeas).inter hPmeas), ← hsplit,
      gaussMeasure_Ioo_inter hPmeas, hP, gaussMeasure_preimage_iterate hAmeas s]
  -- ψ-mixing lower bound on the killed part
  have hmix := gaussMeasure_cylinder_psi_mixing z hzpos 1 hAmeas hA1
  have hkill : (21 / 100) * (gaussMeasure (cfCylinder z)).toReal
        * (gaussMeasure A).toReal
      ≤ (gaussMeasure (cfCylinder z ∩ P)).toReal := by
    have habs := abs_le.mp hmix
    have hzr : 0 ≤ (gaussMeasure (cfCylinder z)).toReal := ENNReal.toReal_nonneg
    have har : 0 ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
    have hPeq : cfCylinder z ∩ (gaussMap^[z.length + 1]) ⁻¹' A = cfCylinder z ∩ P := rfl
    rw [hPeq] at habs
    nlinarith [habs.1]
  -- assemble in `toReal`
  have hfin1 : gaussMeasure (cfCylinder z ∩ P) ≠ ⊤ := measure_ne_top _ _
  have hfin2 : gaussMeasure (zFreeSet z (k + 1)) ≠ ⊤ := measure_ne_top _ _
  have htoReal : (gaussMeasure A).toReal
      = (gaussMeasure (cfCylinder z ∩ P)).toReal
        + (gaussMeasure (zFreeSet z (k + 1))).toReal := by
    rw [hmass, ENNReal.toReal_add hfin1 hfin2]
  nlinarith [hkill, htoReal]

/-- **Geometric decay** of the avoidance mass. -/
theorem gaussMeasure_zFreeSet_le_pow (z : List ℕ) (hzpos : ∀ a ∈ z, 1 ≤ a) :
    ∀ k, (gaussMeasure (zFreeSet z k)).toReal
      ≤ (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal) ^ k := by
  intro k
  induction k with
  | zero => simp [gaussMeasure_zFreeSet_zero]
  | succ k ih =>
    have hc0 : 0 ≤ 1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal := by
      have h1 : gaussMeasure (cfCylinder z) ≤ 1 := by
        rw [← gaussMeasure_univ]
        exact measure_mono (Set.subset_univ _)
      have h2 : (gaussMeasure (cfCylinder z)).toReal ≤ 1 := by
        have := ENNReal.toReal_mono (by norm_num) h1
        simpa using this
      linarith
    calc (gaussMeasure (zFreeSet z (k + 1))).toReal
        ≤ (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal)
            * (gaussMeasure (zFreeSet z k)).toReal :=
          gaussMeasure_zFreeSet_succ_le z hzpos k
      _ ≤ (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal)
            * (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal) ^ k := by
          exact mul_le_mul_of_nonneg_left ih hc0
      _ = (1 - (21 / 100) * (gaussMeasure (cfCylinder z)).toReal) ^ (k + 1) := by ring

/-- **The `z`-avoidance mass vanishes.**  For a genuine word `z`, the Gauss mass of the
points avoiding `z` at all of the first `k` aligned block positions tends to `0`. -/
theorem tendsto_gaussMeasure_zFreeSet (z : List ℕ) (hzne : z ≠ [])
    (hzpos : ∀ a ∈ z, 1 ≤ a) :
    Tendsto (fun k => (gaussMeasure (zFreeSet z k)).toReal) atTop (nhds 0) := by
  set γz : ℝ := (gaussMeasure (cfCylinder z)).toReal with hγz
  have hγpos : 0 < γz := gaussMeasure_cfCylinder_toReal_pos z hzne hzpos
  have hγle : γz ≤ 1 := by
    have h1 : gaussMeasure (cfCylinder z) ≤ 1 := by
      rw [← gaussMeasure_univ]
      exact measure_mono (Set.subset_univ _)
    have := ENNReal.toReal_mono (by norm_num) h1
    simpa [hγz] using this
  set c : ℝ := 1 - (21 / 100) * γz with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; nlinarith
  have hgeo : Tendsto (fun k : ℕ => c ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo
    (fun k => ENNReal.toReal_nonneg) (fun k => ?_)
  exact gaussMeasure_zFreeSet_le_pow z hzpos k

/-! ## From `z`-free cylinders to the avoidance sets -/

open VandeheyAut

lemma cfDigit_iterate (x : ℝ) (n i : ℕ) :
    cfDigit (gaussMap^[n] x) i = cfDigit x (n + i) := by
  simp only [cfDigit, ← Function.iterate_add_apply]
  rw [Nat.add_comm i n]

lemma getD_drop (q : List ℕ) (n i : ℕ) : (q.drop n).getD i 0 = q.getD (n + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **A `z`-free cylinder sits inside the `z`-avoidance set.**  If the word `q` does not
contain `z` as a factor and is long enough for `k` aligned blocks, then every irrational
point of `cfCylinder q` avoids `z` at all `k` aligned block positions. -/
lemma mem_zFreeSet_of_mem_cfCylinder : ∀ (k : ℕ) (z q : List ℕ), ¬ z <:+: q →
    k * (z.length + 1) ≤ q.length → ∀ x ∈ cfCylinder q, Irrational x →
    x ∈ zFreeSet z k := by
  intro k
  induction k with
  | zero => intro z q _ _ x hx _; exact hx.1
  | succ k ih =>
    intro z q hzq hk x hx hirr
    have hm : z.length + 1 ≤ q.length := le_trans (by nlinarith) hk
    refine ⟨⟨hx.1, ?_⟩, ?_⟩
    · -- `x ∉ cfCylinder z`: otherwise `z` is a prefix, hence a factor, of `q`
      intro hxz
      refine hzq (List.IsPrefix.isInfix ?_)
      rw [List.prefix_iff_eq_take]
      refine List.ext_getElem (by simp; omega) ?_
      intro i h1 h2
      have hi : i < z.length := h1
      have hzd := hxz.2 i hi
      have hqd := hx.2 i (by omega)
      have : z.getD i 0 = q.getD i 0 := by rw [← hzd, ← hqd]
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at this
      rw [this, List.getElem_take]
    · -- `T^{|z|+1} x` avoids `z` at the remaining `k` blocks
      set s : ℕ := z.length + 1 with hs
      have horb := irrational_orbit x hirr hx.1 s
      have hdrop : gaussMap^[s] x ∈ cfCylinder (q.drop s) := by
        refine ⟨horb.2, ?_⟩
        intro i hi
        rw [List.length_drop] at hi
        rw [cfDigit_iterate, hx.2 (s + i) (by omega), getD_drop]
      refine ih z (q.drop s) (fun h => hzq (h.trans (List.drop_suffix s q).isInfix)) ?_
        _ hdrop horb.1
      rw [List.length_drop, ← hs]
      refine Nat.le_sub_of_add_le ?_
      calc k * s + s = (k + 1) * s := by ring
        _ ≤ q.length := hk

/-- **The `z`-free window mass is small.**  For a finite family of `z`-free words of length
`L`, the total cylinder mass is at most the `k`-block avoidance mass, as soon as
`k·(|z|+1) ≤ L`. -/
theorem sum_gaussMeasure_zfree_le (z : List ℕ) (F : Finset (List ℕ)) (L k : ℕ)
    (hF : ∀ q ∈ F, q.length = L) (hFz : ∀ q ∈ F, ¬ z <:+: q)
    (hk : k * (z.length + 1) ≤ L) :
    ∑ q ∈ F, (gaussMeasure (cfCylinder q)).toReal
      ≤ (gaussMeasure (zFreeSet z k)).toReal := by
  classical
  have hdisj : (↑F : Set (List ℕ)).PairwiseDisjoint (fun q => cfCylinder q) :=
    fun q hq q' hq' hne => cfCylinder_disjoint (by rw [hF q hq, hF q' hq']) hne
  have hbi := MeasureTheory.measure_biUnion_finset hdisj
    (fun q (_ : q ∈ F) => measurableSet_cfCylinder q) (μ := gaussMeasure)
  have hsub : (⋃ q ∈ F, cfCylinder q) \ Set.range ((↑) : ℚ → ℝ) ⊆ zFreeSet z k := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx.1
    exact mem_zFreeSet_of_mem_cfCylinder k z q (hFz q hq)
      (by rw [hF q hq]; exact hk) x hxq hx.2
  have hnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    gaussMeasure_countable_null (Set.countable_range _)
  have hle : gaussMeasure (⋃ q ∈ F, cfCylinder q) ≤ gaussMeasure (zFreeSet z k) := by
    calc gaussMeasure (⋃ q ∈ F, cfCylinder q)
        = gaussMeasure ((⋃ q ∈ F, cfCylinder q) \ Set.range ((↑) : ℚ → ℝ)) :=
          (measure_sdiff_null hnull).symm
      _ ≤ gaussMeasure (zFreeSet z k) := measure_mono hsub
  rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top _ _), ← hbi]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

end NormalNumbers
