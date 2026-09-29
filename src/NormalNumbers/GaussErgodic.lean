/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFGammaMixing
import NormalNumbers.CFPsiPin
import NormalNumbers.DaryCorrect

/-!
# Ergodicity of the Gauss map for the Gauss measure

The first half of the discharge plan for `VandeheyS7.GaussACRigidity`: the Gauss map `T` is
**ergodic** for `γ`.  The repo already owns correlation decay against an *arbitrary* measurable
set (`gaussMeasure_cylinder_mixing`), so the classical proof runs:

1. If `A` is invariant along irrational orbits then `T^{-(|v|+g)}A` agrees with `A` on the
   irrationals, so `γ(I_v ∩ A) = γ(I_v ∩ T^{-(|v|+g)}A)`, and the mixing bound (geometric in
   `g`) forces `γ(I_v ∩ A) = γ(I_v)·γ(A)` **exactly**, for every cylinder `I_v`.
2. Cylinders of a fixed depth are pairwise disjoint and, on the irrationals, refine to depth
   `n+1`; their diameters tend to `0`.  So every open `U` is, up to a countable set, the
   increasing union of the depth-`n` cylinders it contains, and step 1 upgrades to
   `γ(U ∩ A) = γ(U)·γ(A)`.
3. Open sets are a π-system generating the Borel σ-algebra, so `B ↦ γ(B ∩ A)` and
   `B ↦ γ(A)·γ(B)` agree everywhere; at `B = A` this is `γ(A) = γ(A)²`.
-/

namespace NormalNumbers

open MeasureTheory Set

/-- Invariance along irrational orbits: the honest pointwise form of `T^{-1}A = A`, stated only
where the Gauss map is the genuine CF shift (rationals are `γ`-null and their orbits fall out of
`(0,1)`). -/
def GaussInvariant (A : Set ℝ) : Prop :=
  ∀ x : ℝ, Irrational x → x ∈ Ioo (0 : ℝ) 1 → (x ∈ A ↔ gaussMap x ∈ A)

/-! ## Cylinder combinatorics -/

/-- The word of the first `n` CF digits of `x`. -/
noncomputable def digitWord (x : ℝ) (n : ℕ) : List ℕ := (List.range n).map (cfDigit x)

@[simp] lemma digitWord_length (x : ℝ) (n : ℕ) : (digitWord x n).length = n := by
  simp [digitWord]

lemma digitWord_getD {x : ℝ} {n i : ℕ} (hi : i < n) : (digitWord x n).getD i 0 = cfDigit x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [digitWord]

lemma digitWord_pos {x : ℝ} (hirr : Irrational x) (hx : x ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    ∀ a ∈ digitWord x n, 1 ≤ a := by
  intro a ha
  simp only [digitWord, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact one_le_cfDigit x hirr hx i

lemma digitWord_ne_nil {x : ℝ} {n : ℕ} (hn : 0 < n) : digitWord x n ≠ [] := by
  intro h
  have := digitWord_length x n
  rw [h] at this
  simp at this
  omega

lemma mem_cfCylinder_digitWord {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    x ∈ cfCylinder (digitWord x n) := by
  refine ⟨hx, ?_⟩
  intro i hi
  rw [digitWord_length] at hi
  rw [digitWord_getD hi]

/-- Distinct words of the same length have disjoint cylinders. -/
lemma cfCylinder_disjoint_of_ne {v w : List ℕ} (hlen : v.length = w.length) (hne : v ≠ w) :
    Disjoint (cfCylinder v) (cfCylinder w) := by
  rw [Set.disjoint_left]
  intro x hv hw
  apply hne
  apply List.ext_getElem hlen
  intro i h1 h2
  have h3 := hv.2 i h1
  have h4 := hw.2 i h2
  rw [List.getD_eq_getElem _ _ h1] at h3
  rw [List.getD_eq_getElem _ _ h2] at h4
  rw [← h3, ← h4]

/-! ## Step 1: exact factorization against every cylinder -/

/-- Invariance propagates along the whole orbit, at every irrational point of `(0,1)`. -/
lemma mem_iterate_preimage_iff {A : Set ℝ} (hinv : GaussInvariant A) (m : ℕ) {x : ℝ}
    (hirr : Irrational x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (gaussMap^[m] x ∈ A ↔ x ∈ A) := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      obtain ⟨hirr', hx'⟩ := irrational_gaussMap hirr hx
      rw [ih hirr' hx']
      exact (hinv x hirr hx).symm

/-- On the irrationals, `T^{-m}A` and `A` agree, so they agree `γ`-a.e. -/
lemma gaussMeasure_inter_iterate_preimage {A : Set ℝ} (hA : MeasurableSet A)
    (hinv : GaussInvariant A) (m : ℕ) {S : Set ℝ} (hS : MeasurableSet S) (hS1 : S ⊆ Ioo (0:ℝ) 1) :
    gaussMeasure (S ∩ (gaussMap^[m]) ⁻¹' A) = gaussMeasure (S ∩ A) := by
  have hsub : ∀ y : ℝ, y ∈ (S ∩ (gaussMap^[m]) ⁻¹' A) \ (S ∩ A) ∪
      (S ∩ A) \ (S ∩ (gaussMap^[m]) ⁻¹' A) → y ∈ Set.range ((↑) : ℚ → ℝ) := by
    intro y hy
    by_contra hcon
    have hirr : Irrational y := hcon
    rcases hy with ⟨⟨hyS, hyP⟩, hno⟩ | ⟨⟨hyS, hyA⟩, hno⟩
    · exact hno ⟨hyS, (mem_iterate_preimage_iff hinv m hirr (hS1 hyS)).1 hyP⟩
    · exact hno ⟨hyS, (mem_iterate_preimage_iff hinv m hirr (hS1 hyS)).2 hyA⟩
  have hnull : gaussMeasure ((S ∩ (gaussMap^[m]) ⁻¹' A) \ (S ∩ A) ∪
      (S ∩ A) \ (S ∩ (gaussMap^[m]) ⁻¹' A)) = 0 :=
    measure_mono_null hsub (gaussMeasure_countable_null (Set.countable_range _))
  refine measure_congr (MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩)
  · exact measure_mono_null (fun z hz => Set.mem_union_left _ hz) hnull
  · exact measure_mono_null (fun z hz => Set.mem_union_right _ hz) hnull

/-- **Step 1.**  An invariant set factorizes exactly against every cylinder: the mixing bound is
geometric in the gap `g`, while the left-hand side does not depend on `g` at all. -/
theorem gaussMeasure_cfCylinder_inter_invariant {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Ioo (0:ℝ) 1) (hinv : GaussInvariant A) (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) :
    (gaussMeasure (cfCylinder v ∩ A)).toReal
      = (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure A).toReal := by
  set c : ℝ := |(gaussMeasure (cfCylinder v ∩ A)).toReal -
    (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure A).toReal| with hc
  set K : ℝ := 4 * (volume A).toReal * (gaussMeasure (cfCylinder v)).toReal with hK
  have hbound : ∀ g : ℕ, c ≤ (9/10 : ℝ) ^ g * K := by
    intro g
    have h := gaussMeasure_cylinder_mixing v hpos g hA hA1
    rw [gaussMeasure_inter_iterate_preimage hA hinv (v.length + g)
      (measurableSet_cfCylinder v) (cfCylinder_subset_Ioo v)] at h
    calc c ≤ (9 / 10) ^ g * (4 * (volume A).toReal) *
        (gaussMeasure (cfCylinder v)).toReal := h
      _ = (9/10 : ℝ) ^ g * K := by rw [hK]; ring
  have hlim : Filter.Tendsto (fun g : ℕ => (9/10 : ℝ) ^ g * K) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun g : ℕ => (9/10 : ℝ) ^ g) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using this.mul_const K
  have hle : c ≤ 0 := ge_of_tendsto' hlim hbound
  have : c = 0 := le_antisymm hle (abs_nonneg _)
  have := abs_eq_zero.1 this
  linarith

/-! ## Step 2: from cylinders to open sets -/

/-- Deterministic cylinder-diameter decay: a genuine word of length `n` has
`|I_w| ≤ 2 / 2^n`. -/
lemma volume_cfCylinder_le_two_div (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    (volume (cfCylinder w)).toReal ≤ 2 / 2 ^ w.length := by
  have hK1 : 1 ≤ cfK w := one_le_cfK w hpos
  have hKR : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast hK1
  have hK'R : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  have hpow : (2 : ℝ) ^ (w.length / 2) ≤ (cfK w : ℝ) := by
    have := two_pow_le_cfK w hpos
    exact_mod_cast this
  have hpow0 : (0:ℝ) < 2 ^ (w.length / 2) := by positivity
  rw [volume_cfCylinder w hw hpos, ENNReal.toReal_ofReal (by positivity)]
  have hsq : (2:ℝ) ^ (w.length / 2) * 2 ^ (w.length / 2) ≤ (cfK w : ℝ) * (cfK w : ℝ) :=
    mul_le_mul hpow hpow hpow0.le (by linarith)
  have hexp : (2:ℝ) ^ w.length ≤ 2 * (2 ^ (w.length / 2) * 2 ^ (w.length / 2)) := by
    have h1 : (2:ℝ) ^ w.length ≤ 2 ^ (w.length / 2 + w.length / 2 + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2:ℝ) ^ w.length ≤ 2 ^ (w.length / 2 + w.length / 2 + 1) := h1
      _ = 2 * (2 ^ (w.length / 2) * 2 ^ (w.length / 2)) := by rw [pow_succ, pow_add]; ring
  have hX : (0:ℝ) < (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by nlinarith
  rw [div_le_div_iff₀ hX (by positivity)]
  nlinarith

/-- Every irrational point of an open set lies in one of its own CF cylinders. -/
lemma exists_digitWord_cfCylinder_subset {U : Set ℝ} (hU : IsOpen U) {x : ℝ}
    (hirr : Irrational x) (hx01 : x ∈ Ioo (0:ℝ) 1) (hxU : x ∈ U) :
    ∃ n : ℕ, 0 < n ∧ cfCylinder (digitWord x n) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  have hlim : Filter.Tendsto (fun n : ℕ => 2 / (2:ℝ) ^ n) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 := this.const_mul (2:ℝ)
    simp only [mul_zero] at h2
    convert h2 using 2 with n
    rw [div_pow, one_pow]
    ring
  obtain ⟨n, hn, hnpos⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    (Filter.eventually_gt_atTop 0)).exists
  refine ⟨n, hnpos, ?_⟩
  have hne : digitWord x n ≠ [] := digitWord_ne_nil hnpos
  have hp := digitWord_pos hirr hx01 n
  obtain ⟨a, c, hsub, hlen⟩ := cfCylinder_subset_Icc_length _ hne hp
  have hxmem : x ∈ Icc a c := hsub (mem_cfCylinder_digitWord hx01 n)
  have hlt : c - a < ε := by
    rw [hlen]
    calc (volume (cfCylinder (digitWord x n))).toReal ≤ 2 / 2 ^ (digitWord x n).length :=
          volume_cfCylinder_le_two_div _ hne hp
      _ = 2 / 2 ^ n := by rw [digitWord_length]
      _ < ε := hn
  intro y hy
  have hymem : y ∈ Icc a c := hsub hy
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor
  · have := hymem.1; have := hxmem.2; linarith
  · have := hymem.2; have := hxmem.1; linarith

/-- The genuine words of length `n` whose cylinder is contained in `U`. -/
def cylWords (U : Set ℝ) (n : ℕ) : Set (List ℕ) :=
  {v | v.length = n ∧ (∀ a ∈ v, 1 ≤ a) ∧ cfCylinder v ⊆ U}

/-- The union of those cylinders, restricted to the irrationals (where the CF dynamics is
genuine; the rationals are `γ`-null).  Restricting makes the family exactly monotone in `n`. -/
def cylBody (U : Set ℝ) (n : ℕ) : Set ℝ :=
  (⋃ v ∈ cylWords U n, cfCylinder v) ∩ {x | Irrational x}

lemma measurableSet_irrational : MeasurableSet {x : ℝ | Irrational x} := by
  have : {x : ℝ | Irrational x} = (Set.range ((↑) : ℚ → ℝ))ᶜ := rfl
  rw [this]
  exact ((Set.countable_range _).measurableSet).compl

lemma measurableSet_cylWordsUnion (U : Set ℝ) (n : ℕ) :
    MeasurableSet (⋃ v ∈ cylWords U n, cfCylinder v) := by
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro v _
  exact measurableSet_cfCylinder v

lemma measurableSet_cylBody (U : Set ℝ) (n : ℕ) : MeasurableSet (cylBody U n) :=
  (measurableSet_cylWordsUnion U n).inter measurableSet_irrational

/-- Dropping the rationals does not change a Gauss measure. -/
lemma gaussMeasure_inter_irrational {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure (S ∩ {x : ℝ | Irrational x}) = gaussMeasure S := by
  refine measure_congr (MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩)
  · simp only [Set.diff_eq_empty.2 Set.inter_subset_left, measure_empty]
  · refine measure_mono_null (fun y hy => ?_)
      (gaussMeasure_countable_null (S := Set.range ((↑) : ℚ → ℝ)) (Set.countable_range _))
    by_contra hcon
    exact hy.2 ⟨hy.1, hcon⟩

/-- Countable additivity over the depth-`n` cylinders inside `U`. -/
lemma gaussMeasure_cylWordsUnion_inter (U : Set ℝ) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    gaussMeasure ((⋃ v ∈ cylWords U n, cfCylinder v) ∩ B)
      = ∑' v : cylWords U n, gaussMeasure (cfCylinder (v : List ℕ) ∩ B) := by
  have hrw : (⋃ v ∈ cylWords U n, cfCylinder v) ∩ B
      = ⋃ v : cylWords U n, (cfCylinder (v : List ℕ) ∩ B) := by
    rw [Set.biUnion_eq_iUnion, Set.iUnion_inter]
  rw [hrw]
  refine measure_iUnion ?_ (fun v => (measurableSet_cfCylinder _).inter hB)
  intro v w hvw
  have hne : (v : List ℕ) ≠ (w : List ℕ) := fun h => hvw (Subtype.ext h)
  have hlen : (v : List ℕ).length = (w : List ℕ).length := by
    rw [v.2.1, w.2.1]
  exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left
    (cfCylinder_disjoint_of_ne hlen hne)

/-- **Step 2, one depth.**  An invariant set factorizes against the whole depth-`n` body. -/
lemma gaussMeasure_cylBody_inter_invariant {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Ioo (0:ℝ) 1) (hinv : GaussInvariant A) (U : Set ℝ) (n : ℕ) :
    gaussMeasure (cylBody U n ∩ A) = gaussMeasure (cylBody U n) * gaussMeasure A := by
  have hne : ∀ S : Set ℝ, gaussMeasure S ≠ ⊤ := by
    intro S
    exact ne_top_of_le_ne_top (by rw [gaussMeasure_univ]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ S))
  have hstep : ∀ v : cylWords U n,
      gaussMeasure (cfCylinder (v : List ℕ) ∩ A)
        = gaussMeasure (cfCylinder (v : List ℕ)) * gaussMeasure A := by
    intro v
    have h := gaussMeasure_cfCylinder_inter_invariant hA hA1 hinv (v : List ℕ) v.2.2.1
    rw [← ENNReal.toReal_mul] at h
    exact (ENNReal.toReal_eq_toReal_iff' (hne _) (ENNReal.mul_ne_top (hne _) (hne _))).1 h
  have hset : cylBody U n ∩ A
      = (⋃ v ∈ cylWords U n, cfCylinder v) ∩ (A ∩ {x : ℝ | Irrational x}) := by
    ext y; simp only [cylBody, Set.mem_inter_iff]; tauto
  rw [hset, gaussMeasure_cylWordsUnion_inter U n (hA.inter measurableSet_irrational)]
  have hdrop : ∀ v : cylWords U n,
      gaussMeasure (cfCylinder (v : List ℕ) ∩ (A ∩ {x : ℝ | Irrational x}))
        = gaussMeasure (cfCylinder (v : List ℕ)) * gaussMeasure A := by
    intro v
    rw [← Set.inter_assoc, gaussMeasure_inter_irrational
      ((measurableSet_cfCylinder _).inter hA), hstep v]
  have huniv : gaussMeasure (⋃ v ∈ cylWords U n, cfCylinder v)
      = ∑' v : cylWords U n, gaussMeasure (cfCylinder (v : List ℕ)) := by
    have h := gaussMeasure_cylWordsUnion_inter U n (B := Set.univ) MeasurableSet.univ
    simpa using h
  rw [tsum_congr hdrop, ENNReal.tsum_mul_right, cylBody,
    gaussMeasure_inter_irrational (measurableSet_cylWordsUnion U n), huniv]

/-- A point of a cylinder lies in the one-digit-longer cylinder cut out by its own next digit. -/
lemma mem_cfCylinder_snoc {v : List ℕ} {x : ℝ} (hx : x ∈ cfCylinder v) :
    x ∈ cfCylinder (v ++ [cfDigit x v.length]) := by
  refine ⟨hx.1, fun i hi => ?_⟩
  rw [List.length_append, List.length_cons, List.length_nil] at hi
  rcases lt_or_ge i v.length with h | h
  · rw [List.getD_append _ _ _ _ h]
    exact hx.2 i h
  · have hiv : i = v.length := by omega
    subst hiv
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp

lemma cylBody_mono (U : Set ℝ) : Monotone (cylBody U) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨hxU, hxirr⟩ := hx
  simp only [Set.mem_iUnion] at hxU
  obtain ⟨v, hv, hxv⟩ := hxU
  have hlen := hv.1
  have hx01 : x ∈ Ioo (0:ℝ) 1 := hxv.1
  refine ⟨?_, hxirr⟩
  simp only [Set.mem_iUnion]
  refine ⟨v ++ [cfDigit x v.length], ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.length_append]; simp [hlen]
  · intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hv.2.1 a h
    · simp only [List.mem_singleton] at h
      subst h
      exact one_le_cfDigit x hxirr hx01 v.length
  · exact (cfCylinder_append_subset v _).trans hv.2.2
  · exact mem_cfCylinder_snoc hxv

lemma iUnion_cylBody {U : Set ℝ} (hU : IsOpen U) :
    (⋃ n, cylBody U n) = U ∩ Ioo (0:ℝ) 1 ∩ {x : ℝ | Irrational x} := by
  ext x
  constructor
  · rintro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hxU, hxirr⟩ := hx
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨v, hv, hxv⟩ := hxU
    exact ⟨⟨hv.2.2 hxv, hxv.1⟩, hxirr⟩
  · rintro ⟨⟨hxU, hx01⟩, hxirr⟩
    obtain ⟨n, hn, hsub⟩ := exists_digitWord_cfCylinder_subset hU hxirr hx01 hxU
    simp only [Set.mem_iUnion]
    refine ⟨n, ?_, hxirr⟩
    simp only [Set.mem_iUnion]
    exact ⟨digitWord x n, ⟨digitWord_length x n, digitWord_pos hxirr hx01 n, hsub⟩,
      mem_cfCylinder_digitWord hx01 n⟩

/-- **Step 2.**  An invariant set factorizes against every open set. -/
theorem gaussMeasure_isOpen_inter_invariant {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Ioo (0:ℝ) 1) (hinv : GaussInvariant A) {U : Set ℝ} (hU : IsOpen U) :
    gaussMeasure (U ∩ A) = gaussMeasure U * gaussMeasure A := by
  have hne : ∀ S : Set ℝ, gaussMeasure S ≠ ⊤ := by
    intro S
    exact ne_top_of_le_ne_top (by rw [gaussMeasure_univ]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ S))
  -- the two limits
  have hmonoA : Monotone (fun n => cylBody U n ∩ A) := fun m n h =>
    Set.inter_subset_inter_left _ (cylBody_mono U h)
  have h1 := tendsto_measure_iUnion_atTop (μ := gaussMeasure) hmonoA
  have h2 := tendsto_measure_iUnion_atTop (μ := gaussMeasure) (cylBody_mono U)
  rw [← Set.iUnion_inter, iUnion_cylBody hU] at h1
  rw [iUnion_cylBody hU] at h2
  -- identify the two limits
  have hUA : gaussMeasure (U ∩ Ioo (0:ℝ) 1 ∩ {x : ℝ | Irrational x} ∩ A)
      = gaussMeasure (U ∩ A) := by
    have hset : U ∩ Ioo (0:ℝ) 1 ∩ {x : ℝ | Irrational x} ∩ A
        = (U ∩ Ioo (0:ℝ) 1 ∩ A) ∩ {x : ℝ | Irrational x} := by
      ext y; simp only [Set.mem_inter_iff]; tauto
    rw [hset, gaussMeasure_inter_irrational
      (((hU.measurableSet.inter measurableSet_Ioo)).inter hA)]
    · congr 1
      ext y
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hy, _⟩, hyA⟩; exact ⟨hy, hyA⟩
      · rintro ⟨hy, hyA⟩; exact ⟨⟨hy, hA1 hyA⟩, hyA⟩
  have hUU : gaussMeasure (U ∩ Ioo (0:ℝ) 1 ∩ {x : ℝ | Irrational x}) = gaussMeasure U := by
    rw [gaussMeasure_inter_irrational (hU.measurableSet.inter measurableSet_Ioo),
      Set.inter_comm U (Ioo (0:ℝ) 1), gaussMeasure_inter_Ioo hU.measurableSet]
  rw [hUA] at h1
  rw [hUU] at h2
  -- pass the factorization to the limit
  have h3 : Filter.Tendsto (fun n => gaussMeasure (cylBody U n) * gaussMeasure A)
      Filter.atTop (nhds (gaussMeasure U * gaussMeasure A)) :=
    ENNReal.Tendsto.mul_const h2 (Or.inr (hne A))
  have h4 : (fun n => gaussMeasure (cylBody U n ∩ A))
      = fun n => gaussMeasure (cylBody U n) * gaussMeasure A := by
    funext n
    exact gaussMeasure_cylBody_inter_invariant hA hA1 hinv U n
  rw [Function.comp_def, h4] at h1
  exact tendsto_nhds_unique h1 h3

/-! ## Step 3: ergodicity -/

instance : IsFiniteMeasure gaussMeasure :=
  ⟨by rw [gaussMeasure_univ]; exact ENNReal.one_lt_top⟩

/-- **Step 3.**  Opens are a π-system generating the Borel σ-algebra, so the factorization holds
against every measurable set. -/
theorem gaussMeasure_inter_invariant {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Ioo (0:ℝ) 1) (hinv : GaussInvariant A) {B : Set ℝ} (hB : MeasurableSet B) :
    gaussMeasure (B ∩ A) = gaussMeasure B * gaussMeasure A := by
  have key : gaussMeasure.restrict A = (gaussMeasure A) • gaussMeasure := by
    refine MeasureTheory.ext_of_generate_finite {s : Set ℝ | IsOpen s}
      (BorelSpace.measurable_eq (α := ℝ)) isPiSystem_isOpen ?_ ?_
    · intro U hU
      have hUo : IsOpen U := hU
      rw [Measure.restrict_apply hUo.measurableSet, Measure.smul_apply, smul_eq_mul,
        mul_comm]
      exact gaussMeasure_isOpen_inter_invariant hA hA1 hinv hUo
    · rw [Measure.restrict_apply MeasurableSet.univ, Measure.smul_apply, smul_eq_mul,
        gaussMeasure_univ, mul_one, Set.univ_inter]
  have := congrArg (fun μ => μ B) key
  simpa [Measure.restrict_apply hB, mul_comm] using this

/-- **Ergodicity of the Gauss map for the Gauss measure.**  Every invariant set is `γ`-trivial. -/
theorem gaussMeasure_eq_zero_or_one_of_invariant {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Ioo (0:ℝ) 1) (hinv : GaussInvariant A) :
    gaussMeasure A = 0 ∨ gaussMeasure A = 1 := by
  have hsq : gaussMeasure A = gaussMeasure A * gaussMeasure A := by
    have h := gaussMeasure_inter_invariant hA hA1 hinv hA
    rwa [Set.inter_self] at h
  by_cases h0 : gaussMeasure A = 0
  · exact Or.inl h0
  right
  have hne : gaussMeasure A ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [gaussMeasure_univ]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ A))
  have : gaussMeasure A * 1 = gaussMeasure A * gaussMeasure A := by rw [mul_one]; exact hsq
  exact ((ENNReal.mul_right_inj h0 hne).1 this).symm

/-! ## mathlib packaging: `Ergodic gaussMap gaussMeasure` -/

/-- **The Gauss map is ergodic for the Gauss measure** (mathlib's `Ergodic`).  A strictly
invariant measurable set is invariant along irrational orbits, so the dichotomy applies to its
trace on `(0,1)`, which carries all of `γ`. -/
theorem ergodic_gaussMap : Ergodic gaussMap gaussMeasure where
  toMeasurePreserving := measurePreserving_gaussMap
  toPreErgodic := by
    constructor
    intro s hs hinv
    have hA : MeasurableSet (s ∩ Ioo (0:ℝ) 1) := hs.inter measurableSet_Ioo
    have hAinv : GaussInvariant (s ∩ Ioo (0:ℝ) 1) := by
      intro x hirr hx
      have hT : gaussMap x ∈ Ioo (0:ℝ) 1 := (irrational_gaussMap hirr hx).2
      have hpre : x ∈ gaussMap ⁻¹' s ↔ x ∈ s := by rw [hinv]
      constructor
      · rintro ⟨hxs, _⟩; exact ⟨hpre.2 hxs, hT⟩
      · rintro ⟨hxs, _⟩; exact ⟨hpre.1 hxs, hx⟩
    have hval : gaussMeasure (s ∩ Ioo (0:ℝ) 1) = gaussMeasure s := by
      rw [Set.inter_comm, gaussMeasure_inter_Ioo hs]
    rw [Filter.eventuallyConst_set']
    rcases gaussMeasure_eq_zero_or_one_of_invariant hA Set.inter_subset_right hAinv with h | h
    · exact Or.inl (MeasureTheory.ae_eq_empty.2 (hval ▸ h))
    · refine Or.inr (MeasureTheory.ae_eq_univ.2 ?_)
      have hs1 : gaussMeasure s = 1 := hval ▸ h
      rw [measure_compl hs (measure_ne_top _ _), gaussMeasure_univ, hs1]
      simp

/-! ## Uniqueness of the absolutely continuous invariant probability -/

/-- **The Gauss measure is the unique absolutely continuous invariant probability.**  Ergodicity
makes the Radon–Nikodym derivative `dμ/dγ` — which is a.e. invariant for *any* pair of invariant
finite measures (`MeasurePreserving.rnDeriv_comp_aeEq`) — a.e. constant, and the total mass pins
the constant to `1`.  This is step (ii) of the `GaussACRigidity` discharge. -/
theorem eq_gaussMeasure_of_ac_invariant {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hac : μ ≪ gaussMeasure) (hinv : MeasurePreserving gaussMap μ μ)
    (hmass : μ Set.univ = 1) : μ = gaussMeasure := by
  obtain ⟨c, hc⟩ := ergodic_gaussMap.ae_eq_const_of_ae_eq_comp₀
    (μ.measurable_rnDeriv gaussMeasure).nullMeasurable
    (hinv.rnDeriv_comp_aeEq measurePreserving_gaussMap)
  have hμ : μ = gaussMeasure.withDensity (μ.rnDeriv gaussMeasure) :=
    (Measure.withDensity_rnDeriv_eq μ gaussMeasure hac).symm
  have hsm : μ = c • gaussMeasure := by
    rw [hμ, withDensity_congr_ae hc]
    show gaussMeasure.withDensity (fun _ => c) = c • gaussMeasure
    rw [withDensity_const]
  have hc1 : c = 1 := by
    have := hmass
    rw [hsm, Measure.smul_apply, smul_eq_mul, gaussMeasure_univ, mul_one] at this
    exact this
  rw [hsm, hc1, one_smul]

/-! ## Guard rule: locators and degenerate cases -/

/-- Degenerate case: the empty set is invariant, with `γ = 0`. -/
theorem gaussInvariant_empty : GaussInvariant (∅ : Set ℝ) := by
  intro x _ _; simp

/-- Content locator: the whole phase space is invariant (the Gauss map keeps irrationals of
`(0,1)` inside `(0,1)`), with `γ = 1` — so both alternatives of the ergodic dichotomy occur. -/
theorem gaussInvariant_Ioo : GaussInvariant (Ioo (0:ℝ) 1) := by
  intro x hirr hx
  exact ⟨fun _ => (irrational_gaussMap hirr hx).2, fun _ => hx⟩

/-- **The definition has content**: not every measurable subset of `(0,1)` is invariant.  The
half-interval `(0,1/2)` has `γ`-measure `log(3/2)/log 2 ∈ (0,1)`, so the ergodic dichotomy
refutes its invariance outright. -/
theorem not_gaussInvariant_Ioo_half : ¬ GaussInvariant (Ioo (0:ℝ) (1/2)) := by
  intro hinv
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog32 : (0:ℝ) < Real.log (3/2) := Real.log_pos (by norm_num)
  have hlt : Real.log (3/2) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  have hmeas : gaussMeasure (Ioo (0:ℝ) (1/2))
      = ENNReal.ofReal (Real.log (3/2) / Real.log 2) := by
    rw [gaussMeasure_Ioo (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hr0 : (0:ℝ) < Real.log (3/2) / Real.log 2 := by positivity
  have hr1 : Real.log (3/2) / Real.log 2 < 1 := (div_lt_one hlog2).2 hlt
  rcases gaussMeasure_eq_zero_or_one_of_invariant measurableSet_Ioo
    (Ioo_subset_Ioo le_rfl (by norm_num)) hinv with h | h
  · rw [hmeas, ENNReal.ofReal_eq_zero] at h; linarith
  · rw [hmeas] at h
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp] at h
    have := (ENNReal.ofReal_eq_ofReal_iff hr0.le zero_le_one).1 h
    linarith

section Audit

#print axioms gaussMeasure_cfCylinder_inter_invariant
#print axioms gaussMeasure_isOpen_inter_invariant
#print axioms gaussMeasure_inter_invariant
#print axioms gaussMeasure_eq_zero_or_one_of_invariant
#print axioms gaussInvariant_Ioo
#print axioms not_gaussInvariant_Ioo_half
#print axioms measurePreserving_gaussMap
#print axioms ergodic_gaussMap
#print axioms eq_gaussMeasure_of_ac_invariant

end Audit

end NormalNumbers
