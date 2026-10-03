/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.CantorSelfSimilar

/-!
# Missing-digit Cantor measures `ν_m` and their Frostman bound

Base `b = m + 2`, digits i.i.d. uniform in `{0, …, m}` (the top digit `m + 1` is missing),
`z = Σ D_i b^{-(i+1)}`, `y = 1/2 + z/2 ∈ [1/2, 1)`.  `nu m` is the law of `y`.

* `nu_eq_sum_map`: one-step self-similarity `ν = Σ_a (m+1)⁻¹ (f_a)_* ν`,
  `f_a t = t/b + 1/2 + (a − 1)/(2b)` (`yReal_cons`).
* `not_isNormal_yReal`: every `y` misses digit `m + 1` of `z`, so is not normal in base `b`.
* `nu_le_of_ediam_lt`: a set of diameter `< 1/(2 b^{n+1})` has `ν`-mass `≤ (m+1)^{-n}`
  (separation `sep_of_ne`: points whose digit strings differ before `n` are `b^{-(n+1)}` apart).
* `le_dimH_of_one_le_nu`: mass distribution principle, `d ≤ dim_H E` whenever `ν E ≥ 1`
  (outer measure), for every `d ≤ 1` with `b^d ≤ m + 1`.

This is the measure `ν_L` of `ExplicitOmegaK.dimH_Omega_eq_one` (with `b = 2^L`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace NormalNumbers.DigitCantor

variable (m : ℕ)

/-- I.i.d. uniform digits in `{0, …, m}`. -/
noncomputable def digitMeasure : Measure (ℕ → Fin (m + 1)) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin (m + 1))).toMeasure)

instance : IsProbabilityMeasure (digitMeasure m) := by
  unfold digitMeasure; infer_instance

/-- The digit string as `ℕ`-valued digits. -/
def digs (ω : ℕ → Fin (m + 1)) (i : ℕ) : ℕ := (ω i : ℕ)

/-- `z = Σ D_i b^{-(i+1)}`, `b = m + 2`. -/
noncomputable def zReal (ω : ℕ → Fin (m + 1)) : ℝ := realOfDigits (m + 2) (digs m ω)

/-- `y = 1/2 + z/2 ∈ [1/2, 1)`. -/
noncomputable def yReal (ω : ℕ → Fin (m + 1)) : ℝ := 1 / 2 + zReal m ω / 2

/-- The missing-digit Cantor measure: the law of `yReal`. -/
noncomputable def nu : Measure ℝ := (digitMeasure m).map (yReal m)

variable {m}

theorem digs_lt (ω : ℕ → Fin (m + 1)) (i : ℕ) : digs m ω i < m + 2 := by
  have := (ω i).isLt; unfold digs; omega

theorem digs_le (ω : ℕ → Fin (m + 1)) (i : ℕ) : digs m ω i ≤ m := by
  have := (ω i).isLt; unfold digs; omega

theorem digs_proper (ω : ℕ → Fin (m + 1)) : ProperDigits (m + 2) (digs m ω) := by
  intro N
  refine ⟨N, le_rfl, ?_⟩
  have := digs_le ω N
  omega

theorem zReal_mem_Ico (ω : ℕ → Fin (m + 1)) : zReal m ω ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico (m + 2) (by omega) _ (digs_lt ω) (digs_proper ω)

theorem yReal_mem_Icc (ω : ℕ → Fin (m + 1)) : yReal m ω ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  have h := zReal_mem_Ico ω
  unfold yReal
  constructor <;> linarith [h.1, h.2]

theorem measurable_zReal : Measurable (zReal m) := by
  unfold zReal realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  exact (measurable_of_countable (fun a : Fin (m + 1) => ((a : ℕ) : ℝ))).comp
    (measurable_pi_apply i)

theorem measurable_yReal : Measurable (yReal m) := by
  unfold yReal
  exact measurable_const.add (measurable_zReal.div_const _)

instance : IsProbabilityMeasure (nu m) := by
  unfold nu
  exact Measure.isProbabilityMeasure_map measurable_yReal.aemeasurable

/-! ## Non-normality -/

theorem count_top_eq_zero (ω : ℕ → Fin (m + 1)) (n : ℕ) :
    countOccurrences [m + 1] ((List.range n).map (digs m ω)) = 0 := by
  rw [countOccurrences_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i - ⟨-, h⟩
  have h1 : digs m ω i = m + 1 := by
    simp [List.range'] at h
    exact h.symm
  have := digs_le ω i
  omega

/-- `z` misses the digit `m + 1`, so it is not normal in base `m + 2`. -/
theorem not_isNormal_zReal (ω : ℕ → Fin (m + 1)) : ¬ IsNormal (m + 2) (zReal m ω) := by
  intro h
  have hmem := zReal_mem_Ico ω
  rw [Set.mem_Ico] at hmem
  unfold IsNormal at h
  rw [Int.fract_eq_self.mpr hmem, zReal,
    digitOf_realOfDigits (m + 2) (by omega) _ (digs_lt ω) (digs_proper ω)] at h
  have ht := h [m + 1] (by simp) (by intro d hd; simp at hd; omega)
  simp only [count_top_eq_zero, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  have hb : (0 : ℝ) < m + 2 := by positivity
  simp at this
  linarith

theorem not_isNormal_yReal (ω : ℕ → Fin (m + 1)) : ¬ IsNormal (m + 2) (yReal m ω) := by
  intro h
  have h' := isNormal_rat_mul_add (m + 2) (by omega) _ 2 (-1) (by norm_num) h
  apply not_isNormal_zReal ω
  convert h' using 1
  unfold yReal
  push_cast
  ring

/-! ## Self-similarity -/

theorem summable_digs (ω : ℕ → Fin (m + 1)) :
    Summable fun i => (digs m ω i : ℝ) / ((m + 2 : ℕ) : ℝ) ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) summable_geometric_two
  have hb : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have h1 : (digs m ω i : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (digs_lt ω i).le
  rw [div_le_iff₀ (by positivity)]
  refine h1.trans ?_
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
  linarith

/-- Prepend a digit. -/
def consF (a : Fin (m + 1)) (ω : ℕ → Fin (m + 1)) : ℕ → Fin (m + 1) := fun i => Nat.casesOn i a ω

theorem measurable_consF (a : Fin (m + 1)) : Measurable (consF a) := by
  refine measurable_pi_lambda _ fun i => ?_
  cases i with
  | zero => exact measurable_const
  | succ j => exact measurable_pi_apply j

theorem zReal_cons (a : Fin (m + 1)) (ω : ℕ → Fin (m + 1)) :
    zReal m (consF a ω) = ((a : ℕ) + zReal m ω) / (m + 2) := by
  unfold zReal realOfDigits
  rw [(summable_digs (consF a ω)).tsum_eq_zero_add]
  have : ∀ i, (digs m (consF a ω) (i + 1) : ℝ) / ((m + 2 : ℕ) : ℝ) ^ (i + 1 + 1) =
      (digs m ω i : ℝ) / ((m + 2 : ℕ) : ℝ) ^ (i + 1) / (m + 2) := by
    intro i
    have : digs m (consF a ω) (i + 1) = digs m ω i := rfl
    rw [this, div_div]
    push_cast; ring
  have h0 : digs m (consF a ω) 0 = a := rfl
  rw [tsum_congr this, tsum_div_const, h0]
  push_cast
  ring

/-- The IFS map `f_a t = t/b + 1/2 + (a − 1)/(2b)`. -/
noncomputable def fMap (a : Fin (m + 1)) (t : ℝ) : ℝ :=
  (1 / (m + 2 : ℝ)) * t + (1 / 2 + ((a : ℕ) - 1 : ℝ) / (2 * (m + 2)))

theorem yReal_cons (a : Fin (m + 1)) (ω : ℕ → Fin (m + 1)) :
    yReal m (consF a ω) = fMap a (yReal m ω) := by
  unfold yReal fMap
  rw [zReal_cons]
  have : (m + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

open Classical in
theorem uniform_apply (A : Set (Fin (m + 1))) :
    (PMF.uniformOfFintype (Fin (m + 1))).toMeasure A =
      ∑ a, ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ * (if a ∈ A then 1 else 0) := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Set.indicator, PMF.uniformOfFintype_apply]

open Classical in
theorem preimage_consF_pi (a : Fin (m + 1)) (s : Finset ℕ) (t : ℕ → Set (Fin (m + 1))) :
    consF a ⁻¹' Set.pi (↑s) t =
      if (0 ∈ s → a ∈ t 0) then Set.pi ↑(s.preimage Nat.succ (Nat.succ_injective.injOn))
        (fun j => t (j + 1)) else ∅ := by
  ext ω
  split_ifs with h
  · simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_preimage]
    constructor
    · intro hω j hj; exact hω (j + 1) hj
    · intro hω i hi
      cases i with
      | zero => exact h hi
      | succ j => exact hω j hi
  · simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_empty_iff_false, iff_false]
    intro hω
    push Not at h
    exact h.2 (hω 0 h.1)

theorem card_inv_sum :
    ∑ _a : Fin (m + 1), ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

open Classical in
/-- **One-step self-similarity of the digit measure.** -/
theorem digitMeasure_eq :
    digitMeasure m = ∑ a : Fin (m + 1),
      ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ • (digitMeasure m).map (consF a) := by
  symm
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpi : MeasurableSet (Set.pi (↑s) t) := MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hc : digitMeasure m (Set.pi ↑(s.preimage Nat.succ (Nat.succ_injective.injOn))
      (fun j => t (j + 1))) =
      ∏ j ∈ s.preimage Nat.succ (Nat.succ_injective.injOn),
        (PMF.uniformOfFintype (Fin (m + 1))).toMeasure (t (j + 1)) := by
    unfold digitMeasure
    exact Measure.infinitePi_pi _ fun j _ => ht (j + 1)
  simp_rw [Measure.map_apply (measurable_consF _) hpi, preimage_consF_pi, apply_ite (digitMeasure m),
    measure_empty, hc]
  rw [CantorSelfSimilar.prod_split s]
  generalize (∏ j ∈ s.preimage Nat.succ (Nat.succ_injective.injOn),
    (PMF.uniformOfFintype (Fin (m + 1))).toMeasure (t (j + 1))) = X
  by_cases h0 : 0 ∈ s
  · simp only [h0, true_implies, if_true, uniform_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  · simp only [h0, false_implies, if_true, if_false, one_mul]
    rw [← Finset.sum_mul (s := Finset.univ) (f := fun _ : Fin (m + 1) => ((m + 1 : ℕ) : ℝ≥0∞)⁻¹),
      card_inv_sum, one_mul]

/-- **Self-similarity of `ν`**: `ν = Σ_a (m+1)⁻¹ (f_a)_* ν`. -/
theorem nu_eq_sum_map :
    nu m = ∑ a : Fin (m + 1), ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ • (nu m).map (fMap a) := by
  ext A hA
  have hfm : ∀ a : Fin (m + 1), Measurable (fMap a) := fun a => by
    unfold fMap; fun_prop
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  unfold nu
  rw [Measure.map_apply measurable_yReal hA]
  conv_lhs => rw [digitMeasure_eq]
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (measurable_consF a) (measurable_yReal hA),
    Measure.map_apply (hfm a) hA, Measure.map_apply measurable_yReal ((hfm a) hA)]
  congr 2
  ext ω
  simp [yReal_cons]

/-! ## Separation and the Frostman bound -/

/-- One-sided separation at the first differing digit `j`. -/
theorem sep_aux (ω ω' : ℕ → Fin (m + 1)) (j : ℕ) (hpre : ∀ k < j, ω k = ω' k)
    (hlt : (ω' j : ℕ) < ω j) :
    1 / ((m + 2 : ℕ) : ℝ) ^ (j + 1 + 1) ≤ zReal m ω - zReal m ω' := by
  have hb : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hF := floor_realOfDigits_mul_pow (m + 2) (by omega) _ (digs_lt ω) (digs_proper ω) (j + 1)
  have hF' := floor_realOfDigits_mul_pow (m + 2) (by omega) _ (digs_lt ω') (digs_proper ω') (j + 1)
  set N := ∑ k ∈ Finset.range (j + 1 + 1), digs m ω k * (m + 2) ^ (j + 1 - k) with hN
  set N' := ∑ k ∈ Finset.range (j + 1 + 1), digs m ω' k * (m + 2) ^ (j + 1 - k) with hN'
  have hNN : N' + 2 ≤ N := by
    rw [hN, hN', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have hP : ∑ k ∈ Finset.range j, digs m ω k * (m + 2) ^ (j + 1 - k) =
        ∑ k ∈ Finset.range j, digs m ω' k * (m + 2) ^ (j + 1 - k) :=
      Finset.sum_congr rfl fun k hk => by rw [Finset.mem_range] at hk; simp [digs, hpre k hk]
    rw [hP, show j + 1 - j = 1 by omega, Nat.sub_self, pow_one, pow_zero, mul_one, mul_one]
    have h1 : (digs m ω' j + 1) * (m + 2) ≤ digs m ω j * (m + 2) := Nat.mul_le_mul_right _ hlt
    have h2 := digs_le ω' (j + 1)
    nlinarith
  have hz := Int.floor_le (zReal m ω * ((m + 2 : ℕ) : ℝ) ^ (j + 1 + 1))
  have hz' := Int.lt_floor_add_one (zReal m ω' * ((m + 2 : ℕ) : ℝ) ^ (j + 1 + 1))
  unfold zReal at hz hz' ⊢
  rw [hF] at hz
  rw [hF'] at hz'
  simp only [Int.cast_natCast] at hz hz'
  have hNN' : (N' : ℝ) + 2 ≤ N := by exact_mod_cast hNN
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Points whose digit strings differ before `n` are at least `b^{-(n+1)}` apart. -/
theorem sep_of_ne (ω ω' : ℕ → Fin (m + 1)) (n : ℕ) (h : ∃ j < n, ω j ≠ ω' j) :
    1 / ((m + 2 : ℕ) : ℝ) ^ (n + 1) ≤ |zReal m ω - zReal m ω'| := by
  classical
  have hex : ∃ j, ω j ≠ ω' j := let ⟨j, _, hj⟩ := h; ⟨j, hj⟩
  have hjn : Nat.find hex < n := by
    obtain ⟨j', hj', hne⟩ := h; exact lt_of_le_of_lt (Nat.find_min' hex hne) hj'
  have hpre : ∀ k < Nat.find hex, ω k = ω' k := fun k hk => not_not.1 (Nat.find_min hex hk)
  have hne : ω (Nat.find hex) ≠ ω' (Nat.find hex) := Nat.find_spec hex
  have hb : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hmono : 1 / ((m + 2 : ℕ) : ℝ) ^ (n + 1) ≤ 1 / ((m + 2 : ℕ) : ℝ) ^ (Nat.find hex + 1 + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hb (by omega))
  have hne' : (ω (Nat.find hex) : ℕ) ≠ ω' (Nat.find hex) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hl | hl
  · have := sep_aux ω' ω _ (fun k hk => (hpre k hk).symm) hl
    rw [abs_sub_comm]; exact hmono.trans (this.trans (le_abs_self _))
  · have := sep_aux ω ω' _ hpre hl
    exact hmono.trans (this.trans (le_abs_self _))

theorem cylinder_measure (ω₀ : ℕ → Fin (m + 1)) (n : ℕ) :
    digitMeasure m {ω | ∀ j < n, ω j = ω₀ j} = (((m + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ n := by
  have hset : {ω : ℕ → Fin (m + 1) | ∀ j < n, ω j = ω₀ j} =
      Set.pi ↑(Finset.range n) (fun j => {ω₀ j}) := by
    ext ω; simp
  rw [hset]
  unfold digitMeasure
  rw [Measure.infinitePi_pi _ fun j _ => measurableSet_singleton _]
  simp [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

/-- **Frostman at scale `n`.** -/
theorem nu_le_of_ediam_lt (s : Set ℝ) (n : ℕ)
    (hs : Metric.ediam s < ENNReal.ofReal (1 / (2 * ((m + 2 : ℕ) : ℝ) ^ (n + 1)))) :
    nu m s ≤ (((m + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ n := by
  have hcl : MeasurableSet (closure s) := isClosed_closure.measurableSet
  calc nu m s ≤ nu m (closure s) := measure_mono subset_closure
    _ = digitMeasure m (yReal m ⁻¹' closure s) := Measure.map_apply measurable_yReal hcl
    _ ≤ _ := by
      rcases (yReal m ⁻¹' closure s).eq_empty_or_nonempty with he | ⟨ω₀, hω₀⟩
      · rw [he, measure_empty]; exact zero_le
      · rw [← cylinder_measure ω₀ n]
        refine measure_mono fun ω hω => ?_
        by_contra hc
        simp only [Set.mem_ofPred_eq, not_forall] at hc
        obtain ⟨j, hj, hne⟩ := hc
        have hsep := sep_of_ne ω ω₀ n ⟨j, hj, hne⟩
        have hd : edist (yReal m ω) (yReal m ω₀) ≤ Metric.ediam s := by
          rw [← Metric.ediam_closure]; exact Metric.edist_le_ediam_of_mem hω hω₀
        have hlt := hd.trans_lt hs
        rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity), Real.dist_eq] at hlt
        have h1 : yReal m ω - yReal m ω₀ = (zReal m ω - zReal m ω₀) / 2 := by unfold yReal; ring
        have h2 : 1 / (2 * ((m + 2 : ℕ) : ℝ) ^ (n + 1)) = (1 / ((m + 2 : ℕ) : ℝ) ^ (n + 1)) / 2 := by
          ring
        rw [h1, abs_div, abs_two, h2] at hlt
        linarith

/-- **Frostman bound** `ν(s) ≤ C · ediam(s)^d`. -/
theorem nu_le_mul_ediam_rpow (d : ℝ≥0) (hd1 : d ≤ 1)
    (hd : ((m + 2 : ℕ) : ℝ) ^ (d : ℝ) ≤ m + 1) (s : Set ℝ)
    (hs : Metric.ediam s ≤ ENNReal.ofReal (1 / (4 * (m + 2 : ℕ)))) :
    nu m s ≤ (2 * ((m + 2 : ℕ) : ℝ≥0∞) ^ 2) * Metric.ediam s ^ (d : ℝ) := by
  set b : ℝ := ((m + 2 : ℕ) : ℝ) with hbdef
  have hb1 : (1 : ℝ) < b := by rw [hbdef]; push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hb0 : (0 : ℝ) < b := by linarith
  have hnu1 : nu m s ≤ 1 := prob_le_one
  rcases eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]; simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    refine hnu1.trans ?_
    calc (1 : ℝ≥0∞) ≤ 2 * 1 := by norm_num
      _ ≤ 2 * ((m + 2 : ℕ) : ℝ≥0∞) ^ 2 := by gcongr; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
  -- `q = m + 1 > 1`
  have hq1 : (1 : ℝ) < m + 1 := lt_of_lt_of_le (Real.one_lt_rpow hb1 hdpos') hd
  have hqinv : ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]; exact_mod_cast (show (1 : ℝ) < ((m + 1 : ℕ) : ℝ) by push_cast; exact hq1)
  have hscale : ∀ n : ℕ, (0 : ℝ) < 1 / (2 * b ^ (n + 1)) := fun n => by positivity
  rcases eq_zero_or_pos (Metric.ediam s) with hD0 | hDpos
  · -- diameter zero: mass `≤ q^{-n}` for all `n`
    rw [hD0, ENNReal.zero_rpow_of_pos hdpos', mul_zero]
    refine ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hqinv) fun n => ?_
    refine nu_le_of_ediam_lt s n ?_
    rw [hD0]; exact ENNReal.ofReal_pos.2 (hscale n)
  have hDtop : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  set δ := (Metric.ediam s).toReal with hδ
  have hDeq : Metric.ediam s = ENNReal.ofReal δ := (ENNReal.ofReal_toReal hDtop).symm
  have hδpos : 0 < δ := ENNReal.toReal_pos hDpos.ne' hDtop
  have hδle : δ ≤ 1 / (4 * b) := by
    rw [hDeq] at hs
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hs
  -- the scale `n₀`
  have hex : ∃ n : ℕ, 1 / (2 * b ^ (n + 1 + 1)) ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδpos (show 1 / b < 1 by rw [div_lt_one hb0]; exact hb1)
    refine ⟨n, le_of_lt (lt_of_le_of_lt ?_ hn)⟩
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have : b ^ n ≤ b ^ (n + 1 + 1) := pow_le_pow_right₀ hb1.le (by omega)
    nlinarith [pow_pos hb0 n]
  classical
  set n₀ := Nat.find hex
  have hlow : 1 / (2 * b ^ (n₀ + 1 + 1)) ≤ δ := Nat.find_spec hex
  have hup : δ < 1 / (2 * b ^ (n₀ + 1)) := by
    rcases Nat.eq_zero_or_eq_succ_pred n₀ with h0 | hsucc
    · rw [h0]
      refine lt_of_le_of_lt hδle ?_
      apply one_div_lt_one_div_of_lt (by positivity)
      simp only [zero_add, pow_one]
      linarith
    · have := Nat.find_min hex (show n₀.pred < n₀ by omega)
      push Not at this
      rw [hsucc]; exact this
  have hmass : nu m s ≤ (((m + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ n₀ := by
    refine nu_le_of_ediam_lt s n₀ ?_
    rw [hDeq]; exact (ENNReal.ofReal_lt_ofReal_iff (hscale n₀)).2 hup
  refine hmass.trans ?_
  -- real inequality `q^{-n₀} ≤ 2b² δ^d`
  have hreal : (1 / ((m : ℝ) + 1)) ^ n₀ ≤ 2 * b ^ 2 * δ ^ (d : ℝ) := by
    have h1 : (1 / (2 * b ^ (n₀ + 1 + 1))) ^ (d : ℝ) ≤ δ ^ (d : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlow hdpos'.le
    have h2 : (1 / (2 * b ^ (n₀ + 1 + 1))) ^ (d : ℝ) =
        1 / ((2 * b ^ 2) ^ (d : ℝ) * (b ^ (d : ℝ)) ^ n₀) := by
      rw [show 2 * b ^ (n₀ + 1 + 1) = (2 * b ^ 2) * b ^ n₀ by ring,
        Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast b n₀,
        ← Real.rpow_mul hb0.le, mul_comm (n₀ : ℝ), Real.rpow_mul hb0.le, Real.rpow_natCast]
    have h3 : (2 * b ^ 2) ^ (d : ℝ) ≤ 2 * b ^ 2 := by
      calc (2 * b ^ 2) ^ (d : ℝ) ≤ (2 * b ^ 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by exact_mod_cast hd1)
        _ = 2 * b ^ 2 := Real.rpow_one _
    have h4 : (b ^ (d : ℝ)) ^ n₀ ≤ ((m : ℝ) + 1) ^ n₀ :=
      pow_le_pow_left₀ (by positivity) hd n₀
    have hA : 0 < (2 * b ^ 2) ^ (d : ℝ) := by positivity
    have hB : 0 < (b ^ (d : ℝ)) ^ n₀ := by positivity
    rw [h2] at h1
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 (by positivity))
    rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_div, ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    have : (2 * b ^ 2) ^ (d : ℝ) * (b ^ (d : ℝ)) ^ n₀ ≤ 2 * b ^ 2 * ((m : ℝ) + 1) ^ n₀ :=
      mul_le_mul h3 h4 hB.le (by positivity)
    linarith
  have hL : (((m + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ n₀ = ENNReal.ofReal ((1 / ((m : ℝ) + 1)) ^ n₀) := by
    rw [ENNReal.ofReal_pow (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 2
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have hR : (2 * ((m + 2 : ℕ) : ℝ≥0∞) ^ 2) * Metric.ediam s ^ (d : ℝ) =
      ENNReal.ofReal (2 * b ^ 2 * δ ^ (d : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow hb0.le, hbdef, ENNReal.ofReal_natCast, hDeq,
      ENNReal.ofReal_rpow_of_nonneg hδpos.le hdpos'.le]
    simp
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Mass distribution principle for `ν`.** -/
theorem le_dimH_of_one_le_nu (d : ℝ≥0) (hd1 : d ≤ 1)
    (hd : ((m + 2 : ℕ) : ℝ) ^ (d : ℝ) ≤ m + 1) (E : Set ℝ) (hE : 1 ≤ nu m E) :
    (d : ℝ≥0∞) ≤ dimH E := by
  set C : ℝ≥0∞ := 2 * ((m + 2 : ℕ) : ℝ≥0∞) ^ 2
  have hC0 : C ≠ 0 := by simp [C]
  have hCt : C ≠ ⊤ := by simp [C, ENNReal.mul_eq_top]
  have hle : C⁻¹ • nu m ≤ μH[(d : ℝ)] := by
    refine Measure.le_hausdorffMeasure _ _ (ENNReal.ofReal (1 / (4 * (m + 2 : ℕ))))
      (by simp; positivity) fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    calc C⁻¹ * nu m s ≤ C⁻¹ * (C * Metric.ediam s ^ (d : ℝ)) := by
          gcongr; exact nu_le_mul_ediam_rpow d hd1 hd s hs
      _ = Metric.ediam s ^ (d : ℝ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  refine le_dimH_of_hausdorffMeasure_ne_zero ?_
  intro h0
  have := hle E
  rw [h0, Measure.smul_apply, smul_eq_mul] at this
  have h1 : C⁻¹ * 1 ≤ C⁻¹ * nu m E := by gcongr
  have : C⁻¹ = 0 := le_antisymm (by simpa using h1.trans this) bot_le
  exact ENNReal.inv_ne_zero.2 hCt this

end NormalNumbers.DigitCantor
