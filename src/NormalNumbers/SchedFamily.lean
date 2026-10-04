/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SchedDerandomize

/-!
# Derandomization along a slow schedule, all bases of a primitive-recursive family

`SchedDerandomize.exists_computable_normal_sched` for every base `b` with `S b` at once.  The
base-`2` visit-deviation and level machinery is copied with `2 → b`
(`visit_deviation_wb`, `level_bound_wb`).  Base `b` runs at the reduced resolution
`n / h b` (`hres`), which shrinks its level mass by `(h b)³`; with `h b ≥ 2^b · (bound)`
the masses of all bases at one stage sum to `O(1/(J+1)²)`, so the base-2 assembly goes through
unchanged (`exists_computable_normal_sched_family'`).
-/

open MeasureTheory Filter Topology Complex

namespace NormalNumbers.SchedFamily

open DecayAeNormal VisitDeviation

/-- **Probabilistic deviation of an orbit average** of a test function with summable
Fourier coefficient majorant `B`. -/
theorem prob_mean_dev_wb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (G : Ω → ℝ) (hG : Measurable G) (N : ℕ) (hN : 1 ≤ N) (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hsm : ∀ n : ℤ, n ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (n * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤ (w n) ^ 2 * (N : ℝ) ^ 2)
    (f : C(AddCircle (1 : ℝ), ℂ)) (B : ℤ → ℝ) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n, n ≠ 0 → ‖fourierCoeff f n‖ ≤ B n) (hBs : Summable B)
    (hBw : Summable fun n => B n * w n) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < ‖(∑ k ∈ Finset.range N, f (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff f 0‖} ≤
      (∑' n, B n * w n) / t := by
  set A : ℤ → Ω → ℂ := fun n ω => (∑ k ∈ Finset.range N, ee (n * ((b : ℝ) ^ k * G ω))) / N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hAm : ∀ n, Measurable (A n) := fun n =>
    (Finset.measurable_sum _ fun k _ =>
      measurable_ee.comp ((hG.const_mul _).const_mul _)).div_const _
  have hAb : ∀ n ω, ‖A n ω‖ ≤ 1 := by
    intro n ω
    simp only [A]
    rw [norm_div, Complex.norm_natCast, div_le_one hNpos]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_ee]
  set X : Ω → ℝ := fun ω => ∑' n, (if n = 0 then 0 else B n * ‖A n ω‖)
  have hle : ∀ ω, ‖(∑ k ∈ Finset.range N, f (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
      fourierCoeff f 0‖ ≤ X ω := fun ω =>
    mean_sub_coeff_le f B hB0 hB hBs (fun k => (b : ℝ) ^ k * G ω) N hN
  -- integrals of the Weyl means
  have hAint : ∀ n, n ≠ 0 → ∫ ω, ‖A n ω‖ ∂μ ≤ w n := by
    intro n hn
    have hsm := hsm n hn
    refine (integral_le_sqrt_integral_sq μ _ (hAm n).norm 1
      (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hAb n ω)).trans ?_
    rw [← Real.sqrt_sq (hw0 n)]
    refine Real.sqrt_le_sqrt ?_
    have hpt : ∀ ω, ‖A n ω‖ ^ 2 =
        ‖∑ k ∈ Finset.range N, ee (n * (b : ℝ) ^ k * G ω)‖ ^ 2 / (N : ℝ) ^ 2 := by
      intro ω
      simp only [A]
      rw [norm_div, Complex.norm_natCast, div_pow]
      congr 3
      refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc]
    simp_rw [hpt]
    rw [integral_div, div_le_iff₀ (by positivity)]
    exact hsm
  have hFint : ∀ n, Integrable (fun ω => if n = 0 then (0 : ℝ) else B n * ‖A n ω‖) μ := by
    intro n
    split_ifs
    · exact integrable_const _
    · exact ((Integrable.of_bound (hAm n).norm.aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hAb n ω)).const_mul _)
  have hFnorm : ∀ n, ∫ ω, ‖(if n = 0 then (0 : ℝ) else B n * ‖A n ω‖)‖ ∂μ ≤ B n := by
    intro n
    split_ifs
    · simp [hB0]
    · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
        (integrable_const (B n)) (Eventually.of_forall fun ω => ?_)).trans (by simp)
      show ‖B n * ‖A n ω‖‖ ≤ B n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hB0 n) (norm_nonneg _))]
      exact mul_le_of_le_one_right (hB0 n) (hAb n ω)
  have hsumI : Summable fun n => ∫ ω, ‖(if n = 0 then (0 : ℝ) else B n * ‖A n ω‖)‖ ∂μ :=
    hBs.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hFnorm
  have hXint_eq : ∫ ω, X ω ∂μ = ∑' n, ∫ ω, (if n = 0 then (0 : ℝ) else B n * ‖A n ω‖) ∂μ :=
    (integral_tsum_of_summable_integral_norm hFint hsumI).symm
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    tsum_nonneg fun n => by split_ifs; exact le_rfl; exact mul_nonneg (hB0 n) (norm_nonneg _)
  have hXb : ∀ ω, X ω ≤ ∑' n, B n := fun ω =>
    (hBs.of_nonneg_of_le (fun n => by
        split_ifs; exact le_rfl; exact mul_nonneg (hB0 n) (norm_nonneg _))
      (fun n => by
        split_ifs; exact hB0 n; exact mul_le_of_le_one_right (hB0 n) (hAb n ω))).tsum_le_tsum
      (fun n => by split_ifs; exact hB0 n; exact mul_le_of_le_one_right (hB0 n) (hAb n ω)) hBs
  have hXm : Measurable X := Measurable.tsum fun n => by
    split_ifs
    · exact measurable_const
    · exact (hAm n).norm.const_mul _
  have hXi : Integrable X μ := Integrable.of_bound hXm.aestronglyMeasurable (∑' n, B n)
    (Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hX0 ω)]; exact hXb ω)
  have hEX : ∫ ω, X ω ∂μ ≤ ∑' n, B n * w n := by
    rw [hXint_eq]
    refine (hsumI.of_nonneg_of_le (fun n => ?_) (fun n => ?_)).tsum_le_tsum (fun n => ?_)
      hBw
    · split_ifs
      · simp
      · exact integral_nonneg fun ω => mul_nonneg (hB0 n) (norm_nonneg _)
    · exact (integral_mono_of_nonneg (Eventually.of_forall fun ω => by
        split_ifs; exact le_rfl; exact mul_nonneg (hB0 n) (norm_nonneg _))
        (hFint n).norm (Eventually.of_forall fun ω => le_abs_self _))
    · split_ifs with h
      · simp only [integral_const, smul_zero]
        exact mul_nonneg (hB0 n) (hw0 n)
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hAint n h) (hB0 n)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Eventually.of_forall hX0) hXi t
  calc μ.real {ω | t < ‖(∑ k ∈ Finset.range N,
        f (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N - fourierCoeff f 0‖}
      ≤ μ.real {ω | t ≤ X ω} := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        exact (le_of_lt hω).trans (hle ω)
    _ ≤ (∫ ω, X ω ∂μ) / t := by rw [le_div_iff₀ ht, mul_comm]; exact hmarkov
    _ ≤ (∑' n, B n * w n) / t := by gcongr


/-- **Visit-count deviation from a second-moment bound.** -/
theorem visit_deviation_wb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (G : Ω → ℝ) (hG : Measurable G) (N : ℕ) (hN : 1 ≤ N) (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hsm : ∀ n : ℤ, n ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (n * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤ (w n) ^ 2 * (N : ℝ) ^ 2)
    (a c ρ t : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hlen : c - a ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (ht : 0 < t) (hBw : Summable fun n => plB ρ n * w n) :
    μ.real {ω | 2 * ρ + t < |(visitCount (orbit b (G ω)) a c N : ℝ) / N - (c - a)|} ≤
      2 * ((∑' n, plB ρ n * w n) / t) := by
  set fU := HatFourier.plateau ((c - a) / 2 + ρ) ρ ((a + c) / 2)
  set fL := HatFourier.plateau ((c - a) / 2) ρ ((a + c) / 2)
  have hBU : ∀ n, n ≠ 0 → ‖fourierCoeff fU n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hBL : ∀ n, n ≠ 0 → ‖fourierCoeff fL n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hB0 : ∀ n, 0 ≤ plB ρ n := fun n => by unfold plB; positivity
  have hdU := prob_mean_dev_wb μ b G hG N hN w hw0 hsm fU (plB ρ) hB0 hBU (hasSum_plB ρ hρ).summable hBw t ht
  have hdL := prob_mean_dev_wb μ b G hG N hN w hw0 hsm fL (plB ρ) hB0 hBL (hasSum_plB ρ hρ).summable hBw t ht
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hIU := integral_trapUp_le a c ρ ha hac hc hρ
  have hIL := le_integral_trapLo a c ρ ha hac hc hρ
  have hcU : fourierCoeff fU 0 = ((∫ x in (0 : ℝ)..1, trapUp a c ρ ((x : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) :=
    coeff_zero_real _ _ (plateau_coe_trapUp a c ρ)
  have hcL : fourierCoeff fL 0 = ((∫ x in (0 : ℝ)..1, trapLo a c ρ ((x : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) :=
    coeff_zero_real _ _ (plateau_coe_trapLo a c ρ)
  have hsub : {ω | 2 * ρ + t < |(visitCount (orbit b (G ω)) a c N : ℝ) / N - (c - a)|} ⊆
      {ω | t < ‖(∑ k ∈ Finset.range N, fU (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fU 0‖} ∪
      {ω | t < ‖(∑ k ∈ Finset.range N, fL (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fL 0‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    set u := orbit b (G ω)
    have hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1 := fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hcoe : ∀ k, ((u k : ℝ) : AddCircle (1 : ℝ)) = (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ)) := by
      intro k
      simp only [u, orbit, AddCircle.coe_fract]
      push_cast; ring_nf
    have hcard : (visitCount u a c N : ℝ)
        = ∑ k ∈ Finset.range N, (if (a ≤ u k ∧ u k < c) then (1:ℝ) else 0) := by
      rw [visitCount, Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : a ≤ u k ∧ u k < c
      · simp [Set.mem_Ico, h.1, h.2]
      · simp [Set.mem_Ico, h]
    have hUp : (visitCount u a c N : ℝ)
        ≤ ∑ k ∈ Finset.range N, trapUp a c ρ ((u k : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hcard]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases h : a ≤ u k ∧ u k < c
      · rw [if_pos h]; exact trapUp_ge_indicator a c ρ (u k) hρ h
      · rw [if_neg h]; exact trapUp_nonneg a c ρ hρ _
    have hLo : (∑ k ∈ Finset.range N, trapLo a c ρ ((u k : ℝ) : AddCircle (1 : ℝ)))
        ≤ (visitCount u a c N : ℝ) := by
      rw [hcard]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases h : a ≤ u k ∧ u k < c
      · rw [if_pos h]; exact trapLo_le_one a c ρ _
      · rw [if_neg h]
        have hk := hu k
        rw [trapLo_eq_zero_outside a c ρ (u k) ha hac hc hk.1 hk.2 h hρ]
    set SU := ∑ k ∈ Finset.range N, trapUp a c ρ ((u k : ℝ) : AddCircle (1 : ℝ))
    set SL := ∑ k ∈ Finset.range N, trapLo a c ρ ((u k : ℝ) : AddCircle (1 : ℝ))
    set IU := ∫ x in (0 : ℝ)..1, trapUp a c ρ ((x : ℝ) : AddCircle (1 : ℝ))
    set IL := ∫ x in (0 : ℝ)..1, trapLo a c ρ ((x : ℝ) : AddCircle (1 : ℝ))
    have heU : (∑ k ∈ Finset.range N, fU (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fU 0 = ((SU / N - IU : ℝ) : ℂ) := by
      rw [hcU]; simp only [SU, ← hcoe, plateau_coe_trapUp, fU]; push_cast; rfl
    have heL : (∑ k ∈ Finset.range N, fL (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fL 0 = ((SL / N - IL : ℝ) : ℂ) := by
      rw [hcL]; simp only [SL, ← hcoe, plateau_coe_trapLo, fL]; push_cast; rfl
    simp only [Set.mem_union, Set.mem_setOf_eq, heU, heL, Complex.norm_real, Real.norm_eq_abs]
    have hdU' : (visitCount u a c N : ℝ) / N ≤ SU / N := div_le_div_of_nonneg_right hUp hNR.le
    have hdL' : SL / N ≤ (visitCount u a c N : ℝ) / N := div_le_div_of_nonneg_right hLo hNR.le
    rcases lt_abs.1 hω with h | h
    · left; rw [lt_abs]; left; linarith
    · right; rw [lt_abs]; right; linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  linarith

open SchedDerandomize Derandomize
open ComputableNormalB (list_sum_range_map exists_pos_of_sum_pos)

variable (G : (ℕ → Bool) → ℝ)

/-- Block deviation `> 1/(2n)` at count `N`. -/
theorem block_prob_wb (hG : Measurable G) {b : ℕ} (hb : 2 ≤ b) {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {N : ℕ}
    (hN : 1 ≤ N)
    (hsm : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤ κ * |(h : ℝ)| * N ^ 2 * Wv)
    {n ℓ v : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hv : v < b ^ ℓ) :
    coins.real {ω | 1 / (2 * (n : ℝ)) <
      |(visitCount (orbit b (G ω)) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) N : ℝ) /
        (N : ℝ) - 1 / (b : ℝ) ^ ℓ|} ≤ 144 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hvR : (v : ℝ) + 1 ≤ (b : ℝ) ^ ℓ := by exact_mod_cast hv
  have hP2 : (2 : ℝ) ≤ (b : ℝ) ^ ℓ := by
    have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
    calc (2 : ℝ) ≤ (b : ℝ) ^ 1 := by simpa using hbR
      _ ≤ (b : ℝ) ^ ℓ := pow_le_pow_right₀ (by linarith) hℓ
  set ρ : ℝ := 1 / (6 * (n : ℝ))
  have hρ : 0 < ρ := by positivity
  set w : ℤ → ℝ := fun h => Real.sqrt (κ * Wv * |(h : ℝ)|)
  have hsm' : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤ (w h) ^ 2 * (N : ℝ) ^ 2 := by
    intro h hh
    rw [Real.sq_sqrt (by positivity)]
    refine (hsm h hh).trans (le_of_eq ?_); ring
  have hS := hasSum_plB_w ρ hρ (κ * Wv) (by positivity)
  have e1 : (v + 1 : ℝ) / (b : ℝ) ^ ℓ - (v : ℝ) / (b : ℝ) ^ ℓ = 1 / (b : ℝ) ^ ℓ := by ring
  have hdev := visit_deviation_wb coins b G hG N hN w (fun h => Real.sqrt_nonneg _) hsm'
    ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) ρ ρ
    (by positivity) (by gcongr; linarith) (by rw [div_le_one hP]; exact hvR)
    (by rw [e1, div_le_div_iff₀ hP (by norm_num)]; linarith)
    hρ (by simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    hρ hS.summable
  rw [e1, hS.tsum_eq] at hdev
  have e2 : 2 * ρ + ρ = 1 / (2 * (n : ℝ)) := by simp only [ρ]; field_simp; ring
  rw [e2] at hdev
  refine hdev.trans ?_
  have hpi : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  have hZ := Zc_nonneg
  have hsq := Real.sqrt_nonneg (κ * Wv)
  simp only [ρ]
  rw [show 2 * (2 / (1 / (6 * (n : ℝ)) * Real.pi ^ 2) * Real.sqrt (κ * Wv) * Zc / (1 / (6 * (n : ℝ))))
      = 144 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc / Real.pi ^ 2 by
    field_simp; ring]
  exact div_le_self (by positivity) hpi

/-- Visits to a short cell exceeding `N/(8n)` among `N + n` points. -/
theorem tail_prob_wb (hG : Measurable G) (b : ℕ) {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hsm : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
      κ * |(h : ℝ)| * ((N + n : ℕ) : ℝ) ^ 2 * Wv)
    (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hlen : c - a ≤ 1 / (32 * (n : ℝ))) :
    coins.real {ω | (N : ℝ) < 8 * n * visitCount (orbit b (G ω)) a c (N + n)} ≤
      36864 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 1 ≤ N + n := by omega
  set ρ : ℝ := 1 / (96 * (n : ℝ))
  have hρ : 0 < ρ := by positivity
  set w : ℤ → ℝ := fun h => Real.sqrt (κ * Wv * |(h : ℝ)|)
  have hsm' : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
      (w h) ^ 2 * ((N + n : ℕ) : ℝ) ^ 2 := by
    intro h hh
    rw [Real.sq_sqrt (by positivity)]
    refine (hsm h hh).trans (le_of_eq ?_); ring
  have hS := hasSum_plB_w ρ hρ (κ * Wv) (by positivity)
  have hdev := visit_deviation_wb coins b G hG (N + n) hN1 w (fun h => Real.sqrt_nonneg _) hsm' a c ρ ρ
    ha hac hc (hlen.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith))
    hρ (by simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith) hρ
    hS.summable
  rw [hS.tsum_eq] at hdev
  have hsub : {ω | (N : ℝ) < 8 * n * visitCount (orbit b (G ω)) a c (N + n)} ⊆
      {ω | 2 * ρ + ρ <
        |(visitCount (orbit b (G ω)) a c (N + n) : ℝ) / ((N + n : ℕ) : ℝ) - (c - a)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    set V := (visitCount (orbit b (G ω)) a c (N + n) : ℝ)
    have hNn : (0 : ℝ) < ((N + n : ℕ) : ℝ) := by positivity
    have hle : ((N + n : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast; have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      linarith
    have h1 : 1 / (16 * (n : ℝ)) < V / ((N + n : ℕ) : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hNn]
      nlinarith
    have e : 2 * ρ + ρ = 1 / (32 * (n : ℝ)) := by simp only [ρ]; field_simp; ring
    rw [e, lt_abs]; left
    have : 1 / (16 * (n : ℝ)) = 1 / (32 * (n : ℝ)) + 1 / (32 * (n : ℝ)) := by
      field_simp; ring
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hdev.trans ?_)
  have hpi : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  have hZ := Zc_nonneg
  simp only [ρ]
  rw [show 2 * (2 / (1 / (96 * (n : ℝ)) * Real.pi ^ 2) * Real.sqrt (κ * Wv) * Zc / (1 / (96 * (n : ℝ))))
      = 36864 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc / Real.pi ^ 2 by
    field_simp; ring]
  exact div_le_self (by positivity) hpi

/-! ## Base-`b` level tests -/

section Level

variable (Ψ : ℕ → ℕ → List Bool → ℕ)

/-- Number of failing base-`b` tests at resolution `n`, count `N`. -/
def levelBadB (b n N : ℕ) (p : List Bool) : ℕ :=
  (if failsTop Ψ b n N p then 1 else 0) +
  ((List.range (n + 1)).map fun ℓ => if 1 ≤ ℓ ∧ b ^ ℓ ≤ n then
    ((List.range (b ^ ℓ)).map fun v => if fails Ψ b n N ℓ v p then 1 else 0).sum else 0).sum


theorem levelBadB_pos_cases {b n N : ℕ} {p : List Bool} (h : 0 < levelBadB Ψ b n N p) :
    failsTop Ψ b n N p ∨ ∃ ℓ ∈ (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ b ^ ℓ ≤ n),
        ∃ v ∈ Finset.range (b ^ ℓ), fails Ψ b n N ℓ v p := by
  rw [levelBadB] at h
  by_cases ht : failsTop Ψ b n N p
  · exact Or.inl ht
  · right
    rw [if_neg ht, zero_add, list_sum_range_map] at h
    obtain ⟨ℓ, hℓ, hpos⟩ := exists_pos_of_sum_pos h
    split_ifs at hpos with hc
    · rw [list_sum_range_map] at hpos
      obtain ⟨v, hv, hpos⟩ := exists_pos_of_sum_pos hpos
      split_ifs at hpos with hf
      · exact ⟨ℓ, Finset.mem_filter.2 ⟨hℓ, hc⟩, v, hv, hf⟩
      · exact absurd hpos (lt_irrefl 0)
    · exact absurd hpos (lt_irrefl 0)

theorem pass_of_levelBadB_zero {b n N : ℕ} (hb : 2 ≤ b) {p : List Bool} (h : levelBadB Ψ b n N p = 0) :
    ¬ failsTop Ψ b n N p ∧ ∀ ℓ, 1 ≤ ℓ → b ^ ℓ ≤ n → ∀ v, v < b ^ ℓ → ¬ fails Ψ b n N ℓ v p := by
  rw [levelBadB, Nat.add_eq_zero_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ht => by rw [if_pos ht] at h1; exact one_ne_zero h1, fun ℓ hℓ hℓn v hv hf => ?_⟩
  rw [list_sum_range_map, Finset.sum_eq_zero_iff] at h2
  have hℓle : ℓ ≤ n := (Nat.lt_pow_self (by omega : 1 < b)).le.trans hℓn
  have h3 := h2 ℓ (Finset.mem_range.2 (by omega))
  rw [if_pos ⟨hℓ, hℓn⟩, list_sum_range_map, Finset.sum_eq_zero_iff] at h3
  have h4 := h3 v (Finset.mem_range.2 hv)
  rw [if_pos hf] at h4
  exact one_ne_zero h4



end Level

theorem eta_le_b (A : List Bool → ℝ) {b n N D : ℕ} (hD : b ^ (N + 2 * n) ≤ 2 ^ D) (x : ℝ)
    (p : List Bool) (hax : A p ≤ x) (hxa : x ≤ A p + (1 / 2 : ℝ) ^ D) :
    (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1 := by
  have h0 : 0 ≤ x - A p := by linarith
  have hD' : (b : ℝ) ^ (N + 2 * n) ≤ 2 ^ D := by exact_mod_cast hD
  calc (x - A p) * (b : ℝ) ^ (N + 2 * n)
      ≤ (1 / 2 : ℝ) ^ D * 2 ^ D := by gcongr; linarith
    _ = 1 := by rw [← mul_pow]; norm_num

theorem b_pow_ge {b : ℕ} (hb : 2 ≤ b) (n : ℕ) (hn : 8 ≤ n) : 32 * n ≤ b ^ n :=
  (ComputableNormalB.two_pow_ge n hn).trans (Nat.pow_le_pow_left hb n)

theorem geom_b {b : ℕ} (hb : 1 ≤ b) (k : ℕ) : (b - 1) * ∑ i ∈ Finset.range k, b ^ i + 1 ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    have : (b - 1) * b ^ k + b ^ k = b ^ k * b := by
      rw [mul_comm (b ^ k) b]; zify [hb]; ring
    omega

theorem sum_blocks_le_b {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∑ ℓ ∈ (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ b ^ ℓ ≤ n), b ^ ℓ ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set L := Nat.log b n
  have hsub : (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ b ^ ℓ ≤ n) ⊆
      Finset.range (L + 1) := by
    intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_range] at hℓ ⊢
    have := Nat.le_log_of_pow_le (by omega) hℓ.2.2
    omega
  refine (Finset.sum_le_sum_of_subset hsub).trans ?_
  have h1 := geom_b (b := b) (by omega) (L + 1)
  have h2 : b ^ L ≤ n := Nat.pow_log_le_self b hn.ne'
  set S := ∑ i ∈ Finset.range (L + 1), b ^ i
  have h3 : (b - 1) * S ≤ (b - 1) * (2 * b ^ L) := by
    rw [pow_succ] at h1
    have : b ^ L * b ≤ (b - 1) * (2 * b ^ L) := by
      have : b ≤ 2 * (b - 1) := by omega
      calc b ^ L * b ≤ b ^ L * (2 * (b - 1)) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    omega
  have := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

/-- **Level mass.** -/
theorem level_bound_wb (Ψ : ℕ → ℕ → List Bool → ℕ) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {b n N D : ℕ} (hb : 2 ≤ b) (hn : 8 ≤ n) (hnN : n ≤ N)
    (hD : b ^ (N + 2 * n) ≤ 2 ^ D)
    (hsm1 : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤ κ * |(h : ℝ)| * N ^ 2 * Wv)
    (hsm2 : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
      κ * |(h : ℝ)| * ((N + n : ℕ) : ℝ) ^ 2 * Wv) :
    coins.real {ω | 0 < levelBadB Ψ b n N (pre ω D)} ≤
      74016 * (n : ℝ) ^ 3 * Real.sqrt (κ * Wv) * Zc := by
  set L := (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ b ^ ℓ ≤ n)
  set T0 : Set (ℕ → Bool) := {ω | (N : ℝ) <
    8 * n * visitCount (orbit b (G ω)) 0 (1 / (b : ℝ) ^ n) (N + n)}
  set T1 : Set (ℕ → Bool) := {ω | (N : ℝ) <
    8 * n * visitCount (orbit b (G ω)) (1 - 1 / (b : ℝ) ^ n) 1 (N + n)}
  set Dv : ℕ → ℕ → Set (ℕ → Bool) := fun ℓ v => {ω | 1 / (2 * (n : ℝ)) <
      |(visitCount (orbit b (G ω)) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) N : ℝ) /
        (N : ℝ) - 1 / (b : ℝ) ^ ℓ|}
  have hn1 : 1 ≤ n := by omega
  have hN1 : 1 ≤ N := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsub : {ω | 0 < levelBadB Ψ b n N (pre ω D)} ⊆
      (T0 ∪ T1) ∪ ⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (b ^ ℓ), Dv ℓ v := by
    intro ω hω
    have hcase := levelBadB_pos_cases Ψ hω
    have hax := (hAG ω D).1
    have hη := eta_le_b A hD (G ω) (pre ω D) hax (hAG ω D).2
    simp only [Set.mem_iUnion, Set.mem_union]
    by_cases ht : failsTop Ψ b n N (pre ω D)
    · left
      exact tail_of_failsTop Ψ A hΨ hb (G ω) (pre ω D) (hA0 _) hax hη ht
    · right
      rcases hcase with h | ⟨ℓ, hℓ, v, hv, hf⟩
      · exact absurd h ht
      have hℓ' := Finset.mem_filter.1 hℓ
      refine ⟨ℓ, hℓ, v, hv, ?_⟩
      exact dev_of_fails Ψ A hΨ hb hn1 hN1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ'.1)) (G ω)
        (pre ω D) (hA0 _) hax hη ht hf
  set X := Real.sqrt (κ * Wv) * Zc
  have hX : 0 ≤ X := mul_nonneg (Real.sqrt_nonneg _) Zc_nonneg
  have hbn : (32 * (n : ℝ)) ≤ (b : ℝ) ^ n := by exact_mod_cast b_pow_ge hb n hn
  have hP : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hsmall : 1 / (b : ℝ) ^ n ≤ 1 / (32 * (n : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hbn
  have hle1 : 1 / (b : ℝ) ^ n ≤ 1 := hsmall.trans (by
    rw [div_le_one (by positivity)]; linarith)
  have hT0 : coins.real T0 ≤ 36864 * (n : ℝ) ^ 2 * X := by
    have := tail_prob_wb G hGm b hκ hW hn1 hnN hsm2 0 (1 / (b : ℝ) ^ n) le_rfl (by positivity) hle1
      (by rw [sub_zero]; exact hsmall)
    simpa [T0, X, mul_assoc] using this
  have hT1 : coins.real T1 ≤ 36864 * (n : ℝ) ^ 2 * X := by
    have := tail_prob_wb G hGm b hκ hW hn1 hnN hsm2 (1 - 1 / (b : ℝ) ^ n) 1 (sub_nonneg.2 hle1)
      (by linarith [hP.le, one_div_pos.2 hP]) le_rfl (by rw [sub_sub_cancel]; exact hsmall)
    simpa [T1, X, mul_assoc] using this
  have hDv : ∀ ℓ ∈ L, ∀ v ∈ Finset.range (b ^ ℓ), coins.real (Dv ℓ v) ≤ 144 * (n : ℝ) ^ 2 * X := by
    intro ℓ hℓ v hv
    have := block_prob_wb G hGm hb hκ hW hN1 hsm1 hn1 (Finset.mem_filter.1 hℓ).2.1
      (Finset.mem_range.1 hv)
    simpa [Dv, X, mul_assoc] using this
  have hblocks : (∑ ℓ ∈ L, ((b ^ ℓ : ℕ) : ℝ)) ≤ 2 * n := by
    have := sum_blocks_le_b hb n
    exact_mod_cast this
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
  have h1 : coins.real (T0 ∪ T1) ≤ 2 * (36864 * (n : ℝ) ^ 2 * X) :=
    (measureReal_union_le _ _).trans (by linarith)
  have h2 : coins.real (⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (b ^ ℓ), Dv ℓ v) ≤
      2 * n * (144 * (n : ℝ) ^ 2 * X) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ ℓ ∈ L, coins.real (⋃ v ∈ Finset.range (b ^ ℓ), Dv ℓ v)
        ≤ ∑ ℓ ∈ L, ((b ^ ℓ : ℕ) : ℝ) * (144 * (n : ℝ) ^ 2 * X) := by
          refine Finset.sum_le_sum fun ℓ hℓ => (measureReal_biUnion_finset_le _ _).trans ?_
          calc ∑ v ∈ Finset.range (b ^ ℓ), coins.real (Dv ℓ v)
              ≤ ∑ v ∈ Finset.range (b ^ ℓ), 144 * (n : ℝ) ^ 2 * X :=
                Finset.sum_le_sum fun v hv => hDv ℓ hℓ v hv
            _ = _ := by simp
      _ = (∑ ℓ ∈ L, ((b ^ ℓ : ℕ) : ℝ)) * (144 * (n : ℝ) ^ 2 * X) := by rw [Finset.sum_mul]
      _ ≤ _ := by gcongr
  have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
  have : coins.real (T0 ∪ T1) + coins.real (⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (b ^ ℓ), Dv ℓ v) ≤
      73728 * (n : ℝ) ^ 3 * X + 288 * (n : ℝ) ^ 3 * X := by
    have e2 : 2 * n * (144 * (n : ℝ) ^ 2 * X) = 288 * (n : ℝ) ^ 3 * X := by ring
    nlinarith [mul_le_mul_of_nonneg_right hn2 hX]
  calc _ ≤ _ := this
    _ = 74016 * (n : ℝ) ^ 3 * Real.sqrt (κ * Wv) * Zc := by simp only [X]; ring


section Primrec

variable (Ψ : ℕ → ℕ → List Bool → ℕ)
  (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2)

include hΨp

variable {α : Type*} [Primcodable α]

attribute [local irreducible] fails failsTop in
theorem sprimrec_levelBadB {fb fn fN : α → ℕ} {fp : α → List Bool}
    (hb : Primrec fb) (hn : Primrec fn) (hN : Primrec fN) (hp : Primrec fp) :
    Primrec fun a => levelBadB Ψ (fb a) (fn a) (fN a) (fp a) := by
  have htop : Primrec fun a => if failsTop Ψ (fb a) (fn a) (fN a) (fp a) then 1 else 0 :=
    Primrec.ite (sprimrec_failsTop Ψ hΨp hb hn hN hp) (Primrec.const 1)
      (Primrec.const 0)
  have hin : Primrec fun y : α × ℕ =>
      ((List.range (fb y.1 ^ y.2)).map fun v =>
        if fails Ψ (fb y.1) (fn y.1) (fN y.1) y.2 v (fp y.1) then 1 else 0).sum := by
    have hfv : Primrec₂ fun (y : α × ℕ) (v : ℕ) =>
        if fails Ψ (fb y.1) (fn y.1) (fN y.1) y.2 v (fp y.1) then 1 else 0 :=
      (Primrec.ite (sprimrec_fails Ψ hΨp (hb.comp (Primrec.fst.comp Primrec.fst))
        (hn.comp (Primrec.fst.comp Primrec.fst)) (hN.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd
        (hp.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 1) (Primrec.const 0)).to₂
    exact primrec_sum_map (Primrec.list_range.comp
      (ComputableNormal.primrec_pow.comp (hb.comp Primrec.fst) Primrec.snd)) hfv
  have hcond : PrimrecPred fun y : α × ℕ => 1 ≤ y.2 ∧ fb y.1 ^ y.2 ≤ fn y.1 :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
      (Primrec.nat_le.comp (ComputableNormal.primrec_pow.comp (hb.comp Primrec.fst) Primrec.snd)
        (hn.comp Primrec.fst))
  have hg : Primrec₂ fun (a : α) (ℓ : ℕ) => if 1 ≤ ℓ ∧ fb a ^ ℓ ≤ fn a then
      ((List.range (fb a ^ ℓ)).map fun v =>
        if fails Ψ (fb a) (fn a) (fN a) ℓ v (fp a) then 1 else 0).sum else 0 :=
    (Primrec.ite hcond hin (Primrec.const 0)).to₂
  exact (Primrec.nat_add.comp htop
    (primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp hn)) hg)).of_eq
    fun a => rfl

end Primrec

/-! ## Assembly over a family of bases -/

open ComputableNormal (tsum_tail_le visitCount_mono_n primrec_pow)

theorem sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  rw [Real.sqrt_le_iff]; constructor <;> nlinarith

/-- The resolution bound used per base: `n³ √W ≤ (J+1)^{-2}` from `n⁶ W ≤ (J+1)^{-4}`. -/
theorem cube_sqrt_le {n : ℕ} {W : ℝ} {J : ℕ} (hW : 0 ≤ W)
    (h : (n : ℝ) ^ 6 * W ≤ 1 / ((J : ℝ) + 1) ^ 4) :
    (n : ℝ) ^ 3 * Real.sqrt W ≤ 1 / ((J : ℝ) + 1) ^ 2 := by
  have e1 : (n : ℝ) ^ 3 * Real.sqrt W = Real.sqrt ((n : ℝ) ^ 6 * W) := by
    rw [Real.sqrt_mul (by positivity), show (n : ℝ) ^ 6 = ((n : ℝ) ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (1 / ((J : ℝ) + 1) ^ 4) = 1 / ((J : ℝ) + 1) ^ 2 := by
    rw [show 1 / ((J : ℝ) + 1) ^ 4 = (1 / ((J : ℝ) + 1) ^ 2) ^ 2 by rw [div_pow, one_pow, ← pow_mul],
      Real.sqrt_sq (by positivity)]
  rw [e1, ← e2]; exact Real.sqrt_le_sqrt h

/-- Per-base level mass at reduced resolution `n' ≤ n / H`. -/
theorem mass_reduce {n n' H : ℕ} (hH : 1 ≤ H) (hnH : n' * H ≤ n) {W κ Z : ℝ} (hW : 0 ≤ W)
    (hκ : 0 ≤ κ) (hZ : 0 ≤ Z) {J b : ℕ}
    (hHge : 74016 * (κ + 1) * (Z + 1) * 2 ^ b ≤ (H : ℝ))
    (hev : (n : ℝ) ^ 6 * W ≤ 1 / ((J : ℝ) + 1) ^ 4) :
    74016 * (n' : ℝ) ^ 3 * Real.sqrt (κ * W) * Z ≤ (1 / 2 : ℝ) ^ b / ((J : ℝ) + 1) ^ 2 := by
  have hc := cube_sqrt_le hW hev
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hnH' : (n' : ℝ) * H ≤ n := by exact_mod_cast hnH
  have hsW := Real.sqrt_nonneg W
  have h1 : (n' : ℝ) ^ 3 * Real.sqrt W * H ≤ 1 / ((J : ℝ) + 1) ^ 2 := by
    have : (n' : ℝ) ^ 3 * H ≤ (n : ℝ) ^ 3 := by
      calc (n' : ℝ) ^ 3 * H ≤ (n' : ℝ) ^ 3 * H ^ 3 := by
            gcongr; exact le_self_pow₀ hHR (by norm_num)
        _ = ((n' : ℝ) * H) ^ 3 := by ring
        _ ≤ _ := by gcongr
    calc (n' : ℝ) ^ 3 * Real.sqrt W * H = ((n' : ℝ) ^ 3 * H) * Real.sqrt W := by ring
      _ ≤ (n : ℝ) ^ 3 * Real.sqrt W := by gcongr
      _ ≤ _ := hc
  have hsk := sqrt_le_add_one hκ
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hX : 0 ≤ (n' : ℝ) ^ 3 * Real.sqrt W := by positivity
  rw [Real.sqrt_mul hκ]
  have hstep : 74016 * (n' : ℝ) ^ 3 * (Real.sqrt κ * Real.sqrt W) * Z ≤
      74016 * (κ + 1) * (Z + 1) * ((n' : ℝ) ^ 3 * Real.sqrt W) := by
    have : Real.sqrt κ * Z ≤ (κ + 1) * (Z + 1) := by
      have := Real.sqrt_nonneg κ
      nlinarith
    nlinarith
  refine hstep.trans ?_
  rw [one_div_pow, div_div, le_div_iff₀ (by positivity)]
  have h3 : 74016 * (κ + 1) * (Z + 1) * ((n' : ℝ) ^ 3 * Real.sqrt W) * 2 ^ b ≤
      (n' : ℝ) ^ 3 * Real.sqrt W * H := by nlinarith
  have hJ : (0 : ℝ) < ((J : ℝ) + 1) ^ 2 := by positivity
  rw [le_div_iff₀ hJ] at h1
  calc 74016 * (κ + 1) * (Z + 1) * ((n' : ℝ) ^ 3 * Real.sqrt W) * (2 ^ b * ((J : ℝ) + 1) ^ 2)
      = (74016 * (κ + 1) * (Z + 1) * ((n' : ℝ) ^ 3 * Real.sqrt W) * 2 ^ b) * ((J : ℝ) + 1) ^ 2 := by ring
    _ ≤ ((n' : ℝ) ^ 3 * Real.sqrt W * H) * ((J : ℝ) + 1) ^ 2 := by gcongr
    _ ≤ 1 := h1

/-- **Family derandomization** (statement of
`CantorLiouvilleAll.exists_computable_normal_sched_family`). -/
theorem exists_computable_normal_sched_family' (Ψ : ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    (S : ℕ → Prop) [DecidablePred S] (hS : PrimrecPred S) (κ : ℕ → ℕ) (hκ : Primrec κ)
    (W : ℕ → ℝ) (hW0 : ∀ N, 0 ≤ W N) (hWa : Antitone W)
    (hsm : ∀ b, 2 ≤ b → S b → ∀ h : ℤ, h ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
        κ b * |(h : ℝ)| * N ^ 2 * W N)
    (Ns nr : ℕ → ℕ) (hNs : Primrec Ns) (hnr : Primrec nr) (hNtop : Tendsto Ns atTop atTop)
    (hrat : ∀ a : ℝ, 1 < a → ∀ᶠ j in atTop, (Ns (j + 1) : ℝ) ≤ a * Ns j)
    (hnrtop : Tendsto nr atTop atTop)
    (hev : ∀ᶠ j in atTop, 8 ≤ nr j ∧ nr j ≤ Ns j ∧
      (nr j : ℝ) ^ 6 * W (Ns j) ≤ 1 / ((j : ℝ) + 1) ^ 4)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧ (∀ b, 2 ≤ b → S b → IsNormal b (G e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hev
  obtain ⟨z, hz⟩ := exists_nat_ge Zc
  set B : ℝ := 3 with hBdef
  have hB0 : 0 < B := by norm_num
  set j₁ : ℕ := j₀ + 14 with hj₁def
  set H : ℕ → ℕ := fun b => 74016 * (κ b + 1) * (z + 1) * 2 ^ b with hHdef
  have hH1 : ∀ b, 1 ≤ H b := fun b => by
    simp only [hHdef]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hHp : Primrec H :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const _)
      (Primrec.succ.comp hκ)) (Primrec.const _)) (primrec_pow.comp (Primrec.const 2) Primrec.id)
  set res : ℕ → ℕ → ℕ := fun b J => nr J / H b with hresdef
  set D1 : ℕ → ℕ := fun J => (J + 1) * (Ns J + 2 * nr J) with hD1
  set act : ℕ → ℕ → Prop := fun J b => 2 ≤ b ∧ S b ∧ 8 ≤ res b J with hactdef
  have hactd : ∀ J b, Decidable (act J b) := fun J b => by simp only [hactdef]; infer_instance
  set cnt : ℕ → List Bool → ℕ := fun J p => ((List.range (J + 1)).map fun b =>
    if act J b then levelBadB Ψ b (res b J) (Ns J) (p.take (D1 J)) else 0).sum with hcnt
  set bad : ℕ → List Bool → Bool := fun j p =>
    decide (0 < cnt (j + j₁) p) || bad' (j + j₁) (p.take (d' (j + j₁))) with hbaddef
  set d : ℕ → ℕ := fun j => max (D1 (j + j₁)) (d' (j + j₁)) with hddef
  have hJ1 : Primrec fun j : ℕ => j + j₁ := Primrec.nat_add.comp Primrec.id (Primrec.const _)
  have hD1p : Primrec D1 := Primrec.nat_mul.comp Primrec.succ
    (Primrec.nat_add.comp hNs (Primrec.nat_mul.comp (Primrec.const 2) hnr))
  have hresp : Primrec₂ res := (Primrec.nat_div.comp (hnr.comp Primrec.snd) (hHp.comp Primrec.fst))
  have hcntp : Primrec₂ cnt := by
    have hact : PrimrecPred fun y : (ℕ × List Bool) × ℕ => act y.1.1 y.2 := by
      simp only [hactdef]
      exact PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 2) Primrec.snd)
        (PrimrecPred.and (hS.comp Primrec.snd)
          (Primrec.nat_le.comp (Primrec.const 8) (hresp.comp Primrec.snd (Primrec.fst.comp Primrec.fst))))
    have hlev : Primrec fun y : (ℕ × List Bool) × ℕ =>
        levelBadB Ψ y.2 (res y.2 y.1.1) (Ns y.1.1) (y.1.2.take (D1 y.1.1)) :=
      sprimrec_levelBadB Ψ hΨp Primrec.snd (hresp.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
        (hNs.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_take.comp (hD1p.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
    have hf : Primrec₂ fun (x : ℕ × List Bool) (b : ℕ) =>
        if act x.1 b then levelBadB Ψ b (res b x.1) (Ns x.1) (x.2.take (D1 x.1)) else 0 :=
      (Primrec.ite hact hlev (Primrec.const 0)).to₂
    exact (primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) hf).to₂
  have hbad : Primrec₂ bad := by
    have h1 : PrimrecPred fun x : ℕ × List Bool => 0 < cnt (x.1 + j₁) x.2 :=
      Primrec.nat_lt.comp (Primrec.const 0) (hcntp.comp (hJ1.comp Primrec.fst) Primrec.snd)
    have h2 : Primrec fun x : ℕ × List Bool => bad' (x.1 + j₁) (x.2.take (d' (x.1 + j₁))) :=
      hbad'.comp (hJ1.comp Primrec.fst)
        (Primrec.list_take.comp (hd'.comp (hJ1.comp Primrec.fst)) Primrec.snd)
    exact (Primrec.or.comp h1.decide h2).to₂
  have hd : Primrec d := Primrec.nat_max.comp (hD1p.comp hJ1) (hd'.comp hJ1)
  -- unfolding the count on a prefix
  have hcnt_pre : ∀ J ω D, D1 J ≤ D → cnt J (pre ω D) = ((List.range (J + 1)).map fun b =>
      if act J b then levelBadB Ψ b (res b J) (Ns J) (pre ω (D1 J)) else 0).sum := by
    intro J ω D hD
    simp only [hcnt, pre_take' ω hD]
  have hdj : ∀ j, dens bad d j [] ≤ B / ((j : ℝ) + ((j₁ + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j
    set J := j + j₁ with hJ
    obtain ⟨hn8, hnN, hW6⟩ := hj₀ J (by omega)
    rw [dens_eq_real]
    set Lv : ℕ → Set (ℕ → Bool) := fun b =>
      if act J b then {ω | 0 < levelBadB Ψ b (res b J) (Ns J) (pre ω (D1 J))} else ∅ with hLv
    have hsub : {ω | bad j (pre ω (d j)) = true} ⊆
        (⋃ b ∈ Finset.range (J + 1), Lv b) ∪ {ω | bad' J (pre ω (d' J)) = true} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, hbaddef, Bool.or_eq_true, decide_eq_true_eq] at hω
      rw [pre_take' ω (le_max_right _ _), hcnt_pre J ω _ (le_max_left _ _)] at hω
      rcases hω with h | h
      · left
        rw [list_sum_range_map] at h
        obtain ⟨b, hb, hpos⟩ := exists_pos_of_sum_pos h
        simp only [Set.mem_iUnion]
        refine ⟨b, hb, ?_⟩
        simp only [hLv]
        split_ifs at hpos ⊢ with ha
        · exact hpos
        · exact absurd hpos (lt_irrefl 0)
      · right; exact h
    have hN1 : 1 ≤ Ns J := by omega
    have hW := hW0 (Ns J)
    have hJ0 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    have hLb : ∀ b ∈ Finset.range (J + 1), coins.real (Lv b) ≤ (1 / 2 : ℝ) ^ b / ((J : ℝ) + 1) ^ 2 := by
      intro b hb
      simp only [hLv]
      split_ifs with ha
      · obtain ⟨hb2, hSb, h8⟩ := ha
        have hresN : res b J ≤ Ns J := (Nat.div_le_self _ _).trans hnN
        have hbJ : b ≤ J + 1 := by have := Finset.mem_range.1 hb; omega
        have hD : b ^ (Ns J + 2 * res b J) ≤ 2 ^ D1 J := by
          calc b ^ (Ns J + 2 * res b J) ≤ (2 ^ b) ^ (Ns J + 2 * res b J) :=
                Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
            _ = 2 ^ (b * (Ns J + 2 * res b J)) := by rw [← pow_mul]
            _ ≤ 2 ^ D1 J := Nat.pow_le_pow_right (by norm_num) (by
                simp only [hD1]
                exact Nat.mul_le_mul hbJ (by
                  have : res b J ≤ nr J := Nat.div_le_self _ _
                  omega))
        have hκ0 : (0 : ℝ) ≤ κ b := by positivity
        have hL := level_bound_wb Ψ A hΨ hA0 G hGm hAG hκ0 hW hb2 h8 hresN hD
          (fun h hh => hsm b hb2 hSb h hh _ hN1)
          (fun h hh => (hsm b hb2 hSb h hh _ (by omega)).trans (by
            have : 0 ≤ (κ b : ℝ) * |(h : ℝ)| * ((Ns J + res b J : ℕ) : ℝ) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left (hWa (by omega)) this))
        refine hL.trans ?_
        refine mass_reduce (hH1 b) (Nat.div_mul_le_self _ _) hW hκ0 Zc_nonneg ?_ hW6
        simp only [hHdef]; push_cast
        have : Zc + 1 ≤ (z : ℝ) + 1 := by linarith
        gcongr
      · simp only [measureReal_empty]; positivity
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans ?_)
    have hU : coins.real (⋃ b ∈ Finset.range (J + 1), Lv b) ≤ 2 / ((J : ℝ) + 1) ^ 2 := by
      refine (measureReal_biUnion_finset_le _ _).trans ((Finset.sum_le_sum hLb).trans ?_)
      rw [← Finset.sum_div]
      gcongr
      have := sum_geometric_two_le (J + 1)
      simpa [one_div] using this
    have hm := hmass J
    have hJR : ((j : ℝ) + ((j₁ + 1 : ℕ) : ℝ)) = (J : ℝ) + 1 := by rw [hJ]; push_cast; ring
    rw [hJR]
    calc _ ≤ 2 / ((J : ℝ) + 1) ^ 2 + 1 / ((J : ℝ) + 1) ^ 2 := add_le_add hU hm
      _ = B / ((J : ℝ) + 1) ^ 2 := by rw [hBdef]; ring
  have hnn : ∀ j, 0 ≤ dens bad d j [] := fun j => dens_nonneg j []
  obtain ⟨hs0, ht0⟩ := tsum_tail_le _ hnn B hB0.le 0 (j₁ + 1) (by omega) (fun j _ => hdj j)
  simp only [zero_le, if_true, Nat.cast_zero, zero_add] at hs0 ht0
  have hj₁pos : (0 : ℝ) < j₁ := by have : 0 < j₁ := by omega
                                   exact_mod_cast this
  have hj₁B : 4 * B ≤ (j₁ : ℝ) := by
    rw [hj₁def, hBdef]; push_cast; have : (0 : ℝ) ≤ j₀ := by positivity
    linarith
  have htot : ∑' j, dens bad d j [] ≤ 1 / 4 := by
    refine ht0.trans ?_
    push_cast
    rw [show (j₁ : ℝ) + 1 - 1 = j₁ by ring, div_le_div_iff₀ hj₁pos (by norm_num)]
    linarith
  set c : ℕ := ⌈B⌉₊ + 1 with hcdef
  have hcB : B ≤ (c : ℝ) := by rw [hcdef]; push_cast; linarith [Nat.le_ceil B]
  set Jk : ℕ → ℕ := fun k => c * 8 ^ (k + 1) with hJdef
  have hJp : Primrec Jk :=
    Primrec.nat_mul.comp (Primrec.const _) (primrec_pow.comp (Primrec.const 8) Primrec.succ)
  have htail : ∀ k, ∑' j, (if Jk k < j then dens bad d j [] else 0) ≤ (1 / 8 : ℝ) ^ (k + 1) := by
    intro k
    obtain ⟨_, ht⟩ := tsum_tail_le _ hnn B hB0.le (Jk k + 1) (j₁ + 1) (by omega) (fun j _ => hdj j)
    have e : (fun j => if Jk k < j then dens bad d j [] else 0) =
        fun j => if Jk k + 1 ≤ j then dens bad d j [] else 0 := by
      funext j; simp only [Nat.lt_iff_add_one_le]
    rw [e]
    refine ht.trans ?_
    have h8 : (0 : ℝ) < 8 ^ (k + 1) := by positivity
    have hJR : ((Jk k : ℕ) : ℝ) = c * 8 ^ (k + 1) := by simp [hJdef]
    have hden : (0 : ℝ) < ((Jk k + 1 : ℕ) : ℝ) + ((j₁ + 1 : ℕ) : ℝ) - 1 := by
      push_cast; rw [hJR]
      have : (0 : ℝ) ≤ c * 8 ^ (k + 1) := by positivity
      linarith
    rw [div_pow, one_pow, div_le_div_iff₀ hden h8]
    push_cast; rw [hJR]
    have : (1 : ℝ) ≤ 8 ^ (k + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨e, hce, hav⟩ := exists_primrec_avoid bad hbad d hd Jk hJp hs0 htot htail
  have hpass : ∀ J', j₁ ≤ J' → cnt J' (pre e (D1 J')) = 0 ∧
      bad' J' (pre e (d' J')) = false := by
    intro J' hJ'
    have h := hav (J' - j₁)
    simp only [hbaddef, hddef, Nat.sub_add_cancel hJ', Bool.or_eq_false_iff,
      decide_eq_false_iff_not, not_lt, Nat.le_zero] at h
    rw [pre_take' e (le_max_right _ _), hcnt_pre J' e _ (le_max_left _ _)] at h
    rw [hcnt_pre J' e _ le_rfl]
    exact h
  refine ⟨e, hce, ?_, j₁, fun j hj => (hpass j hj).2⟩
  intro b hb hSb
  have hrestop : Tendsto (fun J => res b J) atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hnrtop.eventually_ge_atTop (M * H b)] with J hJ
    exact (Nat.le_div_iff_mul_le (hH1 b)).2 hJ
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_badic b hb _ fun ℓ hℓ v hv => ?_
  refine tendsto_div_of_monotone_of_exists_subseq_tendsto_div _ _
    (fun m n h => by exact_mod_cast visitCount_mono_n _ _ _ h) fun a ha =>
      ⟨Ns, hrat a ha, hNtop, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_one_div_atTop_nhds_zero_nat.comp hrestop)
  filter_upwards [eventually_ge_atTop (max (max j₀ j₁) b),
    hrestop.eventually_ge_atTop (max 8 (b ^ ℓ))] with J' hJ' hℓn
  obtain ⟨hn8, hnN, -⟩ := hj₀ J' (by omega)
  obtain ⟨hcnt0, -⟩ := hpass J' (by omega)
  have hact : act J' b := ⟨hb, hSb, by omega⟩
  have hlev : levelBadB Ψ b (res b J') (Ns J') (pre e (D1 J')) = 0 := by
    simp only [hcnt] at hcnt0
    rw [pre_take' e le_rfl, list_sum_range_map, Finset.sum_eq_zero_iff] at hcnt0
    have := hcnt0 b (Finset.mem_range.2 (by omega))
    rwa [if_pos hact] at this
  obtain ⟨htop, hp⟩ := pass_of_levelBadB_zero Ψ hb hlev
  have hℓle : ℓ ≤ res b J' := (Nat.lt_pow_self (by omega : 1 < b)).le.trans (by omega)
  have hresN : res b J' ≤ Ns J' := (Nat.div_le_self _ _).trans hnN
  have hD : b ^ (Ns J' + 2 * res b J') ≤ 2 ^ D1 J' := by
    calc b ^ (Ns J' + 2 * res b J') ≤ (2 ^ b) ^ (Ns J' + 2 * res b J') :=
          Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
      _ = 2 ^ (b * (Ns J' + 2 * res b J')) := by rw [← pow_mul]
      _ ≤ 2 ^ D1 J' := Nat.pow_le_pow_right (by norm_num) (by
          simp only [hD1]
          exact Nat.mul_le_mul (by omega) (by
            have : res b J' ≤ nr J' := Nat.div_le_self _ _
            omega))
  have hax := (hAG e (D1 J')).1
  simp only [Real.norm_eq_abs, abs_abs, Function.comp]
  exact good_of_pass Ψ A hΨ hb (by omega) (by omega) hℓle (G e) _ (hA0 _) hax
    (eta_le_b A hD (G e) _ hax (hAG e _).2) htop (hp ℓ hℓ (by omega) v hv)

end NormalNumbers.SchedFamily
