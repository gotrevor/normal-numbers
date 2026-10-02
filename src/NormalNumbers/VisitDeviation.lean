/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HatFourier
import NormalNumbers.DecayAeNormal

/-!
# Quantitative visit-count deviation under polynomial Fourier decay

For a random real `G` with `‖𝔼 e(ξG)‖ ≤ C|ξ|^{-δ}`, the doubling orbit of `G` visits an arc
`[a, c)` with frequency within `2ρ + t` of `c − a`, except on probability
`≤ 2 (tρ)⁻¹ √((1 + K)/N)` (`visit_deviation`).

Route: sandwich the indicator between `trapLo ≤ 1_{[a,c)} ≤ trapUp` (plateaus, `HatFourier`),
expand plateau averages in Fourier modes (`mean_sub_coeff_le`), bound the Weyl means in
`L¹` by `second_moment_le` and Cauchy–Schwarz, then Markov.
-/

open MeasureTheory Filter Topology Complex

namespace NormalNumbers.VisitDeviation

open DecayAeNormal

theorem fourier_coe_eq_ee (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (1 : ℝ)) = ee (n * x) := by
  rw [fourier_coe_apply, ee]
  congr 1; push_cast; ring

/-- **Fourier expansion of an orbit average**, minus its mean. -/
theorem mean_sub_coeff_le (f : C(AddCircle (1 : ℝ), ℂ)) (B : ℤ → ℝ) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n, n ≠ 0 → ‖fourierCoeff f n‖ ≤ B n) (hBs : Summable B)
    (u : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ k ∈ Finset.range N, f (u k : AddCircle (1 : ℝ))) / N - fourierCoeff f 0‖ ≤
      ∑' n, (if n = 0 then 0 else B n * ‖(∑ k ∈ Finset.range N, ee (n * u k)) / N‖) := by
  classical
  -- summability of the coefficients
  have hcs : Summable (fourierCoeff f) := by
    refine Summable.of_norm_bounded (g := fun n => if n = 0 then ‖fourierCoeff f 0‖ else B n)
      ?_ fun n => ?_
    · refine (hBs.add (summable_of_ne_finset_zero (s := {0})
        (f := fun n : ℤ => if n = 0 then ‖fourierCoeff f 0‖ else 0) ?_)).of_nonneg_of_le
        (fun n => by split_ifs <;> simp [hB0]) (fun n => ?_)
      · intro n hn; simp at hn; simp [hn]
      · split_ifs with h
        · subst h; simp [hB0]
        · simp
    · split_ifs with h
      · subst h; rfl
      · exact hB n h
  set A : ℤ → ℂ := fun n => (∑ k ∈ Finset.range N, ee (n * u k)) / N with hA
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  -- the mean as a tsum
  have hmean : HasSum (fun n => fourierCoeff f n * A n)
      ((∑ k ∈ Finset.range N, f (u k : AddCircle (1 : ℝ))) / N) := by
    have hk : ∀ k, HasSum (fun n => fourierCoeff f n * ee (n * u k)) (f (u k)) := by
      intro k
      have := has_pointwise_sum_fourier_series_of_summable hcs (u k : AddCircle (1 : ℝ))
      simp only [smul_eq_mul, fourier_coe_eq_ee] at this
      exact this
    have hsum := hasSum_sum (s := Finset.range N) fun k _ => hk k
    have := hsum.div_const (N : ℂ)
    refine this.congr_fun fun n => ?_
    simp only [hA]
    rw [← Finset.mul_sum, mul_div_assoc]
  have hA0 : A 0 = 1 := by
    simp only [hA, Int.cast_zero, zero_mul]
    simp [ee, hNc]
  rw [← hmean.tsum_eq, hmean.summable.tsum_eq_add_tsum_ite 0, hA0, mul_one, add_sub_cancel_left]
  have hnormA : ∀ n, ‖A n‖ ≤ 1 := by
    intro n
    simp only [hA]
    rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast (by omega : 0 < N))]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_ee]
  have hsumB : Summable fun n => if n = 0 then (0 : ℝ) else B n * ‖A n‖ :=
    hBs.of_nonneg_of_le (fun n => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hB0 n) (norm_nonneg _))
      (fun n => by
        split_ifs
        · exact hB0 n
        · exact mul_le_of_le_one_right (hB0 n) (hnormA n))
  have hle : ∀ n, ‖(if n = 0 then (0 : ℂ) else fourierCoeff f n * A n)‖ ≤
      (if n = 0 then (0 : ℝ) else B n * ‖A n‖) := by
    intro n
    split_ifs with h
    · simp
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB n h) (norm_nonneg _)
  have hsn : Summable fun n => ‖(if n = 0 then (0 : ℂ) else fourierCoeff f n * A n)‖ :=
    hsumB.of_nonneg_of_le (fun n => norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hle hsumB)


/-- `𝔼 g ≤ √(𝔼 g²)` for bounded measurable `g ≥ 0` on a probability space. -/
theorem integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : Measurable g) (M : ℝ) (hgM : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω ∂μ ≤ Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable M
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgM ω)
  have hi2 : Integrable (fun ω => g ω ^ 2) μ := Integrable.of_bound
    (hg.pow_const 2).aestronglyMeasurable (M ^ 2)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgM ω) 2)
  set m := ∫ ω, g ω ∂μ
  have hvar : 0 ≤ ∫ ω, (g ω - m) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hexp : ∫ ω, (g ω - m) ^ 2 ∂μ = ∫ ω, g ω ^ 2 ∂μ - m ^ 2 := by
    have : (fun ω => (g ω - m) ^ 2) = fun ω => g ω ^ 2 + (-(2 * m) * g ω + m ^ 2) := by
      funext ω; ring
    have h3 : Integrable (fun ω => -(2 * m) * g ω + m ^ 2) μ :=
      (hi.const_mul _).add (integrable_const _)
    rw [this, integral_add hi2 h3, integral_add (hi.const_mul _) (integrable_const _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hexp] at hvar
  calc m ≤ |m| := le_abs_self m
    _ = Real.sqrt (m ^ 2) := (Real.sqrt_sq_eq_abs m).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

/-- **Probabilistic deviation of an orbit average** of a test function with summable
Fourier coefficient majorant `B`. -/
theorem prob_mean_dev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (f : C(AddCircle (1 : ℝ), ℂ)) (B : ℤ → ℝ) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n, n ≠ 0 → ‖fourierCoeff f n‖ ≤ B n) (hBs : Summable B)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < ‖(∑ k ∈ Finset.range N, f ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff f 0‖} ≤
      (∑' n, B n) / t *
        Real.sqrt ((N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2) / (N : ℝ) ^ 2) := by
  set K := C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2
  set r := Real.sqrt ((N + K) / (N : ℝ) ^ 2)
  set A : ℤ → Ω → ℂ := fun n ω => (∑ k ∈ Finset.range N, ee (n * (2 ^ k * G ω))) / N
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
  have hle : ∀ ω, ‖(∑ k ∈ Finset.range N, f ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
      fourierCoeff f 0‖ ≤ X ω := fun ω =>
    mean_sub_coeff_le f B hB0 hB hBs (fun k => 2 ^ k * G ω) N hN
  -- integrals of the Weyl means
  have hAint : ∀ n, n ≠ 0 → ∫ ω, ‖A n ω‖ ∂μ ≤ r := by
    intro n hn
    have hsm := second_moment_le μ G hG hC hδ hdec n hn N
    refine (integral_le_sqrt_integral_sq μ _ (hAm n).norm 1
      (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hAb n ω)).trans ?_
    refine Real.sqrt_le_sqrt ?_
    have hpt : ∀ ω, ‖A n ω‖ ^ 2 =
        ‖∑ k ∈ Finset.range N, ee (n * 2 ^ k * G ω)‖ ^ 2 / (N : ℝ) ^ 2 := by
      intro ω
      simp only [A]
      rw [norm_div, Complex.norm_natCast, div_pow]
      congr 3
      refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc]
    simp_rw [hpt]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hsm (by positivity)
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
  have hEX : ∫ ω, X ω ∂μ ≤ (∑' n, B n) * r := by
    rw [hXint_eq, ← tsum_mul_right]
    refine (hsumI.of_nonneg_of_le (fun n => ?_) (fun n => ?_)).tsum_le_tsum (fun n => ?_)
      (hBs.mul_right r)
    · split_ifs
      · simp
      · exact integral_nonneg fun ω => mul_nonneg (hB0 n) (norm_nonneg _)
    · exact (integral_mono_of_nonneg (Eventually.of_forall fun ω => by
        split_ifs; exact le_rfl; exact mul_nonneg (hB0 n) (norm_nonneg _))
        (hFint n).norm (Eventually.of_forall fun ω => le_abs_self _))
    · split_ifs with h
      · simp only [integral_const, smul_zero]
        exact mul_nonneg (hB0 n) (Real.sqrt_nonneg _)
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hAint n h) (hB0 n)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Eventually.of_forall hX0) hXi t
  calc μ.real {ω | t < ‖(∑ k ∈ Finset.range N,
        f ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N - fourierCoeff f 0‖}
      ≤ μ.real {ω | t ≤ X ω} := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        exact (le_of_lt hω).trans (hle ω)
    _ ≤ (∫ ω, X ω ∂μ) / t := by rw [le_div_iff₀ ht, mul_comm]; exact hmarkov
    _ ≤ (∑' n, B n) * r / t := by gcongr
    _ = _ := by ring


/-- `Σ_{n ∈ ℤ} 1/n² = π²/3` (the `n = 0` term is `1/0 = 0`). -/
theorem hasSum_inv_sq_int : HasSum (fun n : ℤ => 1 / ((n : ℝ)) ^ 2) (Real.pi ^ 2 / 3) := by
  have h1 : HasSum (fun n : ℕ => 1 / (((n : ℤ) : ℝ)) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa only [Int.cast_natCast] using hasSum_zeta_two
  have h2' : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero] at this
    refine this.congr_fun fun n => ?_
    push_cast; ring
  have h2 : HasSum (fun n : ℕ => 1 / (((-(n + 1 : ℤ)) : ℤ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    refine h2'.congr_fun fun n => ?_
    simp only [Int.cast_neg, neg_sq]; push_cast; ring
  have := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => 1 / (n : ℝ) ^ 2) h1 h2
  rw [show Real.pi ^ 2 / 3 = Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 by ring]
  exact this

/-- Plateau Fourier majorant. -/
noncomputable def plB (ρ : ℝ) (n : ℤ) : ℝ := 2 / ρ * (1 / (Real.pi ^ 2 * (n : ℝ) ^ 2))

theorem hasSum_plB (ρ : ℝ) (hρ : 0 < ρ) : HasSum (plB ρ) (2 / (3 * ρ)) := by
  have h := hasSum_inv_sq_int.mul_left (2 / ρ / Real.pi ^ 2)
  have hf : plB ρ = fun n : ℤ => 2 / ρ / Real.pi ^ 2 * (1 / (n : ℝ) ^ 2) := by
    funext n; unfold plB
    rw [one_div, one_div, mul_inv]; ring
  have hv : 2 / (3 * ρ) = 2 / ρ / Real.pi ^ 2 * (Real.pi ^ 2 / 3) := by
    have := Real.pi_pos.ne'; field_simp
  rw [hf, hv]; exact h

theorem plateau_coe_trapUp (a c ρ : ℝ) (y : AddCircle (1 : ℝ)) :
    HatFourier.plateau ((c - a) / 2 + ρ) ρ ((a + c) / 2) y = ((trapUp a c ρ y : ℝ) : ℂ) := rfl

theorem plateau_coe_trapLo (a c ρ : ℝ) (y : AddCircle (1 : ℝ)) :
    HatFourier.plateau ((c - a) / 2) ρ ((a + c) / 2) y = ((trapLo a c ρ y : ℝ) : ℂ) := rfl

theorem coeff_zero_real (g : C(AddCircle (1 : ℝ), ℝ)) (f : C(AddCircle (1 : ℝ), ℂ))
    (hfg : ∀ y, f y = ((g y : ℝ) : ℂ)) :
    fourierCoeff f 0 = ((∫ x in (0 : ℝ)..1, g ((x : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral _ 0 0, ← intervalIntegral.integral_ofReal]
  simp only [neg_zero, fourier_zero, one_smul, zero_add, div_one]
  exact intervalIntegral.integral_congr fun x _ => hfg x

/-- **Visit-count deviation under polynomial decay.** -/
theorem visit_deviation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (a c ρ t : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hlen : c - a ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (ht : 0 < t) (N : ℕ) (hN : 1 ≤ N) :
    μ.real {ω | 2 * ρ + t < |(visitCount (orbit 2 (G ω)) a c N : ℝ) / N - (c - a)|} ≤
      2 * (2 / (3 * ρ) / t *
        Real.sqrt ((N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2) / (N : ℝ) ^ 2)) := by
  set fU := HatFourier.plateau ((c - a) / 2 + ρ) ρ ((a + c) / 2)
  set fL := HatFourier.plateau ((c - a) / 2) ρ ((a + c) / 2)
  have hBU : ∀ n, n ≠ 0 → ‖fourierCoeff fU n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hBL : ∀ n, n ≠ 0 → ‖fourierCoeff fL n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hB0 : ∀ n, 0 ≤ plB ρ n := fun n => by unfold plB; positivity
  have hdU := prob_mean_dev μ G hG hC hδ hdec fU (plB ρ) hB0 hBU (hasSum_plB ρ hρ).summable N hN t ht
  have hdL := prob_mean_dev μ G hG hC hδ hdec fL (plB ρ) hB0 hBL (hasSum_plB ρ hρ).summable N hN t ht
  rw [(hasSum_plB ρ hρ).tsum_eq] at hdU hdL
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hIU := integral_trapUp_le a c ρ ha hac hc hρ
  have hIL := le_integral_trapLo a c ρ ha hac hc hρ
  have hcU : fourierCoeff fU 0 = ((∫ x in (0 : ℝ)..1, trapUp a c ρ ((x : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) :=
    coeff_zero_real _ _ (plateau_coe_trapUp a c ρ)
  have hcL : fourierCoeff fL 0 = ((∫ x in (0 : ℝ)..1, trapLo a c ρ ((x : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) :=
    coeff_zero_real _ _ (plateau_coe_trapLo a c ρ)
  have hsub : {ω | 2 * ρ + t < |(visitCount (orbit 2 (G ω)) a c N : ℝ) / N - (c - a)|} ⊆
      {ω | t < ‖(∑ k ∈ Finset.range N, fU ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fU 0‖} ∪
      {ω | t < ‖(∑ k ∈ Finset.range N, fL ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fL 0‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    set u := orbit 2 (G ω)
    have hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1 := fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hcoe : ∀ k, ((u k : ℝ) : AddCircle (1 : ℝ)) = ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ)) := by
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
    have heU : (∑ k ∈ Finset.range N, fU ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff fU 0 = ((SU / N - IU : ℝ) : ℂ) := by
      rw [hcU]; simp only [SU, ← hcoe, plateau_coe_trapUp, fU]; push_cast; rfl
    have heL : (∑ k ∈ Finset.range N, fL ((2 ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
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

end NormalNumbers.VisitDeviation
