/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VisitDeviation

/-!
# Visit-count deviation in every base `b ≥ 2`, with a base-uniform constant

Base-`b` copies of `DecayAeNormal.second_moment_le`, `VisitDeviation.prob_mean_dev` and
`VisitDeviation.visit_deviation`.  The lacunary separation `bⁿ − bᵐ ≥ b^{(n+m)/2}/2` gives the
second-moment constant `C 2^δ (1 − b^{-δ/2})^{-2}`, which is bounded by the base-2 constant
`C 2^δ (1 − 2^{-δ/2})^{-2}`; so every bound here is the base-2 bound, uniformly in `b`.
-/

open MeasureTheory Filter Topology Complex

namespace NormalNumbers.VisitDeviationB

open DecayAeNormal VisitDeviation

/-- Lacunary separation in base `b`: `bⁿ − bᵐ ≥ b^{(n+m)/2}/2` for `m < n`. -/
theorem b_pow_sub_ge (b : ℕ) (hb : 2 ≤ b) {m n : ℕ} (hmn : m < n) :
    (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 ≤ (b : ℝ) ^ n - (b : ℝ) ^ m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) ≤ (b : ℝ) ^ (n : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
    push_cast; linarith
  rw [Real.rpow_natCast] at h1
  have h3 : (b : ℝ) ^ m * 2 ≤ (b : ℝ) ^ n := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [pow_add, pow_add, pow_one]
    have : (1 : ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ (by linarith)
    have : (0 : ℝ) < (b : ℝ) ^ m := by positivity
    have h2 : (2 : ℝ) ≤ (b : ℝ) ^ d * b := by nlinarith
    calc (b : ℝ) ^ m * 2 ≤ (b : ℝ) ^ m * ((b : ℝ) ^ d * b) := by gcongr
      _ = _ := by ring
  linarith

/-- The decay bound at a lacunary difference frequency, base `b`. -/
theorem decay_at_diff_b (b : ℕ) (hb : 2 ≤ b) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (h : ℤ)
    (hh : h ≠ 0) {m n : ℕ} (hmn : m ≠ n) :
    C * |(h : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m)| ^ (-δ) ≤
      C * 2 ^ δ * ((b : ℝ) ^ (-δ / 2)) ^ n * ((b : ℝ) ^ (-δ / 2)) ^ m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hsep : (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 ≤ |(h : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m)| := by
    have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
    have hd : (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 ≤ |(b : ℝ) ^ n - (b : ℝ) ^ m| := by
      rcases lt_or_gt_of_ne hmn with hlt | hlt
      · exact (b_pow_sub_ge b hb hlt).trans (le_abs_self _)
      · have := b_pow_sub_ge b hb hlt
        rw [add_comm m n] at this
        rw [abs_sub_comm]; exact this.trans (le_abs_self _)
    rw [abs_mul]
    nlinarith [abs_nonneg ((b : ℝ) ^ n - (b : ℝ) ^ m)]
  have hpos : (0 : ℝ) < (b : ℝ) ^ (((n + m : ℕ) : ℝ) / 2) / 2 := by positivity
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hsep (by linarith : -δ ≤ 0)
  rw [mul_assoc C, mul_assoc C]
  refine mul_le_mul_of_nonneg_left (hmono.trans (le_of_eq ?_)) hC.le
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm, mul_assoc,
    ← Real.rpow_add hb0]
  congr 2
  push_cast; ring

/-- **Second moment of the Weyl sum** under polynomial decay. -/
theorem second_moment_le_b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : ℕ) (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (h : ℤ) (hh : h ≠ 0) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤
      N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 := by
  set s : ℝ := (b : ℝ) ^ (-δ / 2) with hs
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos (by linarith) _).le
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * G ω)) μ := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  -- expand
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * G ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  -- termwise bound
  have hterm : ∀ n m : ℕ, ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * G ω) ∂μ‖ ≤
      (if n = m then 1 else 0) + C * 2 ^ δ * s ^ n * s ^ m := by
    intro n m
    have hK : 0 ≤ C * 2 ^ δ * s ^ n * s ^ m := by positivity
    split_ifs with hnm
    · refine (norm_integral_le_of_norm_le_const (C := 1)
        (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
      simp; linarith
    · have hne : (h : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m) ≠ 0 := by
        refine mul_ne_zero (by exact_mod_cast hh) (sub_ne_zero.2 fun he => hnm ?_)
        exact Nat.pow_right_injective hb (by exact_mod_cast he)
      have := decay_at_diff_b b hb hC hδ h hh (Ne.symm hnm)
      rw [zero_add]
      exact (hdec _ hne).trans this
  have hgeo : ∑ n ∈ Finset.range N, s ^ n ≤ (1 - s)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hs0 hs1]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_geometric_of_lt_one hs0 hs1)
  have hreal : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((if n = m then 1 else 0) + C * 2 ^ δ * s ^ n * s ^ m) := by
    have := congrArg Complex.re hI
    rw [Complex.ofReal_re] at this
    rw [this]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun m _ => hterm n m
  have hsum : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((if n = m then (1 : ℝ) else 0) + C * 2 ^ δ * s ^ n * s ^ m)
      = N + C * 2 ^ δ * (∑ n ∈ Finset.range N, s ^ n) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range]
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    simp
    rw [Finset.filter_true_of_mem (fun x hx => Finset.mem_range.1 hx), Finset.card_range]
    congr 1
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hsum] at hreal
  refine hreal.trans ?_
  have : 0 ≤ ∑ n ∈ Finset.range N, s ^ n := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : (2 : ℝ) ^ (-δ / 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs2 : s ≤ (2 : ℝ) ^ (-δ / 2) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbR (by linarith)
  have hinv : (1 - s)⁻¹ ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h1 : ∑ n ∈ Finset.range N, s ^ n ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ := hgeo.trans hinv
  gcongr

/-- **Probabilistic deviation of an orbit average** of a test function with summable
Fourier coefficient majorant `B`. -/
theorem prob_mean_dev_b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : ℕ) (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (f : C(AddCircle (1 : ℝ), ℂ)) (B : ℤ → ℝ) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n, n ≠ 0 → ‖fourierCoeff f n‖ ≤ B n) (hBs : Summable B)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < ‖(∑ k ∈ Finset.range N, f (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N -
        fourierCoeff f 0‖} ≤
      (∑' n, B n) / t *
        Real.sqrt ((N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2) / (N : ℝ) ^ 2) := by
  set K := C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2
  set r := Real.sqrt ((N + K) / (N : ℝ) ^ 2)
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
  have hAint : ∀ n, n ≠ 0 → ∫ ω, ‖A n ω‖ ∂μ ≤ r := by
    intro n hn
    have hsm := second_moment_le_b μ b hb G hG hC hδ hdec n hn N
    refine (integral_le_sqrt_integral_sq μ _ (hAm n).norm 1
      (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hAb n ω)).trans ?_
    refine Real.sqrt_le_sqrt ?_
    have hpt : ∀ ω, ‖A n ω‖ ^ 2 =
        ‖∑ k ∈ Finset.range N, ee (n * (b : ℝ) ^ k * G ω)‖ ^ 2 / (N : ℝ) ^ 2 := by
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
        f (((b : ℝ) ^ k * G ω : ℝ) : AddCircle (1 : ℝ))) / N - fourierCoeff f 0‖}
      ≤ μ.real {ω | t ≤ X ω} := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        exact (le_of_lt hω).trans (hle ω)
    _ ≤ (∫ ω, X ω ∂μ) / t := by rw [le_div_iff₀ ht, mul_comm]; exact hmarkov
    _ ≤ (∑' n, B n) * r / t := by gcongr
    _ = _ := by ring


/-- **Visit-count deviation under polynomial decay.** -/
theorem visit_deviation_b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : ℕ) (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (a c ρ t : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hlen : c - a ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (ht : 0 < t) (N : ℕ) (hN : 1 ≤ N) :
    μ.real {ω | 2 * ρ + t < |(visitCount (orbit b (G ω)) a c N : ℝ) / N - (c - a)|} ≤
      2 * (2 / (3 * ρ) / t *
        Real.sqrt ((N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2) / (N : ℝ) ^ 2)) := by
  set fU := HatFourier.plateau ((c - a) / 2 + ρ) ρ ((a + c) / 2)
  set fL := HatFourier.plateau ((c - a) / 2) ρ ((a + c) / 2)
  have hBU : ∀ n, n ≠ 0 → ‖fourierCoeff fU n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hBL : ∀ n, n ≠ 0 → ‖fourierCoeff fL n‖ ≤ plB ρ n := fun n hn =>
    HatFourier.norm_plateau_coeff_le _ ρ _ hρ (by linarith) n hn
  have hB0 : ∀ n, 0 ≤ plB ρ n := fun n => by unfold plB; positivity
  have hdU := prob_mean_dev_b μ b hb G hG hC hδ hdec fU (plB ρ) hB0 hBU (hasSum_plB ρ hρ).summable N hN t ht
  have hdL := prob_mean_dev_b μ b hb G hG hC hδ hdec fL (plB ρ) hB0 hBL (hasSum_plB ρ hρ).summable N hN t ht
  rw [(hasSum_plB ρ hρ).tsum_eq] at hdU hdL
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

end NormalNumbers.VisitDeviationB
