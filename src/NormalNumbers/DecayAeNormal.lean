/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.WeylCriterion
import NormalNumbers.Wall
import Mathlib

/-!
# Polynomial Fourier decay ⇒ almost-sure base-2 normality

For a random real `G` (any probability space) whose characteristic function
`ξ ↦ 𝔼 e(ξ G)` decays like `C|ξ|^{-δ}`, almost every `G ω` is normal in base 2.

Proof (Davenport–Erdős–LeVeque style, as in Manai 2609.24665 `lem:decaynormal`):
`𝔼 ‖Σ_{k<N} e(h 2^k G)‖² ≤ N + K` (`second_moment_le`); so
`Σ_j 𝔼 ‖A_{j²}‖² < ∞`, hence `A_{j²} → 0` a.s. (no Borel–Cantelli needed: an integrable
series is a.e. finite); interpolation (`tendsto_of_tendsto_sq`) gives `A_N → 0`;
then Weyl (`equidistributed_of_weyl`) and Wall (`isNormal_iff_equidistributed_orbit`).
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.DecayAeNormal

/-- `e(t) = exp(2πit)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

/-- Integer-frequency characters ignore the integer part. -/
theorem ee_int_mul_fract (h : ℤ) (t : ℝ) : ee (h * Int.fract t) = ee (h * t) := by
  unfold ee
  rw [Int.fract, show ((h : ℝ) * (t - ⌊t⌋) : ℝ) = h * t + (-(h * ⌊t⌋) : ℤ) by push_cast; ring]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((h : ℂ) * t + -((h : ℂ) * ⌊t⌋))
      = 2 * Real.pi * Complex.I * ((h : ℂ) * t) + ((-(h * ⌊t⌋) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The Weyl mean of the doubling orbit, written with raw (unreduced) phases. -/
theorem fourierMean_orbit_two (x : ℝ) (h : ℤ) (N : ℕ) :
    fourierMean (orbit 2 x) h N = (∑ k ∈ Finset.range N, ee (h * 2 ^ k * x)) / N := by
  unfold fourierMean
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have := ee_int_mul_fract h (x * 2 ^ k)
  unfold ee at this
  unfold orbit
  push_cast at this ⊢
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((Int.fract (x * 2 ^ k) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * ((h : ℂ) * ((Int.fract (x * 2 ^ k) : ℝ) : ℂ)) by ring, this]
  unfold ee; push_cast; ring_nf

/-- Interpolation from square times: unit-bounded summands, means along `j²` tending to `0`,
force all means to `0`. -/
theorem tendsto_of_tendsto_sq (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1)
    (h : Tendsto (fun j : ℕ => (∑ k ∈ Finset.range (j ^ 2), z k) / ((j ^ 2 : ℕ) : ℂ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, z k) / (N : ℂ)) atTop (𝓝 0) := by
  set S : ℕ → ℂ := fun N => ∑ k ∈ Finset.range N, z k
  have hsq : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * b, fun n hn => Nat.le_sqrt.2 hn⟩
  have hA : Tendsto (fun N : ℕ => ‖S (Nat.sqrt N ^ 2) / ((Nat.sqrt N ^ 2 : ℕ) : ℂ)‖
      + 3 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
    have h1 := (h.comp hsq).norm
    have h2 : Tendsto (fun N : ℕ => 3 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 3).comp hsq
    simpa using h1.add h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hA
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set j := Nat.sqrt N
  have hj1 : 1 ≤ j := Nat.le_sqrt.2 (by omega)
  have hjN : j ^ 2 ≤ N := by rw [sq]; exact Nat.sqrt_le N
  have hNj : N < (j + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt N
  have hdiff : ‖S N - S (j ^ 2)‖ ≤ (N - j ^ 2 : ℕ) := by
    have : S N - S (j ^ 2) = ∑ k ∈ Finset.Ico (j ^ 2) N, z k := by
      simp only [S]; rw [Finset.sum_range_sub_sum_range hjN, Finset.range_eq_Ico]
      congr 1; ext k; simp [Finset.mem_Ico]; omega
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hz k).trans ?_
    simp
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hNR : ((j : ℝ)) ^ 2 ≤ N := by exact_mod_cast hjN
  have hdR : ((N - j ^ 2 : ℕ) : ℝ) ≤ 3 * j := by
    have : N - j ^ 2 ≤ 3 * j := by
      have : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
      omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hj2pos : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  rw [norm_div, norm_div]
  simp only [Complex.norm_natCast]
  push_cast
  have hSN : ‖S N‖ ≤ ‖S (j ^ 2)‖ + 3 * j := by
    have := norm_le_insert' (S N) (S (j ^ 2))
    linarith
  calc ‖S N‖ / N ≤ (‖S (j ^ 2)‖ + 3 * j) / N := by gcongr
    _ = ‖S (j ^ 2)‖ / N + 3 * j / N := add_div _ _ _
    _ ≤ ‖S (j ^ 2)‖ / (j : ℝ) ^ 2 + 3 * j / (j : ℝ) ^ 2 := by gcongr
    _ = ‖S (j ^ 2)‖ / (j : ℝ) ^ 2 + 3 / j := by
        congr 1; field_simp

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee; push_cast; rw [← Complex.exp_add]; ring_nf

theorem conj_ee (t : ℝ) : (starRingEnd ℂ) (ee t) = ee (-t) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

theorem measurable_ee : Measurable ee := by
  unfold ee; fun_prop

/-- The square of an exponential sum, expanded. -/
theorem sq_norm_sum_ee (t : ℕ → ℝ) (N : ℕ) :
    ((‖∑ k ∈ Finset.range N, ee (t k)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ee (t n - t m) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [conj_ee, ← ee_add, sub_eq_add_neg]

/-- Lacunary separation: `2ⁿ − 2ᵐ ≥ 2^{(n+m)/2 − 1}` for `m < n`. -/
theorem two_pow_sub_ge {m n : ℕ} (hmn : m < n) :
    (2 : ℝ) ^ (((n + m : ℕ) : ℝ) / 2 - 1) ≤ (2 : ℝ) ^ n - 2 ^ m := by
  have h1 : (2 : ℝ) ^ (((n + m : ℕ) : ℝ) / 2 - 1) ≤ (2 : ℝ) ^ ((n : ℝ) - 1) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
    push_cast; linarith
  have h2 : (2 : ℝ) ^ ((n : ℝ) - 1) = 2 ^ n / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  have h3 : (2 : ℝ) ^ m ≤ 2 ^ n / 2 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [pow_add, pow_add]
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < 2 ^ m := by positivity
    nlinarith
  linarith

/-- The decay bound at a lacunary difference frequency. -/
theorem decay_at_diff {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (h : ℤ) (hh : h ≠ 0) {m n : ℕ}
    (hmn : m ≠ n) :
    C * |(h : ℝ) * ((2 : ℝ) ^ n - 2 ^ m)| ^ (-δ) ≤
      C * 2 ^ δ * ((2 : ℝ) ^ (-δ / 2)) ^ n * ((2 : ℝ) ^ (-δ / 2)) ^ m := by
  have hsep : (2 : ℝ) ^ (((n + m : ℕ) : ℝ) / 2 - 1) ≤ |(h : ℝ) * ((2 : ℝ) ^ n - 2 ^ m)| := by
    have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
    have hd : (2 : ℝ) ^ (((n + m : ℕ) : ℝ) / 2 - 1) ≤ |(2 : ℝ) ^ n - 2 ^ m| := by
      rcases lt_or_gt_of_ne hmn with hlt | hlt
      · exact (two_pow_sub_ge hlt).trans (le_abs_self _)
      · have := two_pow_sub_ge hlt
        rw [add_comm m n] at this
        rw [abs_sub_comm]; exact this.trans (le_abs_self _)
    rw [abs_mul]
    nlinarith [abs_nonneg ((2 : ℝ) ^ n - 2 ^ m)]
  have hmono := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos two_pos _) hsep
    (by linarith : -δ ≤ 0)
  rw [mul_assoc C, mul_assoc C]
  refine mul_le_mul_of_nonneg_left (hmono.trans (le_of_eq ?_)) hC.le
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast; ring

/-- **Second moment of the Weyl sum** under polynomial decay. -/
theorem second_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (h : ℤ) (hh : h ≠ 0) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂μ ≤
      N + C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 := by
  set s : ℝ := (2 : ℝ) ^ (-δ / 2) with hs
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos two_pos _).le
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * G ω)) μ := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  -- expand
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((2 : ℝ) ^ n - 2 ^ m)) * G ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * 2 ^ k * G ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((2 : ℝ) ^ n - 2 ^ m)) * G ω) ∂μ := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  -- termwise bound
  have hterm : ∀ n m : ℕ, ‖∫ ω, ee ((h * ((2 : ℝ) ^ n - 2 ^ m)) * G ω) ∂μ‖ ≤
      (if n = m then 1 else 0) + C * 2 ^ δ * s ^ n * s ^ m := by
    intro n m
    have hK : 0 ≤ C * 2 ^ δ * s ^ n * s ^ m := by positivity
    split_ifs with hnm
    · refine (norm_integral_le_of_norm_le_const (C := 1)
        (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
      simp; linarith
    · have hne : (h : ℝ) * ((2 : ℝ) ^ n - 2 ^ m) ≠ 0 := by
        refine mul_ne_zero (by exact_mod_cast hh) (sub_ne_zero.2 fun he => hnm ?_)
        exact Nat.pow_right_injective le_rfl (by exact_mod_cast he)
      have := decay_at_diff hC hδ h hh (Ne.symm hnm)
      rw [zero_add]
      exact (hdec _ hne).trans this
  have hgeo : ∑ n ∈ Finset.range N, s ^ n ≤ (1 - s)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hs0 hs1]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_geometric_of_lt_one hs0 hs1)
  have hreal : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂μ ≤
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
  gcongr

/-- Almost surely, the Weyl means at a fixed nonzero frequency vanish. -/
theorem ae_tendsto_weyl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ))
    (h : ℤ) (hh : h ≠ 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)) / (N : ℂ))
      atTop (𝓝 0) := by
  set K : ℝ := C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 with hKdef
  have hK : 0 ≤ K := by
    have : (2 : ℝ) ^ (-δ / 2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω) with hSdef
  have hSm : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_sum _ fun k _ => measurable_ee.comp (hG.const_mul _)
  have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω =>
    (norm_sum_le _ _).trans (by simp [norm_ee])
  set f : ℕ → Ω → ℝ := fun j ω => ‖S ((j + 1) ^ 2) ω‖ ^ 2 / (((j + 1) ^ 2 : ℕ) : ℝ) ^ 2
    with hfdef
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
  have hfm : ∀ j, Measurable (f j) := fun j =>
    (((hSm _).norm.pow_const 2).div_const _)
  have hfi : ∀ j, Integrable (f j) μ := fun j =>
    Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hf0 j ω)]
      have hpos : (0 : ℝ) < (((j + 1) ^ 2 : ℕ) : ℝ) := by positivity
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
  have hfI : ∀ j, ∫ ω, f j ω ∂μ ≤ (1 + K) * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j
    have hM := second_moment_le μ G hG hC hδ hdec h hh ((j + 1) ^ 2)
    simp only [hfdef]
    rw [integral_div]
    set M : ℝ := (((j + 1) ^ 2 : ℕ) : ℝ)
    have hM1 : (1 : ℝ) ≤ M := by simp only [M]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have hMe : M = ((j : ℝ) + 1) ^ 2 := by simp [M]
    rw [div_le_iff₀ (by positivity)]
    calc ∫ ω, ‖S ((j + 1) ^ 2) ω‖ ^ 2 ∂μ ≤ M + K := hM
      _ ≤ M + K * M := by nlinarith
      _ = (1 + K) * (1 / M) * M ^ 2 := by field_simp
      _ = _ := by rw [hMe]
  have hsumm : Summable fun j : ℕ => (1 + K) * (1 / ((j : ℝ) + 1) ^ 2) := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using this
  have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, (1 + K) * (1 / ((j : ℝ) + 1) ^ 2))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    exact ENNReal.ofReal_le_ofReal (hfI j)
  have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
    (hfm j).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
  have h3 : Tendsto (fun j : ℕ => S ((j + 1) ^ 2) ω / (((j + 1) ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := h2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun j => ?_
    simp only [hfdef]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity),
      norm_div, Complex.norm_natCast]
  have h4 : Tendsto (fun j : ℕ => S (j ^ 2) ω / ((j ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 h3
  exact tendsto_of_tendsto_sq (fun k => ee (h * 2 ^ k * G ω)) (fun k => (norm_ee _).le) h4

/-- **Polynomial Fourier decay ⇒ almost-sure base-2 normality.** -/
theorem ae_isNormal_two_of_decay {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂μ‖ ≤ C * |ξ| ^ (-δ)) :
    ∀ᵐ ω ∂μ, IsNormal 2 (G ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [ae_tendsto_weyl μ G hG hC hδ hdec h hh] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  have := hω h hh
  refine this.congr fun N => ?_
  rw [fourierMean_orbit_two]

end NormalNumbers.DecayAeNormal
