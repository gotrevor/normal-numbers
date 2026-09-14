/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SeparatingTest
import NormalNumbers.G4EntropySample

/-!
# Entropy expedition §3C: the positive-mass capture inequality (C)

The existing `separating_test_bound` proves a *one-sided* statement: a bounded test whose Haar
average is large and whose sample average is small forces `1 ≤ δ₁ + δ₂ + 2κ + Λδ₃`.  Its proof,
however, establishes a genuinely two-sided fact, and the entropy argument needs the *other*
side.  So the load-bearing content is extracted here as

  `abs_sampleAvg_sub_integral_le` : `|sampleAvg P S f − ∫ f dμ| ≤ 2κ + Λ·δ₃`,

with the old conclusion recovered verbatim as the instance `separating_test_bound_of_transfer`
(the old theorem in `G4SeparatingTest` is untouched).

The second ingredient is the **bounded-Lipschitz bump**

  `bump E ρ y = 1 − min 1 (infDist y E / ρ)`,

which is `1` on `E`, `0` off the `ρ`-thickening of `E`, valued in `[0,1]`, and drops by at most
`dist y z / ρ` when the point moves (`bump_sub_le`).  That last inequality is exactly what turns
"the transported point `F n` is captured" into "the small-prime vector `S n`, which is the point
the Fourier estimates actually control, nearly captures" at a cost `a/ρ`.

Putting them together gives **(C)** (`capture_inequality`): for any set `Good ⊆ P` of sample
points whose transported images land in `E`,

  `|Good| / |P| ≤ μ(thickening ρ E) + a/ρ + 2κ + Λq`,  `a = avg_n dist (F n) (S n)`.

This is a finite unconditional expectation comparison: nothing is conditioned on membership in
the selected low-information event `ℬ`, which is what makes a data-dependent choice of `ℬ`
legitimate later.
-/

open MeasureTheory Metric Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

/-! ### The two-sided sample ↔ Haar transfer -/

section transfer

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]

/-- **The transfer inequality.**  A bounded real test that is uniformly `κ`-approximated by a
character polynomial of nontrivial Fourier mass `≤ Λ`, all of whose nontrivial characters have
sample average of modulus `≤ δ₃`, has sample average within `2κ + Λδ₃` of its Haar average.
This is the two-sided statement hidden inside `separating_test_bound`. -/
theorem abs_sampleAvg_sub_integral_le
    (Q : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ Q) (χ : ι → Ω → ℂ)
    (hχ₀ : ∀ ω, χ i₀ ω = 1)
    (hχ_int : ∀ i ∈ Q, Integrable (χ i) μ)
    (hχ_orth : ∀ i ∈ Q, i ≠ i₀ → ∫ ω, χ i ω ∂μ = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (S : ℕ → Ω)
    (f : Ω → ℝ) (hf_int : Integrable f μ)
    (c : ι → ℂ) (κ : ℝ)
    (h_approx : ∀ ω, ‖(∑ i ∈ Q, c i * χ i ω) - (f ω : ℂ)‖ ≤ κ)
    {δ₃ Λ : ℝ}
    (h_decay : ∀ i ∈ Q, i ≠ i₀ → ‖sampleAvg P S (χ i)‖ ≤ δ₃)
    (h_budget : ∑ i ∈ Q.erase i₀, ‖c i‖ ≤ Λ)
    (hδ₃ : 0 ≤ δ₃) :
    |sampleAvg P S f - ∫ ω, f ω ∂μ| ≤ 2 * κ + Λ * δ₃ := by
  set Pc : Ω → ℂ := fun ω => ∑ i ∈ Q, c i * χ i ω with hPc
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hPc_int : Integrable Pc μ := by
    refine integrable_finsetSum Q fun i hi => ?_
    exact (hχ_int i hi).const_mul (c i)
  have h_int_Pc : ∫ ω, Pc ω ∂μ = c i₀ := by
    simp only [hPc]
    rw [integral_finsetSum Q fun i hi => (hχ_int i hi).const_mul (c i)]
    rw [← Finset.add_sum_erase Q _ hi₀]
    have h0 : ∫ ω, c i₀ * χ i₀ ω ∂μ = c i₀ := by simp [hχ₀]
    rw [h0, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [integral_const_mul, hχ_orth i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi),
      mul_zero]
  have h_lin : sampleAvg P S Pc = ∑ i ∈ Q, c i * sampleAvg P S (χ i) := by
    simp only [sampleAvg, hPc, Complex.real_smul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    ring
  have h_avg₀ : sampleAvg P S (χ i₀) = 1 := by
    simp only [sampleAvg, hχ₀, Finset.sum_const, Complex.real_smul]
    have : ((P.card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  have h_avg_Pc : sampleAvg P S Pc = c i₀ + ∑ i ∈ Q.erase i₀, c i * sampleAvg P S (χ i) := by
    rw [h_lin, ← Finset.add_sum_erase Q _ hi₀, h_avg₀, mul_one]
  have h_avg_close : ‖sampleAvg P S Pc - c i₀‖ ≤ Λ * δ₃ := by
    rw [h_avg_Pc, add_sub_cancel_left]
    calc ‖∑ i ∈ Q.erase i₀, c i * sampleAvg P S (χ i)‖
        ≤ ∑ i ∈ Q.erase i₀, ‖c i * sampleAvg P S (χ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Q.erase i₀, ‖c i‖ * δ₃ := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (h_decay i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)) (norm_nonneg _)
      _ = (∑ i ∈ Q.erase i₀, ‖c i‖) * δ₃ := by rw [Finset.sum_mul]
      _ ≤ Λ * δ₃ := mul_le_mul_of_nonneg_right h_budget hδ₃
  have h_haar_close : ‖c i₀ - ((∫ ω, f ω ∂μ : ℝ) : ℂ)‖ ≤ κ := by
    have hfC : Integrable (fun ω => (f ω : ℂ)) μ := hf_int.ofReal
    rw [← h_int_Pc, ← integral_complex_ofReal, ← integral_sub hPc_int hfC]
    calc ‖∫ ω, (Pc ω - (f ω : ℂ)) ∂μ‖
        ≤ κ * (μ Set.univ).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall h_approx)
      _ = κ := by simp
  have h_sample_close : ‖sampleAvg P S Pc - ((sampleAvg P S f : ℝ) : ℂ)‖ ≤ κ := by
    simp only [sampleAvg, smul_eq_mul, Complex.real_smul]
    push_cast
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    calc ((P.card : ℝ))⁻¹ * ‖∑ n ∈ P, (Pc (S n) - (f (S n) : ℂ))‖
        ≤ (P.card : ℝ)⁻¹ * ∑ n ∈ P, κ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => h_approx (S n))
      _ = κ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  -- assemble both directions on real parts
  have e1 : |(c i₀).re - ∫ ω, f ω ∂μ| ≤ κ := by
    have := (Complex.abs_re_le_norm (c i₀ - ((∫ ω, f ω ∂μ : ℝ) : ℂ))).trans h_haar_close
    rwa [Complex.sub_re, Complex.ofReal_re] at this
  have e2 : |(sampleAvg P S Pc).re - (c i₀).re| ≤ Λ * δ₃ := by
    have := (Complex.abs_re_le_norm (sampleAvg P S Pc - c i₀)).trans h_avg_close
    rwa [Complex.sub_re] at this
  have e3 : |(sampleAvg P S Pc).re - sampleAvg P S f| ≤ κ := by
    have := (Complex.abs_re_le_norm (sampleAvg P S Pc - ((sampleAvg P S f : ℝ) : ℂ))).trans
      h_sample_close
    rwa [Complex.sub_re, Complex.ofReal_re] at this
  have b1 := abs_le.1 e1
  have b2 := abs_le.1 e2
  have b3 := abs_le.1 e3
  rw [abs_le]
  constructor <;> linarith

/-- The old `separating_test_bound` conclusion, recovered as an instance of the transfer. -/
theorem separating_test_bound_of_transfer
    (P : Finset ℕ) (S : ℕ → Ω) (f : Ω → ℝ) {δ₁ δ₂ κ Λ δ₃ : ℝ}
    (h_transfer : |sampleAvg P S f - ∫ ω, f ω ∂μ| ≤ 2 * κ + Λ * δ₃)
    (h_haar : 1 - δ₁ ≤ ∫ ω, f ω ∂μ)
    (h_sample : sampleAvg P S f ≤ δ₂) :
    1 ≤ δ₁ + δ₂ + 2 * κ + Λ * δ₃ := by
  have := abs_le.1 h_transfer
  linarith [this.1, this.2]

end transfer

/-! ### The bounded-Lipschitz bump -/

section bump

variable {Ω : Type*} [PseudoMetricSpace Ω]

/-- The bump `1 - min 1 (d(y,E)/ρ)`: one on `E`, zero off the `ρ`-thickening, `1/ρ`-Lipschitz. -/
noncomputable def bump (E : Set Ω) (ρ : ℝ) (y : Ω) : ℝ := 1 - min 1 (infDist y E / ρ)

lemma bump_nonneg (E : Set Ω) (ρ : ℝ) (y : Ω) : 0 ≤ bump E ρ y := by
  unfold bump
  have : min 1 (infDist y E / ρ) ≤ 1 := min_le_left _ _
  linarith

lemma bump_le_one {E : Set Ω} {ρ : ℝ} (hρ : 0 < ρ) (y : Ω) : bump E ρ y ≤ 1 := by
  unfold bump
  have : 0 ≤ min 1 (infDist y E / ρ) :=
    le_min zero_le_one (div_nonneg (infDist_nonneg) hρ.le)
  linarith

lemma bump_eq_one_of_mem {E : Set Ω} {ρ : ℝ} {y : Ω} (hy : y ∈ E) : bump E ρ y = 1 := by
  unfold bump
  rw [infDist_zero_of_mem hy]
  simp

/-- Off the `ρ`-thickening the bump vanishes. -/
lemma bump_eq_zero_of_not_mem {E : Set Ω} {ρ : ℝ} (hρ : 0 < ρ) (hE : E.Nonempty) {y : Ω}
    (h : y ∉ thickening ρ E) : bump E ρ y = 0 := by
  rw [mem_thickening_iff_infDist_lt hE] at h
  have hle : ρ ≤ infDist y E := not_lt.1 h
  have h1 : (1 : ℝ) ≤ infDist y E / ρ := by
    rw [le_div_iff₀ hρ, one_mul]
    exact hle
  unfold bump
  rw [min_eq_left h1]
  ring

/-- The key Lipschitz drop: moving from `y` to `z` costs at most `dist y z / ρ`. -/
lemma bump_sub_le {E : Set Ω} {ρ : ℝ} (hρ : 0 < ρ) (y z : Ω) :
    bump E ρ y - bump E ρ z ≤ dist y z / ρ := by
  have hd : infDist z E ≤ infDist y E + dist z y := infDist_le_infDist_add_dist
  have hD : (0 : ℝ) ≤ dist y z / ρ := div_nonneg dist_nonneg hρ.le
  have hstep : min 1 (infDist z E / ρ) ≤ min 1 (infDist y E / ρ) + dist y z / ρ := by
    have hz : infDist z E / ρ ≤ infDist y E / ρ + dist y z / ρ := by
      rw [← add_div, div_le_div_iff_of_pos_right hρ, dist_comm y z]
      linarith
    rcases le_total (infDist y E / ρ) 1 with h | h
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) hz
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by linarith)
  unfold bump
  linarith

lemma continuous_bump (E : Set Ω) (ρ : ℝ) : Continuous (bump E ρ) :=
  continuous_const.sub (continuous_const.min ((continuous_infDist_pt E).div_const ρ))

end bump

/-! ### (C): the positive-mass capture inequality -/

section capture

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_bump (E : Set Ω) {ρ : ℝ} (hρ : 0 < ρ) : Integrable (bump E ρ) μ := by
  refine Integrable.mono' (integrable_const 1) (continuous_bump E ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (bump_nonneg _ _ _)]
  exact bump_le_one hρ y

/-- The bump's Haar average is at most the volume of the `ρ`-thickening: it is supported there
and bounded by one. -/
lemma integral_bump_le (E : Set Ω) (hE : E.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ ω, bump E ρ ω ∂μ ≤ (μ (thickening ρ E)).toReal := by
  have hmeas : MeasurableSet (thickening ρ E) := isOpen_thickening.measurableSet
  have hind : Integrable (Set.indicator (thickening ρ E) (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hle : ∀ ω, bump E ρ ω ≤ Set.indicator (thickening ρ E) (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ thickening ρ E
    · rw [Set.indicator_of_mem hω]
      exact bump_le_one hρ ω
    · rw [Set.indicator_of_notMem hω, bump_eq_zero_of_not_mem hρ hE hω]
  refine (integral_mono (integrable_bump E hρ) hind hle).trans_eq ?_
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) hmeas]
  simp [MeasureTheory.measureReal_def]

/-- **(C), the capture inequality.**  If the transported points `F n` of a sub-sample `Good`
all land in `E`, then the density of `Good` is controlled by the volume of the `ρ`-thickening
of `E` plus the average transport error `a/ρ` plus the Fourier/approximation budget.

This is an unconditional comparison of two expectations; nothing is conditioned on membership
in `Good`, which is why a data-dependent choice of the captured collection is legitimate. -/
theorem capture_inequality
    (E : Set Ω) (hE : E.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (P : Finset ℕ) (hP : P.Nonempty) (F S : ℕ → Ω)
    (Good : Finset ℕ) (hGood : Good ⊆ P) (hcap : ∀ n ∈ Good, F n ∈ E)
    {a κ Λ q : ℝ}
    (ha : (P.card : ℝ)⁻¹ * ∑ n ∈ P, dist (F n) (S n) ≤ a)
    (htrans : |sampleAvg P S (bump E ρ) - ∫ ω, bump E ρ ω ∂μ| ≤ 2 * κ + Λ * q) :
    (Good.card : ℝ) / P.card ≤ (μ (thickening ρ E)).toReal + a / ρ + 2 * κ + Λ * q := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  -- lower bound for the sample average of the bump
  have hlow : ∑ n ∈ Good, (1 - dist (F n) (S n) / ρ) ≤ ∑ n ∈ P, bump E ρ (S n) := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hGood fun n _ _ => bump_nonneg _ _ _)
    have h1 : bump E ρ (F n) = 1 := bump_eq_one_of_mem (hcap n hn)
    have h2 := bump_sub_le (E := E) hρ (F n) (S n)
    rw [h1] at h2
    linarith
  have hdrop : ∑ n ∈ Good, dist (F n) (S n) ≤ ∑ n ∈ P, dist (F n) (S n) :=
    Finset.sum_le_sum_of_subset_of_nonneg hGood fun n _ _ => dist_nonneg
  have hsplit : ∑ n ∈ Good, (1 - dist (F n) (S n) / ρ)
      = (Good.card : ℝ) - (∑ n ∈ Good, dist (F n) (S n)) / ρ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div]
  have havg : (Good.card : ℝ) / P.card - a / ρ ≤ sampleAvg P S (bump E ρ) := by
    have hstep : (Good.card : ℝ) - (∑ n ∈ P, dist (F n) (S n)) / ρ
        ≤ ∑ n ∈ P, bump E ρ (S n) := by
      rw [hsplit] at hlow
      have : (∑ n ∈ Good, dist (F n) (S n)) / ρ ≤ (∑ n ∈ P, dist (F n) (S n)) / ρ :=
        div_le_div_of_nonneg_right hdrop hρ.le
      linarith
    have hmul : ((P.card : ℝ))⁻¹ * ((Good.card : ℝ) - (∑ n ∈ P, dist (F n) (S n)) / ρ)
        ≤ ((P.card : ℝ))⁻¹ * ∑ n ∈ P, bump E ρ (S n) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    have hexp : ((P.card : ℝ))⁻¹ * ((Good.card : ℝ) - (∑ n ∈ P, dist (F n) (S n)) / ρ)
        = (Good.card : ℝ) / P.card
          - ((P.card : ℝ))⁻¹ * (∑ n ∈ P, dist (F n) (S n)) / ρ := by
      field_simp
    have hax : ((P.card : ℝ))⁻¹ * (∑ n ∈ P, dist (F n) (S n)) / ρ ≤ a / ρ :=
      div_le_div_of_nonneg_right ha hρ.le
    simp only [sampleAvg, smul_eq_mul]
    rw [hexp] at hmul
    linarith
  have hupper := (abs_le.1 htrans).2
  have hvol := integral_bump_le (μ := μ) E hE hρ
  linarith

end capture

end NormalNumbers.G4Entropy
