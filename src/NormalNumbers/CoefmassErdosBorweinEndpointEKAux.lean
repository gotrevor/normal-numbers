/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Soft Gaussian ballot estimate for the Erdős–Borwein endpoint

This is the minimal local port of the kernel-checked Gaussian barrier argument from
`ErdosProblems.Erdos520.HarperGaussianBarrier` and `HarperGaussianWalk`, through the
fourth-root survival estimate needed by the endpoint proof.  The sibling project is not a
dependency of this repository, so the argument is kept here over Mathlib alone.
-/

namespace NormalNumbers.ErdosBorweinEndpointEKAux

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-!
# Elementary Gaussian barrier infrastructure

Harper's published proof invokes a sharp Gaussian ballot estimate after the
blockwise characteristic-function comparison.  For the upper bound needed by
#520, it is useful to isolate two considerably softer ingredients as well:

* a Gaussian endpoint interval has mass at most its length times the peak of
  the Gaussian density;
* a barrier event can be split according to whether its terminal distance
  from the barrier is small or large.

The latter split, combined with a positive superharmonic function for the
killed Gaussian walk, gives a polynomial survival saving without requiring
the sharp ballot constant.  This file starts that alternative route with the
fully explicit density and abstract splitting estimates.
-/

/-- The standard Gaussian kernel without its normalizing constant. -/
noncomputable def standardGaussianKernel (x : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * x ^ 2)

theorem standardGaussianKernel_pos (x : ℝ) :
    0 < standardGaussianKernel x := by
  exact Real.exp_pos _

theorem continuous_standardGaussianKernel :
    Continuous standardGaussianKernel := by
  unfold standardGaussianKernel
  fun_prop

theorem hasDerivAt_standardGaussianKernel (x : ℝ) :
    HasDerivAt standardGaussianKernel
      (-x * standardGaussianKernel x) x := by
  unfold standardGaussianKernel
  have hinner : HasDerivAt (fun z : ℝ ↦ -(1 / 2 : ℝ) * z ^ 2) (-x) x := by
    convert! (((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))) using 1;
      simp only [id_eq]; ring
  convert! (Real.hasDerivAt_exp _).comp x hinner using 1; ring

theorem integrable_standardGaussianKernel :
    Integrable standardGaussianKernel := by
  simpa only [standardGaussianKernel] using!
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

theorem integrable_id_mul_standardGaussianKernel :
    Integrable (fun x : ℝ ↦ x * standardGaussianKernel x) := by
  simpa only [standardGaussianKernel] using!
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

theorem tendsto_standardGaussianKernel_atBot :
    Filter.Tendsto standardGaussianKernel Filter.atBot (nhds 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (f' := fun x : ℝ ↦ -x * standardGaussianKernel x)
  · intro x hx
    exact hasDerivAt_standardGaussianKernel x
  · simpa only [Pi.neg_apply, neg_mul] using!
      integrable_id_mul_standardGaussianKernel.neg.integrableOn
  · exact integrable_standardGaussianKernel.integrableOn

/-- Exact truncated first moment of the unnormalized standard Gaussian
kernel. -/
theorem integral_Iic_id_mul_standardGaussianKernel (x : ℝ) :
    (∫ z in Iic x, z * standardGaussianKernel z) =
      -standardGaussianKernel x := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := x) (m := (0 : ℝ))
    (f := standardGaussianKernel)
    (f' := fun z : ℝ ↦ -z * standardGaussianKernel z)
    (fun z hz ↦ hasDerivAt_standardGaussianKernel z)
    (by simpa only [Pi.neg_apply, neg_mul] using!
      integrable_id_mul_standardGaussianKernel.neg.integrableOn)
    tendsto_standardGaussianKernel_atBot
  simp only [neg_mul, integral_neg, sub_zero] at h
  linarith

/-- An elementary finite-interval exponential integral used in the Gaussian
tail lower bound below. -/
theorem intervalIntegral_exp_neg_mul (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in (0 : ℝ)..1, Real.exp (-a * u)) =
      (1 - Real.exp (-a)) / a := by
  let F : ℝ → ℝ := fun u ↦ -Real.exp (-a * u) / a
  have hF (u : ℝ) : HasDerivAt F (Real.exp (-a * u)) u := by
    have hinner : HasDerivAt (fun z : ℝ ↦ -a * z) (-a) u := by
      simpa [id] using! (hasDerivAt_id u).const_mul (-a)
    have hexp := (Real.hasDerivAt_exp _).comp u hinner
    unfold F
    convert! hexp.neg.div_const a using 1;
      field_simp [ha.ne']
  calc
    (∫ u : ℝ in (0 : ℝ)..1, Real.exp (-a * u)) = F 1 - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      · exact ((Real.continuous_exp.comp
          (continuous_const.neg.mul continuous_id)).neg.div_const a).continuousOn
      · intro u hu
        exact hF u
      · exact (Real.continuous_exp.comp
          (continuous_const.neg.mul continuous_id)).intervalIntegrable _ _
    _ = (1 - Real.exp (-a)) / a := by
      unfold F
      simp only [mul_one, mul_zero, Real.exp_zero]
      field_simp [ha.ne']
      ring

/-- The elementary exponential integral over `[0,1]` has the reciprocal
lower bound needed for a coarse Mills-ratio estimate. -/
theorem one_div_add_two_le_intervalIntegral_exp
    {x : ℝ} (hx : 0 ≤ x) :
    1 / (x + 2) ≤
      ∫ u : ℝ in (0 : ℝ)..1,
        Real.exp (-(x + 1 / 2) * u) := by
  let a : ℝ := x + 1 / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : 0 < a + 1 := by linarith
  have ha32 : a + 1 ≤ a + 3 / 2 := by norm_num
  have hexpLower : a + 1 ≤ Real.exp a := by
    simpa only [add_comm] using! Real.add_one_le_exp a
  have hexpNeg : Real.exp (-a) ≤ 1 / (a + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ ha1 hexpLower
  have hnum : a / (a + 1) ≤ 1 - Real.exp (-a) := by
    calc
      a / (a + 1) = 1 - 1 / (a + 1) := by
        field_simp [ha1.ne']
        ring
      _ ≤ 1 - Real.exp (-a) := sub_le_sub_left hexpNeg 1
  have hratio : 1 / (a + 1) ≤ (1 - Real.exp (-a)) / a := by
    rw [le_div_iff₀ ha]
    calc
      1 / (a + 1) * a = a / (a + 1) := by ring
      _ ≤ 1 - Real.exp (-a) := hnum
  rw [intervalIntegral_exp_neg_mul a ha]
  calc
    1 / (x + 2) = 1 / (a + 3 / 2) := by
      dsimp [a]
      ring
    _ ≤ 1 / (a + 1) := by
      simpa only [one_div] using! inv_anti₀ ha1 ha32
    _ ≤ (1 - Real.exp (-a)) / a := hratio

theorem standardGaussianKernel_mul_exp_le_add
    {x u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    standardGaussianKernel x * Real.exp (-(x + 1 / 2) * u) ≤
      standardGaussianKernel (x + u) := by
  unfold standardGaussianKernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have huu : u ^ 2 ≤ u := by nlinarith
  nlinarith

/-- Coarse Mills-ratio lower bound for the unnormalized standard Gaussian
kernel.  The constant `2` is deliberately generous and makes the proof use
only a one-unit interval. -/
theorem standardGaussianKernel_le_add_two_mul_tail
    {x : ℝ} (hx : 0 ≤ x) :
    standardGaussianKernel x ≤
      (x + 2) * ∫ z in Ioi x, standardGaussianKernel z := by
  have hx2 : 0 < x + 2 := by linarith
  have hpoint : ∀ u ∈ Icc (0 : ℝ) 1,
      standardGaussianKernel x * Real.exp (-(x + 1 / 2) * u) ≤
        standardGaussianKernel (x + u) := by
    intro u hu
    exact standardGaussianKernel_mul_exp_le_add hu.1 hu.2
  have hinterval :
      standardGaussianKernel x /
          (x + 2) ≤
        ∫ u : ℝ in (0 : ℝ)..1, standardGaussianKernel (x + u) := by
    calc
      standardGaussianKernel x / (x + 2) =
          standardGaussianKernel x * (1 / (x + 2)) := by ring
      _ ≤ standardGaussianKernel x *
          (∫ u : ℝ in (0 : ℝ)..1,
            Real.exp (-(x + 1 / 2) * u)) := by
        exact mul_le_mul_of_nonneg_left
          (one_div_add_two_le_intervalIntegral_exp hx)
          (standardGaussianKernel_pos x).le
      _ = ∫ u : ℝ in (0 : ℝ)..1,
          standardGaussianKernel x *
            Real.exp (-(x + 1 / 2) * u) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ u : ℝ in (0 : ℝ)..1,
          standardGaussianKernel (x + u) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact (continuous_const.mul <|
            Real.continuous_exp.comp
              (continuous_const.neg.mul continuous_id)).intervalIntegrable _ _
        · exact (continuous_standardGaussianKernel.comp
            (continuous_const.add continuous_id)).intervalIntegrable _ _
        · exact hpoint
  have htranslate :
      (∫ u : ℝ in (0 : ℝ)..1, standardGaussianKernel (x + u)) =
        ∫ z : ℝ in x..x + 1, standardGaussianKernel z := by
    simpa only [zero_add, add_zero, add_comm] using!
      (intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := 1) standardGaussianKernel x)
  have hset :
      (∫ z : ℝ in x..x + 1, standardGaussianKernel z) ≤
        ∫ z in Ioi x, standardGaussianKernel z := by
    rw [intervalIntegral.integral_of_le (by linarith : x ≤ x + 1)]
    apply setIntegral_mono_set integrable_standardGaussianKernel.integrableOn
    · change ∀ᵐ z ∂volume.restrict (Ioi x),
        (0 : ℝ) ≤ standardGaussianKernel z
      exact Filter.Eventually.of_forall fun z ↦
        (standardGaussianKernel_pos z).le
    · filter_upwards with z
      exact fun hz ↦ hz.1
  rw [htranslate] at hinterval
  have hdiv : standardGaussianKernel x / (x + 2) ≤
      ∫ z in Ioi x, standardGaussianKernel z := hinterval.trans hset
  simpa only [mul_comm] using! (div_le_iff₀ hx2).mp hdiv

/-- The affine distance-to-barrier function is superharmonic for the
standard Gaussian kernel killed on crossing the barrier. -/
theorem integral_Iic_gaussianBarrierPotential_le
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x,
        (x - z + 2) * standardGaussianKernel z) ≤
      (x + 2) * ∫ z : ℝ, standardGaussianKernel z := by
  have hx2 : 0 ≤ x + 2 := by linarith
  have hconstInt : IntegrableOn
      (fun z : ℝ ↦ (x + 2) * standardGaussianKernel z) (Iic x) :=
    integrable_standardGaussianKernel.const_mul (x + 2) |>.integrableOn
  have hidInt : IntegrableOn
      (fun z : ℝ ↦ z * standardGaussianKernel z) (Iic x) :=
    integrable_id_mul_standardGaussianKernel.integrableOn
  calc
    (∫ z in Iic x,
        (x - z + 2) * standardGaussianKernel z) =
        (∫ z in Iic x,
          ((x + 2) * standardGaussianKernel z -
            z * standardGaussianKernel z)) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro z hz
      ring
    _ = (x + 2) * (∫ z in Iic x, standardGaussianKernel z) -
        ∫ z in Iic x, z * standardGaussianKernel z := by
      rw [integral_sub hconstInt hidInt, integral_const_mul]
    _ = (x + 2) * (∫ z in Iic x, standardGaussianKernel z) +
        standardGaussianKernel x := by
      rw [integral_Iic_id_mul_standardGaussianKernel]
      ring
    _ ≤ (x + 2) * (∫ z in Iic x, standardGaussianKernel z) +
        (x + 2) * ∫ z in Ioi x, standardGaussianKernel z := by
      simpa only [add_comm] using! add_le_add_left
        (standardGaussianKernel_le_add_two_mul_tail hx)
        ((x + 2) * ∫ z in Iic x, standardGaussianKernel z)
    _ = (x + 2) * ∫ z : ℝ, standardGaussianKernel z := by
      rw [← mul_add]
      congr 1
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          integrable_standardGaussianKernel.integrableOn
          integrable_standardGaussianKernel.integrableOn,
        Set.Iic_union_Ioi, setIntegral_univ]

/-- Set-integral form of Mathlib's Gaussian density representation. -/
theorem setIntegral_gaussianReal_eq_integral_mul
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    (∫ x in s, f x ∂gaussianReal m v) =
      ∫ x in s, gaussianPDFReal m v x * f x := by
  rw [← integral_indicator hs,
    integral_gaussianReal_eq_integral_smul (f := s.indicator f) hv,
    ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ s <;> simp [hx, smul_eq_mul]

theorem gaussianPDFReal_zero_one_eq (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * standardGaussianKernel x := by
  unfold gaussianPDFReal standardGaussianKernel
  simp only [NNReal.coe_one, mul_one, sub_zero]
  change (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2)
  congr 2
  ring

/-- The affine potential is genuinely superharmonic for one step of a
standard Gaussian random walk killed on leaving the nonnegative half-line. -/
theorem integral_Iic_gaussianReal_barrierPotential_le
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x, (x - z + 2) ∂gaussianReal 0 1) ≤ x + 2 := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  rw [setIntegral_gaussianReal_eq_integral_mul (by norm_num) (Iic x)
    measurableSet_Iic]
  calc
    (∫ z in Iic x,
        gaussianPDFReal 0 1 z * (x - z + 2)) =
        c * ∫ z in Iic x,
          (x - z + 2) * standardGaussianKernel z := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Iic
      intro z hz
      change gaussianPDFReal 0 1 z * (x - z + 2) =
        c * ((x - z + 2) * standardGaussianKernel z)
      rw [gaussianPDFReal_zero_one_eq]
      dsimp [c]
      ring
    _ ≤ c * ((x + 2) * ∫ z : ℝ, standardGaussianKernel z) := by
      exact mul_le_mul_of_nonneg_left
        (integral_Iic_gaussianBarrierPotential_le hx) hc
    _ = (x + 2) * (c * ∫ z : ℝ, standardGaussianKernel z) := by ring
    _ = (x + 2) * ∫ z : ℝ, gaussianPDFReal 0 1 z := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [gaussianPDFReal_zero_one_eq]
    _ = x + 2 := by
      rw [integral_gaussianPDFReal_eq_one 0 (by norm_num)]
      ring

/-- A nondegenerate real Gaussian density is bounded by its value at its
mean. -/
theorem gaussianPDFReal_le_peak
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  unfold gaussianPDFReal
  have hden : 0 < (2 : ℝ) * (v : ℝ) := by
    positivity
  have hexponent : -(x - m) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden.le
  have hexp : Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    simpa only [Real.exp_zero] using! Real.exp_le_exp.mpr hexponent
  exact mul_le_of_le_one_right (by positivity) hexp

/-- The real mass of a Gaussian interval is bounded by its length times the
peak density.  No normal-CDF API is needed. -/
theorem gaussianReal_real_Icc_le
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) := by
  rw [Measure.real, gaussianReal_apply_eq_integral m hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      (∫ x in Icc a b, gaussianPDFReal m v x) ≤
          ∫ _x in Icc a b,
            (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
        apply setIntegral_mono_on
        · exact (integrable_gaussianPDFReal m v).integrableOn
        · exact integrableOn_const (by simp)
        · exact measurableSet_Icc
        · intro x hx
          exact gaussianPDFReal_le_peak m hv x
      _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
        simp only [smul_eq_mul]
        ring
  · exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg m v x

/-- A version with a coarser but cleaner peak `1 / sqrt v`. -/
theorem gaussianReal_real_Icc_le_inv_sqrt
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤
      (b - a) / Real.sqrt (v : ℝ) := by
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hv0 : 0 ≤ (v : ℝ) := v.2
  have hsqrtv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrt : Real.sqrt (v : ℝ) ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    (gaussianReal m v).real (Icc a b) ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) :=
      gaussianReal_real_Icc_le m hv hab
    _ ≤ (Real.sqrt (v : ℝ))⁻¹ * (b - a) := by
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hsqrtv hsqrt)
        (sub_nonneg.mpr hab)
    _ = (b - a) / Real.sqrt (v : ℝ) := by ring

/-- Abstract near/far terminal-distance split for a barrier event.  The
weighted estimate is the output supplied by a positive supermartingale; the
small-distance estimate is supplied by an endpoint density bound. -/
theorem measureReal_barrier_le_of_terminal_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {A near : Set Ω} (hA : MeasurableSet A)
    (hnear : MeasurableSet near) {D : Ω → ℝ} {r V M : ℝ}
    (hr : 0 < r)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn D A P)
    (hD : ∀ omega ∈ A \ near, r ≤ D omega)
    (hweighted : ∫ omega in A, D omega ∂P ≤ V)
    (hnearMass : P.real (A ∩ near) ≤ r * M) :
    P.real A ≤ V / r + r * M := by
  have hfarMeas : MeasurableSet (A \ near) := hA.diff hnear
  have hsplit : A = (A ∩ near) ∪ (A \ near) := by
    ext omega
    by_cases h : omega ∈ near <;> simp
  have hfarWeighted :
      r * P.real (A \ near) ≤ ∫ omega in A \ near, D omega ∂P := by
    calc
      r * P.real (A \ near) = ∫ _omega in A \ near, r ∂P := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ omega in A \ near, D omega ∂P := by
        apply setIntegral_mono_on
        · exact integrableOn_const
        · exact hDintegrable.mono_set sdiff_subset
        · exact hfarMeas
        · intro omega homega
          exact hD omega homega
  have hfarIntegral_le :
      (∫ omega in A \ near, D omega ∂P) ≤ ∫ omega in A, D omega ∂P := by
    apply setIntegral_mono_set hDintegrable
    · change ∀ᵐ omega ∂P.restrict A, (0 : ℝ) ≤ D omega
      rw [ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall fun omega homega ↦
        hDnonneg omega homega
    · filter_upwards with omega
      exact fun homega ↦ sdiff_subset homega
  have hfarMass : P.real (A \ near) ≤ V / r := by
    rw [le_div_iff₀ hr]
    rw [mul_comm]
    exact (hfarWeighted.trans hfarIntegral_le).trans hweighted
  rw [hsplit]
  calc
    P.real ((A ∩ near) ∪ (A \ near)) ≤
        P.real (A ∩ near) + P.real (A \ near) :=
      measureReal_union_le _ _
    _ ≤ r * M + V / r := add_le_add hnearMass hfarMass
    _ = V / r + r * M := add_comm _ _
noncomputable section

/-!
# A killed standard-Gaussian walk

This file iterates the one-step superharmonic estimate from
`HarperGaussianBarrier`.  The recursion is the dynamic-programming value of
the affine terminal potential for a standard-Gaussian walk killed when its
distance from the barrier becomes negative.
-/

/-- The `n`-step killed affine potential.  Starting at distance `x` from the
barrier, a step `z` is retained precisely when `z ≤ x`; after that step the
new distance is `x - z`. -/
noncomputable def gaussianKilledPotential : ℕ → ℝ → ℝ
  | 0, x => x + 2
  | n + 1, x =>
      ∫ z in Iic x, gaussianKilledPotential n (x - z) ∂gaussianReal 0 1

@[simp]
theorem gaussianKilledPotential_zero (x : ℝ) :
    gaussianKilledPotential 0 x = x + 2 := rfl

@[simp]
theorem gaussianKilledPotential_succ (n : ℕ) (x : ℝ) :
    gaussianKilledPotential (n + 1) x =
      ∫ z in Iic x, gaussianKilledPotential n (x - z) ∂gaussianReal 0 1 := rfl

private theorem integrable_id_gaussianReal_zero_one :
    Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) := by
  exact memLp_one_iff_integrable.mp
    (by simpa only [id_eq] using!
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)))

private theorem integrable_gaussianBarrierAffine (x : ℝ) :
    Integrable (fun z : ℝ ↦ x - z + 2) (gaussianReal 0 1) := by
  exact ((integrable_const (μ := gaussianReal 0 1) x).sub
    integrable_id_gaussianReal_zero_one).add
      (integrable_const (μ := gaussianReal 0 1) 2)

/-- At every finite time the killed potential is nonnegative and is bounded
by its initial affine value.  This is the finite-step supermartingale
estimate, proved without any ballot theorem. -/
theorem gaussianKilledPotential_nonneg_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussianKilledPotential n x ∧ gaussianKilledPotential n x ≤ x + 2 := by
  induction n generalizing x with
  | zero =>
      simp only [gaussianKilledPotential_zero]
      constructor <;> linarith
  | succ n ih =>
      rw [gaussianKilledPotential_succ]
      have hnonneg :
          0 ≤ᵐ[(gaussianReal 0 1).restrict (Iic x)]
            fun z ↦ gaussianKilledPotential n (x - z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz)).1
      have hle :
          (fun z ↦ gaussianKilledPotential n (x - z)) ≤ᵐ[
              (gaussianReal 0 1).restrict (Iic x)]
            fun z ↦ x - z + 2 := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz)).2
      constructor
      · exact integral_nonneg_of_ae hnonneg
      · calc
          (∫ z in Iic x,
              gaussianKilledPotential n (x - z) ∂gaussianReal 0 1) ≤
              ∫ z in Iic x, (x - z + 2) ∂gaussianReal 0 1 := by
            exact integral_mono_of_nonneg hnonneg
              (integrable_gaussianBarrierAffine x).integrableOn hle
          _ ≤ x + 2 := integral_Iic_gaussianReal_barrierPotential_le hx

theorem gaussianKilledPotential_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussianKilledPotential n x :=
  (gaussianKilledPotential_nonneg_le n hx).1

theorem gaussianKilledPotential_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianKilledPotential n x ≤ x + 2 :=
  (gaussianKilledPotential_nonneg_le n hx).2

/-- The terminal distance of an unrestricted finite walk. -/
def gaussianWalkTerminalDistance (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) : ℝ :=
  x - ∑ i, omega i

/-- Recursive barrier event, ordered with the first coordinate as the first
Gaussian increment. -/
def gaussianWalkSurvives : (n : ℕ) → ℝ → (Fin n → ℝ) → Prop
  | 0, _x, _omega => True
  | n + 1, x, omega =>
      omega 0 ≤ x ∧ gaussianWalkSurvives n (x - omega 0) (fun i ↦ omega i.succ)

/-- Terminal affine payoff, set to zero on paths killed at the barrier. -/
def gaussianWalkKilledPayoff : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ
  | 0, x, _omega => x + 2
  | n + 1, x, omega =>
      if omega 0 ≤ x then
        gaussianWalkKilledPayoff n (x - omega 0) (fun i ↦ omega i.succ)
      else 0

@[simp]
theorem gaussianWalkKilledPayoff_zero (x : ℝ) (omega : Fin 0 → ℝ) :
    gaussianWalkKilledPayoff 0 x omega = x + 2 := rfl

@[simp]
theorem gaussianWalkKilledPayoff_succ (n : ℕ) (x : ℝ)
    (omega : Fin (n + 1) → ℝ) :
    gaussianWalkKilledPayoff (n + 1) x omega =
      if omega 0 ≤ x then
        gaussianWalkKilledPayoff n (x - omega 0) (fun i ↦ omega i.succ)
      else 0 := rfl

theorem measurable_gaussianWalkKilledPayoff_joint (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦
      gaussianWalkKilledPayoff n p.1 p.2) := by
  induction n with
  | zero =>
      simpa only [gaussianWalkKilledPayoff_zero] using!
        (measurable_fst.add measurable_const)
  | succ n ih =>
      simp only [gaussianWalkKilledPayoff_succ]
      have hhead : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ fun i : Fin n ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply Measurable.ite
      · exact measurableSet_le hhead measurable_fst
      · exact ih.comp ((measurable_fst.sub hhead).prodMk htail)
      · exact measurable_const

theorem measurable_gaussianWalkKilledPayoff (n : ℕ) (x : ℝ) :
    Measurable (gaussianWalkKilledPayoff n x) := by
  exact (measurable_gaussianWalkKilledPayoff_joint n).comp
    (measurable_const.prodMk measurable_id)

/-- On a surviving path, the killed payoff is its terminal affine
distance. -/
theorem gaussianWalkKilledPayoff_eq_of_survives (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) (h : gaussianWalkSurvives n x omega) :
    gaussianWalkKilledPayoff n x omega =
      gaussianWalkTerminalDistance n x omega + 2 := by
  induction n generalizing x with
  | zero => simp [gaussianWalkTerminalDistance]
  | succ n ih =>
    rw [gaussianWalkKilledPayoff_succ]
    have hfirst : omega 0 ≤ x := h.1
    rw [if_pos hfirst,
      ih (x - omega 0) (fun i ↦ omega i.succ) h.2]
    simp only [gaussianWalkTerminalDistance]
    rw [Fin.sum_univ_succ]
    ring

/-- A killed path has zero payoff. -/
theorem gaussianWalkKilledPayoff_eq_zero_of_not_survives (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) (h : ¬gaussianWalkSurvives n x omega) :
    gaussianWalkKilledPayoff n x omega = 0 := by
  induction n generalizing x with
  | zero => exact (h trivial).elim
  | succ n ih =>
      rw [gaussianWalkKilledPayoff_succ]
      by_cases hfirst : omega 0 ≤ x
      · rw [if_pos hfirst]
        apply ih
        intro htail
        exact h ⟨hfirst, htail⟩
      · rw [if_neg hfirst]

/-- A simple `L¹` majorant for the killed terminal payoff. -/
theorem norm_gaussianWalkKilledPayoff_le (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) :
    ‖gaussianWalkKilledPayoff n x omega‖ ≤
      |x| + ∑ i, |omega i| + 2 := by
  by_cases h : gaussianWalkSurvives n x omega
  · rw [gaussianWalkKilledPayoff_eq_of_survives n x omega h]
    simp only [gaussianWalkTerminalDistance]
    calc
      |x - ∑ i, omega i + 2| ≤ |x - ∑ i, omega i| + 2 := by
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using!
          abs_add_le (x - ∑ i, omega i) 2
      _ ≤ |x| + |∑ i, omega i| + 2 := by
        gcongr
        exact abs_sub x (∑ i, omega i)
      _ ≤ |x| + ∑ i, |omega i| + 2 := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
  · rw [gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega h, norm_zero]
    positivity

theorem integrable_gaussianWalkKilledPayoff (n : ℕ) (x : ℝ) :
    Integrable (gaussianWalkKilledPayoff n x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  let Pn : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  have heval (i : Fin n) :
      Integrable (fun omega : Fin n → ℝ ↦ omega i) Pn := by
    exact integrable_eval integrable_id_gaussianReal_zero_one
  have habs (i : Fin n) :
      Integrable (fun omega : Fin n → ℝ ↦ |omega i|) Pn := by
    simpa only [Real.norm_eq_abs] using! (heval i).norm
  have hmajorant : Integrable
      (fun omega : Fin n → ℝ ↦ |x| + ∑ i, |omega i| + 2) Pn := by
    fun_prop
  exact hmajorant.mono'
    (measurable_gaussianWalkKilledPayoff n x).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_gaussianWalkKilledPayoff_le n x))

/-- The dynamic-programming recursion is exactly the expected killed payoff
on the finite iid standard-Gaussian product space. -/
theorem integral_gaussianWalkKilledPayoff_eq (n : ℕ) (x : ℝ) :
    (∫ omega : Fin n → ℝ, gaussianWalkKilledPayoff n x omega
      ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
        gaussianKilledPotential n x := by
  induction n generalizing x with
  | zero =>
      simp [gaussianWalkKilledPayoff, gaussianKilledPotential]
  | succ n ih =>
      let gamma : Measure ℝ := gaussianReal 0 1
      let Ptail : Measure (Fin n → ℝ) :=
        Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) 0).symm
      have he_symm (p : ℝ × (Fin n → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin n → ℝ) ↦
            gaussianWalkKilledPayoff (n + 1) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (integrable_gaussianWalkKilledPayoff (n + 1) x)
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ, gaussianWalkKilledPayoff_succ]
      rw [gaussianKilledPotential_succ]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x
        · simp only [hz, if_true, mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail] using! ih (x - z)
        · have hnot : z ∉ Iic x := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

/-- The sum of `n` coordinates on the finite iid standard-Gaussian product
space is Gaussian with variance `n`. -/
theorem map_gaussianWalk_sum_eq (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map
        (fun omega ↦ ∑ i, omega i) =
      gaussianReal 0 (n : ℝ≥0) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_sum_pi_eq_prod]
  simp_rw [charFun_gaussianReal]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, Pi.pow_apply]
  rw [charFun_gaussianReal]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Consequently, the unrestricted terminal distance from a barrier started
at `x` is Gaussian with mean `x` and variance `n`. -/
theorem map_gaussianWalkTerminalDistance_eq (n : ℕ) (x : ℝ) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map
        (gaussianWalkTerminalDistance n x) =
      gaussianReal x (n : ℝ≥0) := by
  let S : (Fin n → ℝ) → ℝ := fun omega ↦ ∑ i, omega i
  have hfun : gaussianWalkTerminalDistance n x = (fun z ↦ x - z) ∘ S := by
    funext omega
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    show (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map S =
      gaussianReal 0 (n : ℝ≥0) by simpa only [S] using! map_gaussianWalk_sum_eq n,
    gaussianReal_map_const_sub]
  simp only [sub_zero]

theorem gaussianWalkTerminalDistance_nonneg_of_survives
    (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) (hx : 0 ≤ x)
    (h : gaussianWalkSurvives n x omega) :
    0 ≤ gaussianWalkTerminalDistance n x omega := by
  induction n generalizing x with
  | zero =>
      simpa [gaussianWalkTerminalDistance] using! hx
  | succ n ih =>
      have htail := ih (x - omega 0) (fun i ↦ omega i.succ)
        (sub_nonneg.mpr h.1) h.2
      simp only [gaussianWalkTerminalDistance] at htail ⊢
      rw [Fin.sum_univ_succ]
      linarith

/-- The measurable finite-path survival event. -/
def gaussianWalkSurvivalSet (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {omega | gaussianWalkSurvives n x omega}

theorem measurableSet_gaussianWalkSurvivalSet (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    MeasurableSet (gaussianWalkSurvivalSet n x) := by
  have heq : gaussianWalkSurvivalSet n x =
      gaussianWalkKilledPayoff n x ⁻¹' Ioi 0 := by
    ext omega
    simp only [gaussianWalkSurvivalSet, mem_ofPred_eq, mem_preimage, mem_Ioi]
    constructor
    · intro h
      rw [gaussianWalkKilledPayoff_eq_of_survives n x omega h]
      linarith [gaussianWalkTerminalDistance_nonneg_of_survives n x omega hx h]
    · intro hpos
      by_contra hsurv
      rw [gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega hsurv]
        at hpos
      linarith
  rw [heq]
  exact (measurable_gaussianWalkKilledPayoff n x) measurableSet_Ioi

theorem integrable_gaussianWalkTerminalDistance (n : ℕ) (x : ℝ) :
    Integrable (gaussianWalkTerminalDistance n x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  have heval (i : Fin n) : Integrable
      (fun omega : Fin n → ℝ ↦ omega i)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    exact integrable_eval integrable_id_gaussianReal_zero_one
  unfold gaussianWalkTerminalDistance
  have hsum : Integrable (fun omega : Fin n → ℝ ↦ ∑ i, omega i)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    exact integrable_finsetSum Finset.univ fun i _hi ↦ heval i
  exact (integrable_const (μ :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) x).sub hsum

/-- The killed-potential recursion is the affine terminal moment on the
actual survival event. -/
theorem integralOn_gaussianWalkSurvival_terminal_eq (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ omega in gaussianWalkSurvivalSet n x,
        (gaussianWalkTerminalDistance n x omega + 2)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
      gaussianKilledPotential n x := by
  calc
    (∫ omega in gaussianWalkSurvivalSet n x,
        (gaussianWalkTerminalDistance n x omega + 2)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
        ∫ omega : Fin n → ℝ,
          gaussianWalkKilledPayoff n x omega
          ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      rw [← integral_indicator (measurableSet_gaussianWalkSurvivalSet n hx)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianWalkSurvives n x omega
        · have hmem : omega ∈ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_mem hmem,
            gaussianWalkKilledPayoff_eq_of_survives n x omega h]
        · have hmem : omega ∉ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_notMem hmem,
            gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega h]
    _ = gaussianKilledPotential n x :=
      integral_gaussianWalkKilledPayoff_eq n x

/-- Terminal-density completion of the soft barrier argument.  If the
unrestricted endpoint has Gaussian law and the killed affine potential has
expectation at most its initial value, splitting at terminal distance `r`
gives the displayed near/far estimate. -/
theorem measureReal_gaussianWalk_barrier_le
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤ (x + 2) / r + r / Real.sqrt (v : ℝ) := by
  let near : Set Omega := D ⁻¹' Icc 0 r
  have hnear : MeasurableSet near := hDmeas measurableSet_Icc
  have hfar : ∀ omega ∈ A \ near, r ≤ D omega + 2 := by
    intro omega homega
    have hD0 : 0 ≤ D omega := hDnonneg omega homega.1
    have hnot : D omega ∉ Icc (0 : ℝ) r := homega.2
    have hrD : r < D omega := by
      by_contra h
      exact hnot ⟨hD0, le_of_not_gt h⟩
    linarith
  have hnearMass : P.real (A ∩ near) ≤
      r * (1 / Real.sqrt (v : ℝ)) := by
    calc
      P.real (A ∩ near) ≤ P.real near :=
        measureReal_mono inter_subset_right
      _ = (P.map D).real (Icc 0 r) := by
        exact (map_measureReal_apply hDmeas measurableSet_Icc).symm
      _ = (gaussianReal x v).real (Icc 0 r) := by rw [hlaw]
      _ ≤ r / Real.sqrt (v : ℝ) := by
        simpa only [sub_zero] using!
          gaussianReal_real_Icc_le_inv_sqrt x hv hr.le
      _ = r * (1 / Real.sqrt (v : ℝ)) := by ring
  have hsplit := measureReal_barrier_le_of_terminal_split P hA hnear hr
    (D := fun omega ↦ D omega + 2)
    (fun omega homega ↦ by linarith [hDnonneg omega homega])
    hDintegrable hfar hweighted hnearMass
  simpa only [div_eq_mul_inv, one_mul] using! hsplit

/-- Optimized fourth-root form of `measureReal_gaussianWalk_barrier_le`.
The loss `v⁻¹/⁴` is weaker than the sharp Gaussian ballot exponent but is
already a genuine polynomial survival saving. -/
theorem measureReal_gaussianWalk_barrier_le_fourthRoot
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤
      (x + 3) / Real.sqrt (Real.sqrt (v : ℝ)) := by
  have hvreal : 0 < (v : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvreal
  have hr : 0 < Real.sqrt (Real.sqrt (v : ℝ)) :=
    Real.sqrt_pos.2 hsqrt
  have hbase := measureReal_gaussianWalk_barrier_le P hA hDmeas hv hr
    hlaw hDnonneg hDintegrable hweighted
  calc
    P.real A ≤
        (x + 2) / Real.sqrt (Real.sqrt (v : ℝ)) +
          Real.sqrt (Real.sqrt (v : ℝ)) / Real.sqrt (v : ℝ) := hbase
    _ = (x + 3) / Real.sqrt (Real.sqrt (v : ℝ)) := by
      have hsquare : (Real.sqrt (Real.sqrt (v : ℝ))) ^ 2 =
          Real.sqrt (v : ℝ) := Real.sq_sqrt hsqrt.le
      field_simp [hr.ne', hsqrt.ne']
      nlinarith

/-- The genuinely optimized near/far split.  Its square-root dependence on
the starting potential is the form suitable for a dyadic Markov bootstrap. -/
theorem measureReal_gaussianWalk_barrier_le_optimized
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} (hx : 0 ≤ x) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤
      2 * Real.sqrt (x + 2) / Real.sqrt (Real.sqrt (v : ℝ)) := by
  let a : ℝ := x + 2
  let b : ℝ := Real.sqrt (v : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  have hvreal : 0 < (v : ℝ) := by positivity
  have hb : 0 < b := by exact Real.sqrt_pos.2 hvreal
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hr : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hbase := measureReal_gaussianWalk_barrier_le P hA hDmeas hv hr
    hlaw hDnonneg hDintegrable hweighted
  have hsqrtMul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha.le]
  calc
    P.real A ≤ a / Real.sqrt (a * b) + Real.sqrt (a * b) / b := by
      simpa only [a, b] using! hbase
    _ = 2 * Real.sqrt a / Real.sqrt b := by
      rw [hsqrtMul]
      have hsaSq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
      have hsbSq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
      field_simp [hsa.ne', hsb.ne', hb.ne']
      nlinarith
    _ = 2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (v : ℝ)) := by rfl

/-- Unconditional finite-walk soft ballot estimate. -/
theorem gaussianWalk_survival_probability_le_fourthRoot
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n x) ≤
      2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) := by
  let Pn : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  let D : (Fin n → ℝ) → ℝ := gaussianWalkTerminalDistance n x
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hDmeas : Measurable D := by
    unfold D gaussianWalkTerminalDistance
    fun_prop
  have hlaw : Pn.map D = gaussianReal x (n : ℝ≥0) := by
    simpa only [Pn, D] using! map_gaussianWalkTerminalDistance_eq n x
  have hnonneg : ∀ omega ∈ gaussianWalkSurvivalSet n x, 0 ≤ D omega := by
    intro omega homega
    exact gaussianWalkTerminalDistance_nonneg_of_survives n x omega hx homega
  have hint : IntegrableOn (fun omega ↦ D omega + 2)
      (gaussianWalkSurvivalSet n x) Pn := by
    have hfull : Integrable (fun omega : Fin n → ℝ ↦
        gaussianWalkTerminalDistance n x omega + 2)
        (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) :=
      (integrable_gaussianWalkTerminalDistance n x).add
        (integrable_const (μ :=
          Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) 2)
    simpa only [Pn, D] using! hfull.integrableOn
  have hweighted : (∫ omega in gaussianWalkSurvivalSet n x,
      (D omega + 2) ∂Pn) ≤ x + 2 := by
    have heq := integralOn_gaussianWalkSurvival_terminal_eq n hx
    rw [show (∫ omega in gaussianWalkSurvivalSet n x,
        (D omega + 2) ∂Pn) = gaussianKilledPotential n x by
          simpa only [Pn, D] using! heq]
    exact gaussianKilledPotential_le n hx
  simpa only [Pn, NNReal.coe_natCast] using!
    (measureReal_gaussianWalk_barrier_le_optimized Pn
      (measurableSet_gaussianWalkSurvivalSet n hx) hDmeas
      (x := x) hx (v := (n : ℝ≥0)) hv hlaw hnonneg hint hweighted)

/-! ## Constant-variance rescaling -/

theorem gaussianWalkSurvives_div_iff
    (n : ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) (omega : Fin n → ℝ) :
    gaussianWalkSurvives n x omega ↔
      gaussianWalkSurvives n (x / s) (fun i ↦ omega i / s) := by
  induction n generalizing x with
  | zero => simp only [gaussianWalkSurvives]
  | succ n ih =>
      simp only [gaussianWalkSurvives]
      constructor
      · rintro ⟨hfirst, htail⟩
        refine ⟨(div_le_div_iff_of_pos_right hs).2 hfirst, ?_⟩
        simpa only [sub_div] using!
          (ih (x - omega 0) (fun i ↦ omega i.succ)).1 htail
      · rintro ⟨hfirst, htail⟩
        refine ⟨(div_le_div_iff_of_pos_right hs).1 hfirst, ?_⟩
        exact (ih (x - omega 0) (fun i ↦ omega i.succ)).2
          (by simpa only [sub_div] using! htail)

theorem gaussianReal_map_div_sqrt_variance
    {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).map
        (fun z ↦ z / Real.sqrt (v : ℝ)) =
      gaussianReal 0 1 := by
  have hvreal : 0 < (v : ℝ) := by positivity
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvreal
  rw [gaussianReal_map_div_const]
  have hvar : v / NNReal.mk (Real.sqrt (v : ℝ) ^ 2)
      (sq_nonneg _) = 1 := by
    ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt hvreal.le]
    exact div_self hvreal.ne'
  rw [hvar]
  simp only [zero_div]

theorem map_gaussianWalk_div_sqrt_variance
    (n : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).map
        (fun omega i ↦ omega i / Real.sqrt (v : ℝ)) =
      Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
  let f : (i : Fin n) → ℝ → ℝ :=
    fun _ z ↦ z / Real.sqrt (v : ℝ)
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin n ↦ gaussianReal 0 v) (f := f)
    (fun _ ↦ (by fun_prop))
  calc
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).map
        (fun omega i ↦ omega i / Real.sqrt (v : ℝ)) =
        Measure.pi (fun i : Fin n ↦
          (gaussianReal 0 v).map (f i)) := by
      simpa only [f] using! hpi
    _ = Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      have hfun : (fun i : Fin n ↦ (gaussianReal 0 v).map (f i)) =
          (fun _ : Fin n ↦ gaussianReal 0 1) := by
        funext i
        simpa only [f] using! gaussianReal_map_div_sqrt_variance hv
      rw [hfun]

/-- The fourth-root bound for iid centered Gaussians of any fixed nonzero variance. -/
theorem gaussianWalk_fixedVariance_survival_probability_le_fourthRoot
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x)
    {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).real
        (gaussianWalkSurvivalSet n x) ≤
      2 * Real.sqrt (x / Real.sqrt (v : ℝ) + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun omega i ↦ omega i / s
  let Pv : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 v
  have hvreal : 0 < (v : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hvreal
  have hF : Measurable F := by
    unfold F
    fun_prop
  have hset : F ⁻¹' gaussianWalkSurvivalSet n (x / s) =
      gaussianWalkSurvivalSet n x := by
    ext omega
    exact (gaussianWalkSurvives_div_iff n hs x omega).symm
  calc
    Pv.real (gaussianWalkSurvivalSet n x) =
        (Pv.map F).real (gaussianWalkSurvivalSet n (x / s)) := by
      rw [map_measureReal_apply hF
        (measurableSet_gaussianWalkSurvivalSet n (div_nonneg hx hs.le))]
      rw [hset]
    _ = (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n (x / s)) := by
      rw [show Pv.map F =
          Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) by
        simpa only [Pv, F, s] using! map_gaussianWalk_div_sqrt_variance n hv]
    _ ≤ 2 * Real.sqrt (x / s + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) :=
      gaussianWalk_survival_probability_le_fourthRoot n hn (div_nonneg hx hs.le)
    _ = 2 * Real.sqrt (x / Real.sqrt (v : ℝ) + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) := rfl

/-- Removing the first coordinate from a prefix sum leaves the corresponding tail prefix. -/
theorem gaussianWalk_prefix_sum_succ {n : ℕ} (omega : Fin (n + 1) → ℝ) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) ↦ i ≤ j.succ), omega i) =
      omega 0 + ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i ≤ j), omega i.succ := by
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.zero_le, ↓reduceIte,
    Fin.succ_le_succ_iff]

/-- Recursive survival is equivalent to every finite prefix sum staying below the barrier. -/
theorem gaussianWalkSurvives_iff_prefix_sums
    (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) :
    gaussianWalkSurvives n x omega ↔
      ∀ j, ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i ≤ j), omega i ≤ x := by
  induction n generalizing x with
  | zero => simp [gaussianWalkSurvives]
  | succ n ih =>
      rw [gaussianWalkSurvives]
      constructor
      · rintro ⟨hfirst, htail⟩ j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simpa [Finset.sum_filter, Fin.sum_univ_succ] using hfirst
        · rw [gaussianWalk_prefix_sum_succ]
          have hk := (ih (x - omega 0) (fun i ↦ omega i.succ)).1 htail k
          linarith
      · intro h
        constructor
        · simpa [Finset.sum_filter, Fin.sum_univ_succ] using h 0
        · apply (ih (x - omega 0) (fun i ↦ omega i.succ)).2
          intro j
          have hj := h j.succ
          rw [gaussianWalk_prefix_sum_succ] at hj
          linarith


end
end NormalNumbers.ErdosBorweinEndpointEKAux
