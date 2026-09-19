import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NormalNumbers.RealDefs

/-!
# Weyl's criterion (obligation W3 of DESIGN-2026-09-19-bcr-wiring.md)

If every nonzero Fourier mean of a `[0,1)`-valued sequence vanishes, the sequence
is equidistributed in the sense of `NormalNumbers.Equidistributed` (visit
frequency of every `[a, c) ⊆ [0, 1)` tends to `c − a`).

Route: fix `[a, c)`; squeeze its indicator between continuous functions on
`AddCircle 1` built from the circle norm (`‖y - m‖` with `m` the midpoint), whose
integrals are within `2δ` of `c − a`; approximate any continuous circle function
uniformly by a trigonometric polynomial using `span_fourier_closure_eq_top`; the
Fourier hypothesis makes the Cesàro mean of every nonconstant `fourier n` vanish,
so the mean of a trig polynomial tends to its integral; finish with `ε/3`.
No number theory: this file is pure analysis.
-/

open Filter Topology Complex MeasureTheory intervalIntegral

namespace NormalNumbers

/-- The `h`-th Fourier mean of the first `n` terms of `u`. -/
noncomputable def fourierMean (u : ℕ → ℝ) (h : ℤ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (u k : ℂ))) / n

section Analysis

/-- Cesàro mean of `f` along the circle projection of `u`. -/
noncomputable def cMean (u : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, f ((u k : ℝ) : AddCircle (1 : ℝ))) / n

/-- Integral of a circle function over one period. -/
noncomputable def cInt (f : C(AddCircle (1 : ℝ), ℂ)) : ℂ :=
  ∫ x in (0 : ℝ)..1, f ((x : ℝ) : AddCircle (1 : ℝ))

/-- The set of continuous functions whose Cesàro means converge to the integral. -/
def CGood (u : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
  Tendsto (cMean u f) atTop (𝓝 (cInt f))

lemma continuous_comp_coe (f : C(AddCircle (1 : ℝ), ℂ)) :
    Continuous fun x : ℝ => f ((x : ℝ) : AddCircle (1 : ℝ)) :=
  f.continuous.comp (AddCircle.continuous_mk' 1)

lemma intervalIntegrable_comp_coe (f : C(AddCircle (1 : ℝ), ℂ)) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℝ) : AddCircle (1 : ℝ))) volume a b :=
  (continuous_comp_coe f).intervalIntegrable a b

lemma cInt_add (f g : C(AddCircle (1 : ℝ), ℂ)) : cInt (f + g) = cInt f + cInt g := by
  simp only [cInt, ContinuousMap.add_apply]
  exact intervalIntegral.integral_add (intervalIntegrable_comp_coe f 0 1)
    (intervalIntegrable_comp_coe g 0 1)

lemma cInt_smul (a : ℂ) (f : C(AddCircle (1 : ℝ), ℂ)) : cInt (a • f) = a * cInt f := by
  simp only [cInt, ContinuousMap.smul_apply, smul_eq_mul]
  exact intervalIntegral.integral_const_mul _ _

lemma cMean_add (u : ℕ → ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) :
    cMean u (f + g) n = cMean u f n + cMean u g n := by
  simp only [cMean, ContinuousMap.add_apply, Finset.sum_add_distrib]
  ring

lemma cMean_smul (u : ℕ → ℝ) (a : ℂ) (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) :
    cMean u (a • f) n = a * cMean u f n := by
  simp only [cMean, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `‖cMean u f n‖ ≤ ‖f‖`. -/
lemma norm_cMean_le (u : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) :
    ‖cMean u f n‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [cMean, h, norm_nonneg]
  · rw [cMean, norm_div]
    have hn : (0:ℝ) < ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast h
    rw [div_le_iff₀ hn]
    calc ‖∑ k ∈ Finset.range n, f ((u k : ℝ) : AddCircle (1 : ℝ))‖
        ≤ ∑ _k ∈ Finset.range n, ‖f‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => f.norm_coe_le_norm _)
      _ = ‖f‖ * n := by simp [mul_comm]
      _ = ‖f‖ * ‖(n : ℂ)‖ := by simp

lemma norm_cInt_le (f : C(AddCircle (1 : ℝ), ℂ)) : ‖cInt f‖ ≤ ‖f‖ := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := ‖f‖)
    (f := fun x : ℝ => f ((x : ℝ) : AddCircle (1 : ℝ)))
    (fun x _ => f.norm_coe_le_norm _)
  simpa [cInt] using this

lemma cInt_fourier_ne (h : ℤ) (hh : h ≠ 0) : cInt (fourier h) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hh]
  have hx : ∀ x : ℝ, (fourier h) ((x : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) * (x : ℂ)) := by
    intro x
    rw [fourier_coe_apply]
    norm_num
  rw [cInt]
  simp only [hx]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (1 : ℝ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I h
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((1:ℝ) : ℂ))
        = (h : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact this
  rw [h1]
  simp

lemma cInt_fourier_zero : cInt (fourier (T := (1:ℝ)) 0) = 1 := by
  simp [cInt, fourier_zero]

lemma cMean_eq_fourierMean (u : ℕ → ℝ) (h : ℤ) (n : ℕ) :
    cMean u (fourier h) n = fourierMean u h n := by
  rw [cMean, fourierMean]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourier_coe_apply]
  norm_num

lemma cgood_fourier (u : ℕ → ℝ) (h : ℤ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0)) :
    CGood u (fourier h) := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [CGood, cInt_fourier_zero]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℂ)) (f := atTop (α := ℕ)))
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : ((n : ℂ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    simp [cMean, div_self hn']
  · rw [CGood, cInt_fourier_ne h hh]
    have : cMean u (fourier h) = fourierMean u h := funext fun n => cMean_eq_fourierMean u h n
    rw [this]
    exact hW h hh

lemma cgood_span (u : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0))
    {f : C(AddCircle (1 : ℝ), ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : CGood u f := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨h, rfl⟩ := hx; exact cgood_fourier u h hW
  | zero =>
      have h0 : cMean u (0 : C(AddCircle (1:ℝ), ℂ)) = fun _ => (0:ℂ) := by
        funext n; simp [cMean]
      rw [CGood, h0]
      simpa [cInt] using tendsto_const_nhds (x := (0:ℂ)) (f := atTop (α := ℕ))
  | add x y _ _ hx hy =>
      have : cMean u (x + y) = fun n => cMean u x n + cMean u y n :=
        funext fun n => cMean_add u x y n
      rw [CGood, this, cInt_add]
      exact hx.add hy
  | smul a x _ hx =>
      have : cMean u (a • x) = fun n => a * cMean u x n :=
        funext fun n => cMean_smul u a x n
      rw [CGood, this, cInt_smul]
      exact hx.const_mul a

/-- Every continuous function on the circle has Cesàro means converging to its
integral: the `ε/3` argument against a trigonometric approximation. -/
lemma cgood_all (u : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0))
    (f : C(AddCircle (1 : ℝ), ℂ)) : CGood u f := by
  rw [CGood, Metric.tendsto_atTop]
  intro ε hε
  have hdense : f ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1:ℝ)))) : Set _) := by
    have := span_fourier_closure_eq_top (T := (1:ℝ))
    have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))).topologicalClosure := by
      rw [this]; trivial
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨P, hPmem, hP⟩ := Metric.mem_closure_iff.mp hdense (ε / 3) (by linarith)
  have hPgood := cgood_span u hW hPmem
  rw [CGood, Metric.tendsto_atTop] at hPgood
  obtain ⟨N, hN⟩ := hPgood (ε / 3) (by linarith)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnorm : ‖f - P‖ < ε / 3 := by rwa [← dist_eq_norm]
  have h1 : ‖cMean u f n - cMean u P n‖ < ε / 3 := by
    have : cMean u f n - cMean u P n = cMean u (f - P) n := by
      simp [cMean, ContinuousMap.sub_apply, Finset.sum_sub_distrib, sub_div]
    rw [this]
    exact lt_of_le_of_lt (norm_cMean_le u (f - P) n) hnorm
  have h2 : ‖cInt P - cInt f‖ < ε / 3 := by
    have : cInt P - cInt f = cInt (P - f) := by
      simp only [cInt, ContinuousMap.sub_apply]
      rw [intervalIntegral.integral_sub (intervalIntegrable_comp_coe P 0 1)
        (intervalIntegrable_comp_coe f 0 1)]
    rw [this]
    refine lt_of_le_of_lt (norm_cInt_le (P - f)) ?_
    rwa [show P - f = -(f - P) by ring, norm_neg]
  have h3 : dist (cMean u P n) (cInt P) < ε / 3 := hN n (le_trans (le_max_left _ _) hn)
  rw [dist_eq_norm] at h3 ⊢
  calc ‖cMean u f n - cInt f‖
      = ‖(cMean u f n - cMean u P n) + (cMean u P n - cInt P) + (cInt P - cInt f)‖ := by
        congr 1; ring
    _ ≤ ‖cMean u f n - cMean u P n‖ + ‖cMean u P n - cInt P‖ + ‖cInt P - cInt f‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

/-- Real-valued form of `cgood_all`. -/
lemma cgood_real (u : ℕ → ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0))
    (g : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, g ((u k : ℝ) : AddCircle (1 : ℝ))) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, g ((x : ℝ) : AddCircle (1 : ℝ)))) := by
  set f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun y => ((g y : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ with hf
  have hmean : ∀ n : ℕ, (cMean u f n).re
      = (∑ k ∈ Finset.range n, g ((u k : ℝ) : AddCircle (1 : ℝ))) / n := by
    intro n
    rw [cMean]
    have : (∑ k ∈ Finset.range n, f ((u k : ℝ) : AddCircle (1 : ℝ)))
        = ((∑ k ∈ Finset.range n, g ((u k : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
      push_cast [hf]; rfl
    rw [this, ← Complex.ofReal_natCast n, ← Complex.ofReal_div, Complex.ofReal_re]
  have hint : (cInt f).re = ∫ x in (0 : ℝ)..1, g ((x : ℝ) : AddCircle (1 : ℝ)) := by
    have h := intervalIntegral_re (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := fun x : ℝ => f ((x : ℝ) : AddCircle (1 : ℝ))) (intervalIntegrable_comp_coe f 0 1)
    rw [cInt, show ((∫ x in (0:ℝ)..1, f ((x : ℝ) : AddCircle (1 : ℝ))).re)
      = RCLike.re (∫ x in (0:ℝ)..1, f ((x : ℝ) : AddCircle (1 : ℝ))) from rfl, ← h]
    simp [hf]
  have := (Complex.continuous_re.tendsto (cInt f)).comp (cgood_all u hW f)
  simp only [Function.comp_def, hmean, hint] at this
  exact this

section Trapezoid

/-- Continuous upper trapezoid for the arc `[a, c)` on the circle: `1` on the arc,
`0` at circle-distance `≥ δ` from it. -/
noncomputable def trapUp (a c δ : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun y => min 1 (max 0 (((c - a) / 2 + δ - ‖y - (((a + c) / 2 : ℝ) : AddCircle (1 : ℝ))‖) / δ)),
    by fun_prop⟩

/-- Continuous lower trapezoid for the arc `[a, c)`: `0` outside the arc. -/
noncomputable def trapLo (a c δ : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun y => min 1 (max 0 (((c - a) / 2 - ‖y - (((a + c) / 2 : ℝ) : AddCircle (1 : ℝ))‖) / δ)),
    by fun_prop⟩

lemma trapUp_nonneg (a c δ : ℝ) (hδ : 0 < δ) (y : AddCircle (1 : ℝ)) : 0 ≤ trapUp a c δ y := by
  simp only [trapUp, ContinuousMap.coe_mk, le_min_iff]
  exact ⟨zero_le_one, le_max_left _ _⟩

lemma trapUp_le_one (a c δ : ℝ) (y : AddCircle (1 : ℝ)) : trapUp a c δ y ≤ 1 :=
  min_le_left _ _

lemma trapLo_nonneg (a c δ : ℝ) (y : AddCircle (1 : ℝ)) : 0 ≤ trapLo a c δ y := by
  simp only [trapLo, ContinuousMap.coe_mk, le_min_iff]
  exact ⟨zero_le_one, le_max_left _ _⟩

lemma trapLo_le_one (a c δ : ℝ) (y : AddCircle (1 : ℝ)) : trapLo a c δ y ≤ 1 :=
  min_le_left _ _

/-- The circle norm of `↑x - ↑m` equals `|x - m|` on the fundamental interval centred at `m`. -/
lemma norm_coe_sub (m x : ℝ) (hx : |x - m| ≤ 1 / 2) :
    ‖((x : ℝ) : AddCircle (1 : ℝ)) - ((m : ℝ) : AddCircle (1 : ℝ))‖ = |x - m| := by
  rw [← AddCircle.coe_sub]
  rw [AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero]
  simpa using hx

/-- Circle norm as a distance to the nearest integer. -/
lemma norm_coe_ge (t : ℝ) (r : ℝ) (h : ∀ k : ℤ, r ≤ |t - k|) :
    r ≤ ‖((t : ℝ) : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq (p := (1:ℝ))]
  simpa using h (round t)

lemma norm_coe_le (t : ℝ) : ‖((t : ℝ) : AddCircle (1 : ℝ))‖ ≤ |t| := by
  rw [AddCircle.norm_eq (p := (1:ℝ))]
  have := round_le t 0
  simpa using this

lemma continuousR_comp (g : C(AddCircle (1 : ℝ), ℝ)) :
    Continuous fun x : ℝ => g ((x : ℝ) : AddCircle (1 : ℝ)) :=
  g.continuous.comp (AddCircle.continuous_mk' 1)

lemma intIntegrableR (g : C(AddCircle (1 : ℝ), ℝ)) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => g ((x : ℝ) : AddCircle (1 : ℝ))) volume a b :=
  (continuousR_comp g).intervalIntegrable a b

lemma periodicR (g : C(AddCircle (1 : ℝ), ℝ)) :
    Function.Periodic (fun x : ℝ => g ((x : ℝ) : AddCircle (1 : ℝ))) 1 := by
  intro x
  simp [AddCircle.coe_add_period]

lemma intR_shift (g : C(AddCircle (1 : ℝ), ℝ)) (t : ℝ) :
    (∫ x in (0:ℝ)..1, g ((x : ℝ) : AddCircle (1 : ℝ)))
      = ∫ x in t..t+1, g ((x : ℝ) : AddCircle (1 : ℝ)) := by
  simpa using ((periodicR g).intervalIntegral_add_eq t 0).symm

lemma trapUp_apply_of_close (a c δ x : ℝ) (hx : |x - (a + c) / 2| ≤ 1 / 2) :
    trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ))
      = min 1 (max 0 (((c - a) / 2 + δ - |x - (a + c) / 2|) / δ)) := by
  simp only [trapUp, ContinuousMap.coe_mk]
  rw [norm_coe_sub _ _ hx]

lemma trapLo_apply_of_close (a c δ x : ℝ) (hx : |x - (a + c) / 2| ≤ 1 / 2) :
    trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ))
      = min 1 (max 0 (((c - a) / 2 - |x - (a + c) / 2|) / δ)) := by
  simp only [trapLo, ContinuousMap.coe_mk]
  rw [norm_coe_sub _ _ hx]

/-- Upper trapezoid: integral at most `(c - a) + 2δ`. -/
lemma integral_trapUp_le (a c δ : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hδ : 0 < δ) :
    (∫ x in (0:ℝ)..1, trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ))) ≤ (c - a) + 2 * δ := by
  by_cases hbig : 1 / 2 ≤ (c - a) / 2 + δ
  · have h1 : (∫ x in (0:ℝ)..1, trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ)))
        ≤ ∫ _x in (0:ℝ)..1, (1:ℝ) := by
      refine intervalIntegral.integral_mono_on (by norm_num) (intIntegrableR _ _ _)
        intervalIntegrable_const (fun x _ => trapUp_le_one a c δ _)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h1
    linarith
  · push_neg at hbig
    set m : ℝ := (a + c) / 2 with hm
    set r : ℝ := (c - a) / 2 with hr
    have hr0 : 0 ≤ r := by rw [hr]; linarith
    have hAB : m - 1/2 ≤ m - r - δ := by linarith
    have hBC : m - r - δ ≤ m + r + δ := by linarith
    have hCD : m + r + δ ≤ m + 1/2 := by linarith
    have hzero : ∀ x : ℝ, |x - m| ≤ 1/2 → r + δ ≤ |x - m| →
        trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      intro x hx1 hx2
      rw [trapUp_apply_of_close a c δ x (by rw [← hm]; exact hx1), ← hm, ← hr]
      have : ((r + δ - |x - m|) / δ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      rw [max_eq_left this]
      exact min_eq_right zero_le_one
    have e1 : (∫ x in (m - 1/2)..(m - r - δ), trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ))) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [Set.uIcc_of_le hAB] at hx
      exact hzero x (by rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]])
        (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2])
    have e3 : (∫ x in (m + r + δ)..(m + 1/2), trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ))) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [Set.uIcc_of_le hCD] at hx
      exact hzero x (by rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]])
        (by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])
    have e2 : (∫ x in (m - r - δ)..(m + r + δ), trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ)))
        ≤ 2 * r + 2 * δ := by
      have := intervalIntegral.integral_mono_on hBC (intIntegrableR (trapUp a c δ) _ _)
        (intervalIntegrable_const (c := (1:ℝ))) (fun x _ => trapUp_le_one a c δ _)
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
      linarith
    have hs1 := intervalIntegral.integral_add_adjacent_intervals
      (a := m - 1/2) (b := m - r - δ) (c := m + r + δ)
      (intIntegrableR (trapUp a c δ) _ _) (intIntegrableR (trapUp a c δ) _ _)
    have hs2 := intervalIntegral.integral_add_adjacent_intervals
      (a := m - 1/2) (b := m + r + δ) (c := m + 1/2)
      (intIntegrableR (trapUp a c δ) _ _) (intIntegrableR (trapUp a c δ) _ _)
    have hshift := intR_shift (trapUp a c δ) (m - 1/2)
    have hend : m - 1/2 + 1 = m + 1/2 := by ring
    rw [hend] at hshift
    rw [hshift, ← hs2, ← hs1, e1, e3]
    have : c - a = 2 * r := by rw [hr]; ring
    linarith

/-- Lower trapezoid: integral at least `(c - a) - 2δ`. -/
lemma le_integral_trapLo (a c δ : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hδ : 0 < δ) :
    (c - a) - 2 * δ ≤ ∫ x in (0:ℝ)..1, trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) := by
  by_cases hsmall : (c - a) / 2 ≤ δ
  · have h0 : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => trapLo_nonneg a c δ _)
    linarith
  · push_neg at hsmall
    set m : ℝ := (a + c) / 2 with hm
    set r : ℝ := (c - a) / 2 with hr
    have hr2 : r ≤ 1/2 := by rw [hr]; linarith
    have hAB : m - 1/2 ≤ m - r + δ := by linarith
    have hBC : m - r + δ ≤ m + r - δ := by linarith
    have hCD : m + r - δ ≤ m + 1/2 := by linarith
    have hone : ∀ x : ℝ, |x - m| ≤ r - δ → trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) = 1 := by
      intro x hx
      have hx1 : |x - m| ≤ 1/2 := by linarith
      rw [trapLo_apply_of_close a c δ x (by rw [← hm]; exact hx1), ← hm, ← hr]
      have h1 : (1:ℝ) ≤ (r - |x - m|) / δ := by
        rw [le_div_iff₀ hδ]; linarith
      rw [max_eq_right (by linarith : (0:ℝ) ≤ (r - |x - m|) / δ)]
      exact min_eq_left h1
    have e2 : (∫ x in (m - r + δ)..(m + r - δ), trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)))
        = 2 * r - 2 * δ := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      · intro x hx
        rw [Set.uIcc_of_le hBC] at hx
        refine hone x ?_
        rw [abs_le]
        constructor <;> [linarith [hx.1]; linarith [hx.2]]
    have e1 : (0:ℝ) ≤ ∫ x in (m - 1/2)..(m - r + δ), trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) :=
      intervalIntegral.integral_nonneg hAB (fun x _ => trapLo_nonneg a c δ _)
    have e3 : (0:ℝ) ≤ ∫ x in (m + r - δ)..(m + 1/2), trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) :=
      intervalIntegral.integral_nonneg hCD (fun x _ => trapLo_nonneg a c δ _)
    have hs1 := intervalIntegral.integral_add_adjacent_intervals
      (a := m - 1/2) (b := m - r + δ) (c := m + r - δ)
      (intIntegrableR (trapLo a c δ) _ _) (intIntegrableR (trapLo a c δ) _ _)
    have hs2 := intervalIntegral.integral_add_adjacent_intervals
      (a := m - 1/2) (b := m + r - δ) (c := m + 1/2)
      (intIntegrableR (trapLo a c δ) _ _) (intIntegrableR (trapLo a c δ) _ _)
    have hshift := intR_shift (trapLo a c δ) (m - 1/2)
    have hend : m - 1/2 + 1 = m + 1/2 := by ring
    rw [hend] at hshift
    rw [hshift, ← hs2, ← hs1, e2]
    have : c - a = 2 * r := by rw [hr]; ring
    linarith

/-- Distance from a point outside the arc to every integer translate of the midpoint. -/
lemma le_abs_sub_int (a c x : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hnot : ¬ (a ≤ x ∧ x < c)) (k : ℤ) :
    (c - a) / 2 ≤ |x - (a + c) / 2 - (k : ℝ)| := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · subst hk
    rcases not_and_or.mp hnot with h | h
    · have hxa : x < a := lt_of_not_ge h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hxc : c ≤ x := le_of_not_gt h
      rw [abs_of_nonneg (by linarith)]
      linarith
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1:ℤ) ≤ k)
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma trapUp_ge_indicator (a c δ x : ℝ) (hδ : 0 < δ) (hx : a ≤ x ∧ x < c) :
    (1 : ℝ) ≤ trapUp a c δ ((x : ℝ) : AddCircle (1 : ℝ)) := by
  have hnorm : ‖((x : ℝ) : AddCircle (1 : ℝ)) - (((a + c) / 2 : ℝ) : AddCircle (1 : ℝ))‖
      ≤ (c - a) / 2 := by
    rw [← AddCircle.coe_sub]
    refine (norm_coe_le _).trans ?_
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  simp only [trapUp, ContinuousMap.coe_mk, le_min_iff]
  refine ⟨le_refl _, ?_⟩
  refine le_max_of_le_right ?_
  rw [le_div_iff₀ hδ]
  linarith

lemma trapLo_eq_zero_outside (a c δ x : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hnot : ¬ (a ≤ x ∧ x < c)) (hδ : 0 < δ) :
    trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have hnorm : (c - a) / 2
      ≤ ‖((x : ℝ) : AddCircle (1 : ℝ)) - (((a + c) / 2 : ℝ) : AddCircle (1 : ℝ))‖ := by
    rw [← AddCircle.coe_sub]
    refine norm_coe_ge _ _ fun k => ?_
    have := le_abs_sub_int a c x ha hac hc hx0 hx1 hnot k
    rwa [show x - (a + c) / 2 - (k : ℝ) = x - (a + c) / 2 - (k : ℝ) from rfl] at this
  simp only [trapLo, ContinuousMap.coe_mk]
  have h1 : ((c - a) / 2 - ‖((x : ℝ) : AddCircle (1 : ℝ))
      - (((a + c) / 2 : ℝ) : AddCircle (1 : ℝ))‖) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [max_eq_left h1]
  exact min_eq_right zero_le_one

end Trapezoid

end Analysis

/-- **Weyl's criterion**, the direction used by the normality wiring: vanishing
Fourier means at every nonzero frequency give equidistribution. -/
theorem equidistributed_of_weyl (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0)) :
    Equidistributed u := by
  intro a c ha hac hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hupT := cgood_real u hW (trapUp a c δ)
  have hloT := cgood_real u hW (trapLo a c δ)
  rw [Metric.tendsto_atTop] at hupT hloT
  obtain ⟨N1, hN1⟩ := hupT (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hloT (ε / 4) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn1
  -- the visit count is the sum of the indicator
  have hcard : (visitCount u a c n : ℝ)
      = ∑ k ∈ Finset.range n, (if (a ≤ u k ∧ u k < c) then (1:ℝ) else 0) := by
    rw [visitCount]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : a ≤ u k ∧ u k < c
    · simp [Set.mem_Ico, h.1, h.2]
    · simp [Set.mem_Ico, h]
  -- squeeze the indicator between the trapezoids
  have hsqueezeUp : (visitCount u a c n : ℝ)
      ≤ ∑ k ∈ Finset.range n, trapUp a c δ ((u k : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hcard]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : a ≤ u k ∧ u k < c
    · rw [if_pos h]; exact trapUp_ge_indicator a c δ (u k) hδ h
    · rw [if_neg h]; exact trapUp_nonneg a c δ hδ _
  have hsqueezeLo : (∑ k ∈ Finset.range n, trapLo a c δ ((u k : ℝ) : AddCircle (1 : ℝ)))
      ≤ (visitCount u a c n : ℝ) := by
    rw [hcard]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : a ≤ u k ∧ u k < c
    · rw [if_pos h]; exact trapLo_le_one a c δ _
    · rw [if_neg h]
      have hk := hu k
      rw [trapLo_eq_zero_outside a c δ (u k) ha hac hc hk.1 hk.2 h hδ]
  -- pass to the means
  have hdivUp : (visitCount u a c n : ℝ) / n
      ≤ (∑ k ∈ Finset.range n, trapUp a c δ ((u k : ℝ) : AddCircle (1 : ℝ))) / n :=
    div_le_div_of_nonneg_right hsqueezeUp hnR.le
  have hdivLo : (∑ k ∈ Finset.range n, trapLo a c δ ((u k : ℝ) : AddCircle (1 : ℝ))) / n
      ≤ (visitCount u a c n : ℝ) / n :=
    div_le_div_of_nonneg_right hsqueezeLo hnR.le
  have hd1 := hN1 n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  have hd2 := hN2 n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  rw [Real.dist_eq, abs_lt] at hd1 hd2
  have hIup := integral_trapUp_le a c δ ha hac hc hδ
  have hIlo := le_integral_trapLo a c δ ha hac hc hδ
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith [hd2.1, hd1.2]; linarith [hd1.2, hd2.1]]

end NormalNumbers

