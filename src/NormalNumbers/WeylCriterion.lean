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

end Analysis

/-- **Weyl's criterion**, the direction used by the normality wiring: vanishing
Fourier means at every nonzero frequency give equidistribution. -/
theorem equidistributed_of_weyl (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0)) :
    Equidistributed u := by
  sorry

end NormalNumbers

