/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.WeylCriterion

/-!
# A Weyl criterion for SIGNED weights

`WeylCriterion.lean` proves: if every nonzero Fourier mean of `u` vanishes, then the Cesàro
means of every continuous circle function converge to its integral.  Leaf B of the rotation
route (`SwingC3Rotation.tailLargeDecouple_holds`) is not that statement — it is the statement
that a *difference* of two counting measures vanishes:

`(1/N) ∑_{n<N} w n · f (θ + tailLarge P b n) → 0`,  `w n = 1_{n ≡ r (Q)} − 1/Q`.

This file is the corresponding criterion for a bounded signed weight `w`.  It is strictly
easier than the original: the target limit is `0`, so no integral has to be identified, and
`h = 0` is *not* excluded — the `h = 0` hypothesis is just `(1/N)∑_{n<N} w n → 0`, which for
the class weight is free.

The `ε/3` argument is the same: `wMean` is linear in `f` and bounded by `W·‖f‖`, and the
trigonometric polynomials are dense.

**Why this matters for the swing.**  The 2026-09-24 B4 probe
(`probes/swingc3_b4_fourier.py`) measured the Fourier defect directly and found it decaying
like `(log N)^{−a}` with `a ≈ 1.86`, one full power of `log` better than the global mean's
`(log N)^{−0.84} = (log N)^{Re e(1/b) − 1}`.  So the Fourier hypothesis below is exactly the
quantity the arithmetic has to control, and `wgood_all` turns it into Leaf B.
-/

open Filter Topology Complex MeasureTheory

namespace NormalNumbers

/-- The signed-weight Cesàro mean of `f` along `u`. -/
noncomputable def wMean (u w : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, (w k : ℂ) * f ((u k : ℝ) : AddCircle (1 : ℝ))) / n

/-- The signed-weight Fourier mean.  Note `h = 0` is allowed and carries real content. -/
noncomputable def wFourierMean (u w : ℕ → ℝ) (h : ℤ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n,
      (w k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (u k : ℂ))) / n

/-- `f` for which the signed mean vanishes. -/
def WGood (u w : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
  Tendsto (wMean u w f) atTop (𝓝 0)

lemma wMean_add (u w : ℕ → ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) :
    wMean u w (f + g) n = wMean u w f n + wMean u w g n := by
  simp only [wMean, ContinuousMap.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma wMean_smul (u w : ℕ → ℝ) (a : ℂ) (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) :
    wMean u w (a • f) n = a * wMean u w f n := by
  simp only [wMean, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `‖wMean u w f n‖ ≤ W · ‖f‖` whenever `|w| ≤ W`. -/
lemma norm_wMean_le {W : ℝ} (u w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ W)
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℕ) : ‖wMean u w f n‖ ≤ W * ‖f‖ := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hw 0)
  rcases Nat.eq_zero_or_pos n with h | h
  · simp only [wMean, h, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, div_zero, norm_zero]
    positivity
  · rw [wMean, norm_div]
    have hn : (0 : ℝ) < ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast h
    rw [div_le_iff₀ hn]
    calc ‖∑ k ∈ Finset.range n, (w k : ℂ) * f ((u k : ℝ) : AddCircle (1 : ℝ))‖
        ≤ ∑ _k ∈ Finset.range n, W * ‖f‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul (hw k) (f.norm_coe_le_norm _) (norm_nonneg _) hW0
      _ = (W * ‖f‖) * n := by simp [mul_comm]
      _ = (W * ‖f‖) * ‖(n : ℂ)‖ := by simp

lemma wMean_eq_wFourierMean (u w : ℕ → ℝ) (h : ℤ) (n : ℕ) :
    wMean u w (fourier h) n = wFourierMean u w h n := by
  rw [wMean, wFourierMean]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourier_coe_apply]
  norm_num

lemma wgood_fourier (u w : ℕ → ℝ) (h : ℤ)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) atTop (𝓝 0)) :
    WGood u w (fourier h) := by
  rw [WGood, show wMean u w (fourier h) = wFourierMean u w h from
    funext fun n => wMean_eq_wFourierMean u w h n]
  exact hW h

lemma wgood_span (u w : ℕ → ℝ)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) atTop (𝓝 0))
    {f : C(AddCircle (1 : ℝ), ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) : WGood u w f := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨h, rfl⟩ := hx; exact wgood_fourier u w h hW
  | zero =>
      have h0 : wMean u w (0 : C(AddCircle (1 : ℝ), ℂ)) = fun _ => (0 : ℂ) := by
        funext n; simp [wMean]
      rw [WGood, h0]
      exact tendsto_const_nhds
  | add x y _ _ hx hy =>
      have hxy : wMean u w (x + y) = fun n => wMean u w x n + wMean u w y n :=
        funext fun n => wMean_add u w x y n
      rw [WGood, hxy]
      simpa using hx.add hy
  | smul a x _ hx =>
      have hax : wMean u w (a • x) = fun n => a * wMean u w x n :=
        funext fun n => wMean_smul u w a x n
      rw [WGood, hax]
      simpa using hx.const_mul a

/-- **The signed-weight Weyl criterion.**  If every Fourier mean (including `h = 0`) of the
`w`-weighted sequence vanishes, so does the `w`-weighted mean of every continuous function. -/
theorem wgood_all {W : ℝ} (u w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ W)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) atTop (𝓝 0))
    (f : C(AddCircle (1 : ℝ), ℂ)) : WGood u w f := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hw 0)
  rw [WGood, Metric.tendsto_atTop]
  intro ε hε
  have hWpos : 0 < W + 1 := by linarith
  have hdense : f ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) : Set _) := by
    have hspan := span_fourier_closure_eq_top (T := (1 : ℝ))
    have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
      rw [hspan]; trivial
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨P, hPmem, hP⟩ :=
    Metric.mem_closure_iff.mp hdense (ε / (2 * (W + 1))) (by positivity)
  have hPgood := wgood_span u w hW hPmem
  rw [WGood, Metric.tendsto_atTop] at hPgood
  obtain ⟨N, hN⟩ := hPgood (ε / 2) (by linarith)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnorm : ‖f - P‖ < ε / (2 * (W + 1)) := by rwa [← dist_eq_norm]
  have h1 : ‖wMean u w f n - wMean u w P n‖ < ε / 2 := by
    have hsub : wMean u w f n - wMean u w P n = wMean u w (f - P) n := by
      simp only [wMean, ContinuousMap.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]
    rw [hsub]
    calc ‖wMean u w (f - P) n‖ ≤ W * ‖f - P‖ := norm_wMean_le u w hw _ n
      _ ≤ (W + 1) * ‖f - P‖ := by nlinarith [norm_nonneg (f - P)]
      _ < (W + 1) * (ε / (2 * (W + 1))) := by
          exact mul_lt_mul_of_pos_left hnorm hWpos
      _ = ε / 2 := by field_simp
  have h2 : dist (wMean u w P n) 0 < ε / 2 := hN n (le_trans (le_max_left _ _) hn)
  rw [dist_eq_norm, sub_zero] at h2 ⊢
  calc ‖wMean u w f n‖ = ‖(wMean u w f n - wMean u w P n) + wMean u w P n‖ := by ring_nf
    _ ≤ ‖wMean u w f n - wMean u w P n‖ + ‖wMean u w P n‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Real-valued form of `wgood_all`. -/
theorem wgood_real {W : ℝ} (u w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ W)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) atTop (𝓝 0))
    (g : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ))) / n)
      atTop (𝓝 0) := by
  set f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun y => ((g y : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ with hf
  have hmean : ∀ n : ℕ, (wMean u w f n).re
      = (∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ))) / n := by
    intro n
    rw [wMean]
    have hs : (∑ k ∈ Finset.range n, (w k : ℂ) * f ((u k : ℝ) : AddCircle (1 : ℝ)))
        = ((∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
      push_cast [hf]; rfl
    rw [hs, ← Complex.ofReal_natCast n, ← Complex.ofReal_div, Complex.ofReal_re]
  have hcont := (Complex.continuous_re.tendsto (0 : ℂ)).comp (wgood_all u w hw hW f)
  simp only [Function.comp_def, hmean, Complex.zero_re] at hcont
  exact hcont

/-! ### The class weight -/

open Classical in
/-- The signed weight Leaf B needs: `w n = 1_{n ≡ r (mod Q)} − 1/Q`. -/
noncomputable def classWeight (r Q n : ℕ) : ℝ :=
  (if n ≡ r [MOD Q] then 1 else 0) - 1 / (Q : ℝ)

lemma inv_cast_le_one (Q : ℕ) : 0 ≤ 1 / (Q : ℝ) ∧ 1 / (Q : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · norm_num
  · have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith

lemma abs_classWeight_le (r Q n : ℕ) : |classWeight r Q n| ≤ 1 := by
  classical
  obtain ⟨h0, h1⟩ := inv_cast_le_one Q
  rw [classWeight]
  by_cases h : n ≡ r [MOD Q] <;> simp only [h, if_true, if_false] <;> rw [abs_le] <;>
    constructor <;> linarith

/-- The `h = 0` Fourier hypothesis for the class weight is free: it says
`#{n < N : n ≡ r (Q)}/N → 1/Q`, which is elementary. -/
theorem wFourierMean_classWeight_zero_eq (u : ℕ → ℝ) (r Q n : ℕ) :
    wFourierMean u (classWeight r Q) 0 n
      = (∑ k ∈ Finset.range n, (classWeight r Q k : ℂ)) / n := by
  rw [wFourierMean]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  norm_num

end NormalNumbers
