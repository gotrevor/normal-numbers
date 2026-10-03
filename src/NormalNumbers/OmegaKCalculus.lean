/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Calculus of `G_p(t) = p(t^{1/k})`

Helper lemmas for `ExplicitOmegaK` (`Gk k p = gk k p` by `rfl`): analyticity on `t > 0`, the
explicit second derivative `G_p''(t) = Σ_i a_i (i/k)(i/k − 1) t^{i/k − 2}`, and its
non-vanishing somewhere on `[1/2, 1]` when `1 ≤ deg p < k`.
-/

open Polynomial Filter Topology

namespace NormalNumbers.OmegaKCalculus

/-- `G_p(t) = p(t^{1/k})`; definitionally `ExplicitOmegaK.Gk`. -/
noncomputable def gk (k : ℕ) (p : ℤ[X]) (t : ℝ) : ℝ := aeval (t ^ ((k : ℝ)⁻¹)) p

theorem analyticAt_rpow_const {a t : ℝ} (ht : 0 < t) : AnalyticAt ℝ (fun u : ℝ => u ^ a) t := by
  have h : AnalyticAt ℝ (fun u => Real.exp (Real.log u * a)) t :=
    ((analyticAt_log ht).mul analyticAt_const).rexp'
  refine h.congr ?_
  filter_upwards [lt_mem_nhds ht] with u hu
  rw [Real.rpow_def_of_pos hu]

theorem analyticOnNhd_gk (k : ℕ) (p : ℤ[X]) : AnalyticOnNhd ℝ (gk k p) (Set.Ioi 0) :=
  fun _ ht => (analyticAt_rpow_const ht).aeval_polynomial p

/-- Power-sum form of `gk` on `t > 0`. -/
theorem gk_eq_sum (k : ℕ) (p : ℤ[X]) {t : ℝ} (ht : 0 < t) :
    gk k p t = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * t ^ ((i : ℝ) / k) := by
  rw [gk, aeval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, inv_mul_eq_div]

theorem hasDerivAt_sum_rpow (s : Finset ℕ) (c r : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∑ i ∈ s, c i * u ^ r i) (∑ i ∈ s, c i * (r i * t ^ (r i - 1))) t := by
  have := HasDerivAt.fun_sum (u := s) (A := fun i u => c i * u ^ r i)
    (A' := fun i => c i * (r i * t ^ (r i - 1))) (x := t)
    (fun i _ => (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (c i))
  simpa using this

theorem deriv_gk_eventually (k : ℕ) (p : ℤ[X]) {t : ℝ} (ht : 0 < t) :
    deriv (gk k p) =ᶠ[𝓝 t] fun u => ∑ i ∈ Finset.range (p.natDegree + 1),
      ((p.coeff i : ℝ) * ((i : ℝ) / k)) * u ^ ((i : ℝ) / k - 1) := by
  filter_upwards [lt_mem_nhds ht] with u hu
  have heq : gk k p =ᶠ[𝓝 u] fun v => ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i : ℝ) * v ^ ((i : ℝ) / k) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact gk_eq_sum k p hv
  rw [heq.deriv_eq, (hasDerivAt_sum_rpow _ _ _ hu).deriv]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem deriv2_gk (k : ℕ) (p : ℤ[X]) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (gk k p)) t = ∑ i ∈ Finset.range (p.natDegree + 1),
      ((p.coeff i : ℝ) * ((i : ℝ) / k) * ((i : ℝ) / k - 1)) * t ^ ((i : ℝ) / k - 2) := by
  rw [(deriv_gk_eventually k p ht).deriv_eq, (hasDerivAt_sum_rpow _ _ _ ht).deriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (i : ℝ) / k - 1 - 1 = (i : ℝ) / k - 2 by ring]
  ring

/-- The polynomial `Q(s) = Σ a_i (i/k)(i/k − 1) s^i`, with `t² G_p''(t) = Q(t^{1/k})`. -/
noncomputable def qPoly (k : ℕ) (p : ℤ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i : ℝ) * ((i : ℝ) / k) * ((i : ℝ) / k - 1)) * X ^ i

theorem deriv2_gk_eq_qPoly (k : ℕ) (hk : k ≠ 0) (p : ℤ[X]) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (gk k p)) t = (qPoly k p).eval (t ^ ((k : ℝ)⁻¹)) * t ^ (-2 : ℝ) := by
  rw [deriv2_gk k p ht, qPoly, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  have key : t ^ ((k : ℝ)⁻¹ * i) * t ^ (-2 : ℝ) = t ^ ((i : ℝ) / k - 2) := by
    rw [← Real.rpow_add ht]; ring_nf
  rw [mul_assoc _ (t ^ _), key]

theorem qPoly_coeff (k : ℕ) (p : ℤ[X]) (j : ℕ) (hj : j ≤ p.natDegree) :
    (qPoly k p).coeff j = (p.coeff j : ℝ) * ((j : ℝ) / k) * ((j : ℝ) / k - 1) := by
  rw [qPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_of_le hj]

theorem qPoly_ne_zero (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) :
    qPoly k p ≠ 0 := by
  intro h
  have hc := qPoly_coeff k p p.natDegree le_rfl
  rw [h, coeff_zero] at hc
  have hp0 : p ≠ 0 := by rintro rfl; simp at h1
  have ha : (p.coeff p.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.2 hp0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hd : (0 : ℝ) < p.natDegree := by exact_mod_cast (by omega : 0 < p.natDegree)
  have hdk : (p.natDegree : ℝ) < k := by exact_mod_cast hk
  have h2 : (p.natDegree : ℝ) / k ≠ 0 := (div_pos hd hkpos).ne'
  have h3 : (p.natDegree : ℝ) / k - 1 ≠ 0 := by
    have : (p.natDegree : ℝ) / k < 1 := (div_lt_one hkpos).2 hdk
    linarith
  exact (mul_ne_zero (mul_ne_zero ha h2) h3) hc.symm

/-- **`G_p'' ≠ 0` somewhere on `[1/2, 1]` when `1 ≤ deg p < k`.** -/
theorem exists_deriv2_gk_ne_zero (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree)
    (hk : p.natDegree < k) : ∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv (gk k p)) t ≠ 0 := by
  have hk0 : k ≠ 0 := by omega
  by_contra hall
  push Not at hall
  apply qPoly_ne_zero k p h1 hk
  apply eq_zero_of_infinite_isRoot
  have hinf : ((fun t : ℝ => t ^ ((k : ℝ)⁻¹)) '' Set.Icc (1 / 2 : ℝ) 1).Infinite := by
    refine (Set.Icc_infinite (by norm_num : (1 / 2 : ℝ) < 1)).image ?_
    intro a ha b hb hab
    have ha0 : 0 ≤ a := by linarith [ha.1]
    have hb0 : 0 ≤ b := by linarith [hb.1]
    have := congrArg (fun x : ℝ => x ^ k) hab
    simpa [Real.rpow_inv_natCast_pow ha0 hk0, Real.rpow_inv_natCast_pow hb0 hk0] using this
  refine hinf.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  have htp : 0 < t := by linarith [ht.1]
  have := hall t ht
  rw [deriv2_gk_eq_qPoly k hk0 p htp] at this
  have hne : t ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos htp _).ne'
  exact (mul_eq_zero.1 this).resolve_right hne

/-- Bounds feeding Baker–Banaji's explicit constant: for `F` `C²` on an open `U ⊇ [1/2,1]` with
`F'' ≠ 0` on the window, there are `A₁ ≥ max|F'|`, `0 < a₁ ≤ |F'(t₀)|`, `A₂ ≥ max|F''|`,
`0 < a₂ ≤ min|F''|`. -/
theorem exists_window_bounds (F : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆ U) (hF : ContDiffOn ℝ 2 F U)
    (hF'' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t ≠ 0) :
    ∃ A₁ a₁ A₂ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A₁) ∧
      (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, a₁ ≤ |deriv F t|) ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A₂) ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a₂ ≤ |deriv (deriv F) t|) := by
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (1 / 2 : ℝ) 1).Nonempty := ⟨1, by norm_num, le_rfl⟩
  have hd1 : ContinuousOn (deriv F) U := hF.continuousOn_deriv_of_isOpen hU (by norm_num)
  have hd2 : ContinuousOn (deriv (deriv F)) U :=
    (hF.deriv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen hU le_rfl
  obtain ⟨A₁, hA₁⟩ := hK.exists_bound_of_continuousOn (hd1.mono hsub)
  obtain ⟨A₂, hA₂⟩ := hK.exists_bound_of_continuousOn (hd2.mono hsub)
  obtain ⟨t₂, ht₂, hmin⟩ := hK.exists_isMinOn hne ((hd2.mono hsub).norm)
  have ha₁ : ∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv F t ≠ 0 := by
    by_contra h
    push Not at h
    have h34 : (3 / 4 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    apply hF'' _ h34
    have hev : deriv F =ᶠ[𝓝 (3 / 4 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)] with u hu
      exact h u ⟨hu.1.le, hu.2.le⟩
    rw [hev.deriv_eq]; simp
  obtain ⟨t₁, ht₁, ht₁ne⟩ := ha₁
  refine ⟨A₁, |deriv F t₁|, A₂, |deriv (deriv F) t₂|, abs_pos.2 ht₁ne,
    abs_pos.2 (hF'' t₂ ht₂), fun t ht => by simpa using hA₁ t ht, ⟨t₁, ht₁, le_rfl⟩,
    fun t ht => by simpa using hA₂ t ht, fun t ht => by simpa using hmin ht⟩

end NormalNumbers.OmegaKCalculus
