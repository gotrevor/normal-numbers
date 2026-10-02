/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.WeylCriterion

/-!
# Quantitative C′: an Erdős–Turán inequality by a Fejér sandwich (build gap 5)

The Fejér kernel `K_H(t) = |∑_{j≤H} e(jt)|²/(H+1)` is nonnegative, has unit mass over every
period, and is `≤ 1/(4δ²(H+1))` at distance `≥ δ` from `ℤ`.  Its window integrals
`g(x) = ∫_{x−β}^{x−α} K_H` are finite trigonometric polynomials whose nonzero coefficients are
`≤ 1/(π|m|)`, so `g` sandwiches the indicator of `[a, c)` with no Fourier-series convergence.
-/

open Complex Real MeasureTheory intervalIntegral Finset Filter

namespace NormalNumbers.PrimeModel.Quant

/-- The unit circle point `e(t) = exp(2πit)`. -/
noncomputable def zE (t : ℝ) : ℂ := Complex.exp (2 * π * I * t)

/-- The Fejér partial sum `∑_{j ≤ H} e(t)^j`. -/
noncomputable def fejS (H : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range (H + 1), zE t ^ j

/-- The Fejér kernel `K_H(t) = |∑_{j≤H} e(jt)|² / (H+1)`. -/
noncomputable def fejK (H : ℕ) (t : ℝ) : ℝ := ‖fejS H t‖ ^ 2 / (H + 1)

lemma fejK_nonneg (H : ℕ) (t : ℝ) : 0 ≤ fejK H t := by unfold fejK; positivity

lemma zE_pow (t : ℝ) (j : ℕ) : zE t ^ j = Complex.exp (2 * π * I * ((j : ℤ) : ℝ) * t) := by
  rw [zE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma norm_zE (t : ℝ) : ‖zE t‖ = 1 := by
  rw [zE, Complex.norm_exp]
  simp

lemma continuous_zE : Continuous zE := by unfold zE; fun_prop

lemma continuous_fejK (H : ℕ) : Continuous (fejK H) := by
  unfold fejK fejS; have := continuous_zE; fun_prop

/-- The double-sum expansion `K_H(t) = (H+1)⁻¹ ∑_{j,l} e((j−l)t)`. -/
lemma fejK_expand (H : ℕ) (t : ℝ) :
    ((fejK H t : ℝ) : ℂ) = (1 / ((H : ℂ) + 1)) * ∑ j ∈ range (H + 1), ∑ l ∈ range (H + 1),
      Complex.exp (2 * π * I * (((j : ℤ) - l : ℤ) : ℝ) * t) := by
  have hconj : (starRingEnd ℂ) (zE t) = Complex.exp (-(2 * π * I * t)) := by
    rw [zE, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  have hsq : ((‖fejS H t‖ ^ 2 : ℝ) : ℂ) = fejS H t * (starRingEnd ℂ) (fejS H t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [fejK]; push_cast
  rw [show ((‖fejS H t‖ : ℂ)) ^ 2 = ((‖fejS H t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, hsq]
  rw [div_eq_mul_inv, mul_comm, one_div]
  congr 1
  rw [fejS, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_pow, hconj, zE, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `∫_p^q e(mt) dt` for `m ≠ 0`. -/
lemma integral_exp_int {m : ℤ} (hm : m ≠ 0) (p q : ℝ) :
    ∫ t in p..q, Complex.exp (2 * π * I * (m : ℝ) * t)
      = (Complex.exp (2 * π * I * (m : ℝ) * q) - Complex.exp (2 * π * I * (m : ℝ) * p))
        / (2 * π * I * (m : ℝ)) := by
  have hc : (2 * π * I * (m : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  exact integral_exp_mul_complex hc

lemma exp_two_pi_int (m : ℤ) (p : ℝ) :
    Complex.exp (2 * π * I * (m : ℝ) * ((p + 1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * (m : ℝ) * p) := by
  rw [show 2 * π * I * ((m : ℝ) : ℂ) * ((p + 1 : ℝ) : ℂ)
      = 2 * π * I * (m : ℝ) * p + (m : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Unit mass over every period. -/
lemma integral_fejK_period (H : ℕ) (p : ℝ) : ∫ t in p..(p + 1), fejK H t = 1 := by
  have hc : ((∫ t in p..(p + 1), fejK H t : ℝ) : ℂ) = 1 := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [fejK_expand]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      exact (continuous_finsetSum _ (fun l _ => by fun_prop)).intervalIntegrable _ _)]
    have hin : ∀ j ∈ range (H + 1), ∫ t in p..(p + 1), ∑ l ∈ range (H + 1),
        Complex.exp (2 * π * I * (((j : ℤ) - l : ℤ) : ℝ) * t) = 1 := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum (fun l _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        have hm : ((j : ℤ) - l) ≠ 0 := by omega
        rw [integral_exp_int hm, exp_two_pi_int, sub_self, zero_div]
      · intro h; exact absurd hj h
    rw [Finset.sum_congr rfl hin]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  exact_mod_cast hc

/-- `|sin(πt)| ≥ 2δ` at distance `≥ δ` from `{0, ±1}` inside `(−1, 1)`. -/
lemma two_mul_le_abs_sin {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ |t|) (h2 : |t| ≤ 1 - δ) :
    2 * δ ≤ |Real.sin (π * t)| := by
  have key : ∀ s : ℝ, δ ≤ s → s ≤ 1 / 2 → 2 * δ ≤ Real.sin (π * s) := by
    intro s hs1 hs2
    have := Real.mul_le_sin (x := π * s) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * s) = 2 * s := by field_simp
    linarith
  have hab : |t| ≤ 1 := by linarith
  have e : |Real.sin (π * t)| = Real.sin (π * |t|) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at hab ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos]))
    · rw [abs_of_nonpos ht] at hab ⊢
      rw [show π * t = -(π * -t) by ring, Real.sin_neg, abs_neg]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos]))
  rw [e]
  rcases le_total |t| (1 / 2) with hs | hs
  · exact key _ h1 hs
  · have := key (1 - |t|) (by linarith) (by linarith)
    rwa [show π * (1 - |t|) = π - π * |t| by ring, Real.sin_pi_sub] at this

lemma norm_zE_sub_one_sq (t : ℝ) : ‖zE t - 1‖ ^ 2 = 4 * Real.sin (π * t) ^ 2 := by
  have hz : zE t = Complex.exp (((2 * π * t : ℝ) : ℂ) * I) := by
    rw [zE]; congr 1; push_cast; ring
  rw [hz, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show ((Real.cos (2 * π * t) : ℂ) + (Real.sin (2 * π * t) : ℂ) * I - 1)
      = ((Real.cos (2 * π * t) - 1 : ℝ) : ℂ) + ((Real.sin (2 * π * t) : ℝ) : ℂ) * I by
      push_cast; ring]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hc : Real.cos (2 * π * t) = 1 - 2 * Real.sin (π * t) ^ 2 := by
    rw [show 2 * π * t = 2 * (π * t) by ring, Real.cos_two_mul, Real.cos_sq']; ring
  have hs : Real.sin (2 * π * t) = 2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [show 2 * π * t = 2 * (π * t) by ring, Real.sin_two_mul]
  rw [hc, hs]
  have := Real.sin_sq_add_cos_sq (π * t)
  nlinarith [this]

/-- **Pointwise decay.**  At distance `≥ δ` from `{0, ±1}`, `K_H(t) ≤ 1/(4δ²(H+1))`. -/
lemma fejK_le (H : ℕ) {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ |t|) (h2 : |t| ≤ 1 - δ) :
    fejK H t ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by
  have hsin := two_mul_le_abs_sin hδ h1 h2
  have hz : 4 * δ ≤ ‖zE t - 1‖ := by
    have hsq := norm_zE_sub_one_sq t
    have : (4 * δ) ^ 2 ≤ ‖zE t - 1‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_abs (Real.sin (π * t)), abs_nonneg (Real.sin (π * t))]
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg (zE t - 1)]
  have hgeom : fejS H t * (zE t - 1) = zE t ^ (H + 1) - 1 := by
    rw [fejS]; exact geom_sum_mul _ _
  have hnum : ‖zE t ^ (H + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_zE, one_pow, norm_one]; norm_num
  have hS : ‖fejS H t‖ * (4 * δ) ≤ 2 := by
    have := congrArg norm hgeom
    rw [norm_mul] at this
    nlinarith [norm_nonneg (fejS H t)]
  have hS' : ‖fejS H t‖ ≤ 1 / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [fejK, div_le_div_iff₀ (by positivity) (by positivity)]
  have h0 := norm_nonneg (fejS H t)
  have hsq : ‖fejS H t‖ ^ 2 ≤ (1 / (2 * δ)) ^ 2 := pow_le_pow_left₀ h0 hS' 2
  have e : (1 / (2 * δ)) ^ 2 * (4 * δ ^ 2) = 1 := by field_simp; ring
  have hH : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ 4 * δ ^ 2 * ((H : ℝ) + 1))]

/-! ## The window function -/

/-- The Fejér window `g(x) = ∫_{x−β}^{x−α} K_H`, a smoothed indicator of `[α, β]`. -/
noncomputable def fejG (H : ℕ) (α β x : ℝ) : ℝ := ∫ t in (x - β)..(x - α), fejK H t

lemma fejG_nonneg (H : ℕ) {α β : ℝ} (hαβ : α ≤ β) (x : ℝ) : 0 ≤ fejG H α β x :=
  intervalIntegral.integral_nonneg (by linarith) (fun t _ => fejK_nonneg H t)

/-- The `m`-th coefficient of the window, `(e(−mα) − e(−mβ))/(2πim)`. -/
noncomputable def winCoef (α β : ℝ) (m : ℤ) : ℂ :=
  (Complex.exp (-(2 * π * I * (m : ℝ) * α)) - Complex.exp (-(2 * π * I * (m : ℝ) * β)))
    / (2 * π * I * (m : ℝ))

lemma norm_winCoef_le (α β : ℝ) {m : ℤ} (hm : m ≠ 0) :
    ‖winCoef α β m‖ ≤ 1 / (π * |(m : ℝ)|) := by
  have hm' : (0 : ℝ) < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  rw [winCoef, norm_div]
  have hnum : ‖Complex.exp (-(2 * π * I * (m : ℝ) * α)) - Complex.exp (-(2 * π * I * (m : ℝ) * β))‖
      ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ∀ y : ℝ, ‖Complex.exp (-(2 * π * I * (m : ℝ) * y))‖ = 1 := by
      intro y; rw [Complex.norm_exp]; simp
    rw [h1, h1]; norm_num
  have hden : ‖(2 * π * I * (m : ℝ) : ℂ)‖ = 2 * π * |(m : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real]
    simp [abs_of_pos Real.pi_pos]
  rw [hden, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ π * |(m : ℝ)|)]

/-- One term of the window integral. -/
lemma integral_window_term (m : ℤ) (α β x : ℝ) :
    ∫ t in (x - β)..(x - α), Complex.exp (2 * π * I * (m : ℝ) * t)
      = if m = 0 then ((β - α : ℝ) : ℂ)
        else Complex.exp (2 * π * I * (m : ℝ) * x) * winCoef α β m := by
  split_ifs with hm
  · subst hm; simp
  · rw [integral_exp_int hm, winCoef, mul_div_assoc']
    congr 1
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring

/-- **The mean of the window along a sequence** is `β − α` plus off-diagonal Weyl terms. -/
lemma window_mean_eq (H : ℕ) (α β : ℝ) (u : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (((∑ k ∈ range n, fejG H α β (u k)) / n : ℝ) : ℂ)
      = ((β - α : ℝ) : ℂ) + (1 / ((H : ℂ) + 1)) * ∑ j ∈ range (H + 1),
          ∑ l ∈ (range (H + 1)).erase j,
            winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n := by
  have hpt : ∀ x : ℝ, ((fejG H α β x : ℝ) : ℂ) = (1 / ((H : ℂ) + 1)) * ∑ j ∈ range (H + 1),
      ∑ l ∈ range (H + 1), (if ((j : ℤ) - l) = 0 then ((β - α : ℝ) : ℂ)
        else Complex.exp (2 * π * I * ((((j : ℤ) - l : ℤ)) : ℝ) * x) * winCoef α β ((j : ℤ) - l)) := by
    intro x
    rw [fejG, ← intervalIntegral.integral_ofReal]
    simp_rw [fejK_expand]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (continuous_finsetSum _ (fun l _ => by fun_prop)).intervalIntegrable _ _)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun l _ =>
      (by fun_prop : Continuous _).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl fun l _ => integral_window_term _ α β x
  have hnR : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hj : ∀ j ∈ range (H + 1), ∑ x ∈ range n, ∑ l ∈ range (H + 1),
      (if ((j : ℤ) - l) = 0 then ((β - α : ℝ) : ℂ)
        else Complex.exp (2 * π * I * ((((j : ℤ) - l : ℤ)) : ℝ) * (u x)) * winCoef α β ((j : ℤ) - l))
      = (n : ℂ) * ((β - α : ℝ) : ℂ) + (n : ℂ) * ∑ l ∈ (range (H + 1)).erase j,
          winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n := by
    intro j hj
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ hj]
    simp only [sub_self, if_true, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlj : ((j : ℤ) - l) ≠ 0 := by
      have := Finset.ne_of_mem_erase hl; omega
    simp only [hlj, if_false]
    rw [← Finset.sum_mul, fourierMean]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsum : ∑ x ∈ range n, Complex.exp (2 * π * I * ((((j : ℤ) - l : ℤ)) : ℝ) * (u x))
        = ∑ k ∈ range n, Complex.exp (2 * π * I * (((j : ℤ) - l : ℤ) : ℂ) * (u k : ℂ)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    rw [hsum]
    field_simp
    try ring
  rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hH : ((H : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero H
  push_cast
  field_simp
  rw [← Finset.mul_sum]; ring

/-- Frequency `−m` is the conjugate of frequency `m`. -/
lemma norm_fourierMean_neg (u : ℕ → ℝ) (m : ℤ) (n : ℕ) :
    ‖fourierMean u (-m) n‖ = ‖fourierMean u m n‖ := by
  have : fourierMean u (-m) n = (starRingEnd ℂ) (fourierMean u m n) := by
    rw [fourierMean, fourierMean, map_div₀, map_sum, Complex.conj_natCast]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  rw [this, Complex.norm_conj]

/-- **Counting.**  For fixed `j ≤ H`, each gap `k = |j − l| ∈ [1, H]` occurs at most twice. -/
lemma sum_erase_gap_le (H j : ℕ) (hj : j ≤ H) (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k) :
    ∑ l ∈ (range (H + 1)).erase j, φ ((j : ℤ) - l).natAbs
      ≤ 2 * ∑ k ∈ Icc 1 H, φ k := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun l => l < j)]
  have side : ∀ (A : Finset ℕ), (∀ l ∈ A, l ∈ (range (H + 1)).erase j) →
      Set.InjOn (fun l : ℕ => ((j : ℤ) - l).natAbs) A →
      ∑ l ∈ A, φ ((j : ℤ) - l).natAbs ≤ ∑ k ∈ Icc 1 H, φ k := by
    intro A hA hinj
    rw [← Finset.sum_image (f := φ) (fun x hx y hy hxy => hinj hx hy hxy)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hφ k)
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have := hA l hl
    rw [Finset.mem_erase, Finset.mem_range] at this
    rw [Finset.mem_Icc]; omega
  have h1 := side ((range (H + 1)).erase j |>.filter (fun l => l < j))
    (fun l hl => (Finset.mem_filter.mp hl).1) (by
      intro x hx y hy hxy
      have := (Finset.mem_filter.mp hx).2; have := (Finset.mem_filter.mp hy).2
      simp only at hxy; omega)
  have h2 := side ((range (H + 1)).erase j |>.filter (fun l => ¬ l < j))
    (fun l hl => (Finset.mem_filter.mp hl).1) (by
      intro x hx y hy hxy
      have := (Finset.mem_filter.mp hx).2; have := (Finset.mem_filter.mp hy).2
      simp only at hxy; omega)
  linarith

/-- **The window error.**  `|mean of g − (β − α)| ≤ 2 ∑_{k=1}^{H} |W_k|/(πk)`. -/
lemma window_mean_err (H : ℕ) (α β : ℝ) (u : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    |(∑ k ∈ range n, fejG H α β (u k)) / n - (β - α)|
      ≤ 2 * ∑ k ∈ Icc 1 H, ‖fourierMean u (k : ℤ) n‖ / (π * k) := by
  set φ : ℕ → ℝ := fun k => ‖fourierMean u (k : ℤ) n‖ / (π * k) with hφ
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => by simp only [hφ]; positivity
  have hid := window_mean_eq H α β u n hn
  have hcomp : (((∑ k ∈ range n, fejG H α β (u k)) / n - (β - α) : ℝ) : ℂ)
      = (1 / ((H : ℂ) + 1)) * ∑ j ∈ range (H + 1), ∑ l ∈ (range (H + 1)).erase j,
          winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n := by
    push_cast at hid ⊢; rw [hid]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcomp, norm_mul]
  have hH : ‖(1 / ((H : ℂ) + 1))‖ = 1 / ((H : ℝ) + 1) := by
    rw [norm_div, norm_one]; congr 1
    exact_mod_cast Complex.norm_natCast (H + 1)
  rw [hH]
  have hterm : ∀ j ∈ range (H + 1), ∀ l ∈ (range (H + 1)).erase j,
      ‖winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n‖
        ≤ φ ((j : ℤ) - l).natAbs := by
    intro j _ l hl
    have hne : ((j : ℤ) - l) ≠ 0 := by have := Finset.ne_of_mem_erase hl; omega
    rw [norm_mul]
    have hw := norm_winCoef_le α β hne
    have hF : ‖fourierMean u ((j : ℤ) - l) n‖ = ‖fourierMean u (((j : ℤ) - l).natAbs : ℤ) n‖ := by
      rcases Int.natAbs_eq ((j : ℤ) - l) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [norm_fourierMean_neg]
    have habs : |(((j : ℤ) - l : ℤ) : ℝ)| = ((((j : ℤ) - l).natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs] at hw
    simp only [hφ]
    rw [hF, div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  have hsum : ‖∑ j ∈ range (H + 1), ∑ l ∈ (range (H + 1)).erase j,
      winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n‖
      ≤ ((H : ℝ) + 1) * (2 * ∑ k ∈ Icc 1 H, φ k) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ range (H + 1), ‖∑ l ∈ (range (H + 1)).erase j,
        winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n‖ ≤ 2 * ∑ k ∈ Icc 1 H, φ k := by
      intro j hj
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm j hj)).trans ?_)
      exact sum_erase_gap_le H j (by have := Finset.mem_range.mp hj; omega) φ hφ0
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  calc 1 / ((H : ℝ) + 1) * ‖∑ j ∈ range (H + 1), ∑ l ∈ (range (H + 1)).erase j,
        winCoef α β ((j : ℤ) - l) * fourierMean u ((j : ℤ) - l) n‖
      ≤ 1 / ((H : ℝ) + 1) * (((H : ℝ) + 1) * (2 * ∑ k ∈ Icc 1 H, φ k)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * ∑ k ∈ Icc 1 H, φ k := by field_simp

/-! ### The sandwich -/

lemma fejK_ii (H : ℕ) (p q : ℝ) : IntervalIntegrable (fejK H) volume p q :=
  (continuous_fejK H).intervalIntegrable _ _

/-- An integral over a sub-interval of a period is at most `1`. -/
lemma integral_fejK_le_one (H : ℕ) {p q r : ℝ} (hpr : r ≤ p) (hpq : p ≤ q) (hq : q ≤ r + 1) :
    ∫ t in p..q, fejK H t ≤ 1 := by
  rw [← integral_fejK_period H r]
  exact integral_mono_interval hpr hpq hq
    (Filter.Eventually.of_forall fun t => fejK_nonneg H t) (fejK_ii H _ _)

/-- Away from `ℤ`, the kernel integrates to at most length times `1/(4δ²(H+1))`. -/
lemma integral_fejK_le_away (H : ℕ) {δ p q : ℝ} (hδ : 0 < δ) (hpq : p ≤ q)
    (hpt : ∀ t ∈ Set.Icc p q, δ ≤ |t| ∧ |t| ≤ 1 - δ) :
    ∫ t in p..q, fejK H t ≤ (q - p) * (1 / (4 * δ ^ 2 * (H + 1))) := by
  have := integral_mono_on hpq (fejK_ii H p q) intervalIntegrable_const
    (fun t ht => fejK_le H hδ (hpt t ht).1 (hpt t ht).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  exact this

/-- The central mass: `∫_{−δ}^{δ} K ≥ 1 − 1/(4δ²(H+1))`. -/
lemma integral_fejK_center (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    1 - 1 / (4 * δ ^ 2 * (H + 1)) ≤ ∫ t in (-δ)..δ, fejK H t := by
  have hsplit := integral_add_adjacent_intervals (fejK_ii H (-δ) δ) (fejK_ii H δ (-δ + 1))
  rw [integral_fejK_period] at hsplit
  have hside := integral_fejK_le_away H hδ (show δ ≤ -δ + 1 by linarith) (fun t ht => by
    obtain ⟨h1, h2⟩ := ht
    have ht0 : 0 ≤ t := by linarith
    rw [abs_of_nonneg ht0]; constructor <;> linarith)
  have hη : 0 ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by positivity
  have : (-δ + 1 - δ) * (1 / (4 * δ ^ 2 * (H + 1))) ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by
    have : -δ + 1 - δ ≤ 1 := by linarith
    nlinarith
  linarith

/-- Upper sandwich: `1_{[a,c)}(x) ≤ g(x) + η` with window `[a − δ, c + δ]`. -/
lemma ind_le_fejG_up (H : ℕ) {a c δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hac : a ≤ c) (x : ℝ) :
    (if x ∈ Set.Ico a c then (1 : ℝ) else 0)
      ≤ fejG H (a - δ) (c + δ) x + 1 / (4 * δ ^ 2 * (H + 1)) := by
  have hη : 0 ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by positivity
  split_ifs with hx
  · obtain ⟨hx1, hx2⟩ := hx
    have hc := integral_fejK_center H hδ hδ2
    have : ∫ t in (-δ)..δ, fejK H t ≤ fejG H (a - δ) (c + δ) x := by
      unfold fejG
      exact integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun t => fejK_nonneg H t) (fejK_ii H _ _)
    linarith
  · have := fejG_nonneg H (show a - δ ≤ c + δ by linarith) x
    linarith

/-- Lower sandwich: for `x ∈ [0,1)`, `g(x) ≤ 1_{[a,c)}(x) + η` with window `[a + δ, c − δ]`. -/
lemma fejG_lo_le_ind (H : ℕ) {a c δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hc : c ≤ 1)
    (hac : 2 * δ ≤ c - a) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    fejG H (a + δ) (c - δ) x
      ≤ (if x ∈ Set.Ico a c then (1 : ℝ) else 0) + 1 / (4 * δ ^ 2 * (H + 1)) := by
  have hη : 0 ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by positivity
  unfold fejG
  split_ifs with hx
  · obtain ⟨hxa, hxc⟩ := hx
    have := integral_fejK_le_one H (p := x - (c - δ)) (q := x - (a + δ)) (r := x - (c - δ)) le_rfl (by linarith) (by linarith)
    linarith
  · have hlen : (x - (a + δ) - (x - (c - δ))) * (1 / (4 * δ ^ 2 * (H + 1)))
        ≤ 1 / (4 * δ ^ 2 * (H + 1)) := by
      have : x - (a + δ) - (x - (c - δ)) ≤ 1 := by linarith
      have : 0 ≤ x - (a + δ) - (x - (c - δ)) := by linarith
      nlinarith
    refine le_trans (integral_fejK_le_away H hδ (by linarith) ?_) (by linarith)
    intro t ⟨ht1, ht2⟩
    rcases lt_or_ge x a with hxa | hxa
    · have : t < 0 := by linarith
      rw [abs_of_neg this]; constructor <;> linarith
    · have hxc : c ≤ x := by
        by_contra h; exact hx ⟨hxa, lt_of_not_ge h⟩
      have : 0 ≤ t := by linarith
      rw [abs_of_nonneg this]; constructor <;> linarith

/-- **Erdős–Turán by the Fejér sandwich.**  For a sequence in `[0,1)` and `0 < δ ≤ 1/2`,
`|visits/n − (c − a)| ≤ 2δ + 1/(4δ²(H+1)) + 2∑_{k≤H} |W_k|/(πk)`. -/
theorem visit_err (H : ℕ) (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k ∧ u k < 1) {a c δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (n : ℕ) (hn : 0 < n) :
    |(visitCount u a c n : ℝ) / n - (c - a)|
      ≤ 2 * δ + 1 / (4 * δ ^ 2 * (H + 1))
        + 2 * ∑ k ∈ Icc 1 H, ‖fourierMean u (k : ℤ) n‖ / (π * k) := by
  set η := 1 / (4 * δ ^ 2 * (H + 1)) with hη
  set E := 2 * ∑ k ∈ Icc 1 H, ‖fourierMean u (k : ℤ) n‖ / (π * k) with hE
  have hη0 : 0 ≤ η := by positivity
  have hE0 : 0 ≤ E := by
    have := window_mean_err H 0 0 u n hn; exact (abs_nonneg _).trans this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcnt : (visitCount u a c n : ℝ) = ∑ k ∈ range n, (if u k ∈ Set.Ico a c then (1 : ℝ) else 0) := by
    rw [visitCount, Finset.natCast_card_filter]
  -- upper
  have hup : (visitCount u a c n : ℝ) / n ≤ (c - a) + 2 * δ + E + η := by
    have h1 : (visitCount u a c n : ℝ) ≤ ∑ k ∈ range n, fejG H (a - δ) (c + δ) (u k) + n * η := by
      rw [hcnt]
      refine (Finset.sum_le_sum fun k _ => ind_le_fejG_up H hδ hδ2 hac (u k)).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 := (abs_le.mp (window_mean_err H (a - δ) (c + δ) u n hn)).2
    rw [div_le_iff₀ hnR]
    have h3 : (∑ k ∈ range n, fejG H (a - δ) (c + δ) (u k))
        = (∑ k ∈ range n, fejG H (a - δ) (c + δ) (u k)) / n * n := by field_simp
    nlinarith
  -- lower
  have hlo : (c - a) - 2 * δ - E - η ≤ (visitCount u a c n : ℝ) / n := by
    rcases lt_or_ge (c - a) (2 * δ) with hsmall | hbig
    · have : 0 ≤ (visitCount u a c n : ℝ) / n := by positivity
      linarith
    have h1 : ∑ k ∈ range n, fejG H (a + δ) (c - δ) (u k) ≤ (visitCount u a c n : ℝ) + n * η := by
      rw [hcnt]
      refine (Finset.sum_le_sum fun k _ =>
        fejG_lo_le_ind H hδ ha hc hbig (hu k).1 (hu k).2).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 := (abs_le.mp (window_mean_err H (a + δ) (c - δ) u n hn)).1
    rw [le_div_iff₀ hnR]
    have h3 : (∑ k ∈ range n, fejG H (a + δ) (c - δ) (u k))
        = (∑ k ∈ range n, fejG H (a + δ) (c - δ) (u k)) / n * n := by field_simp
    nlinarith
  rw [abs_le]; constructor <;> linarith

end NormalNumbers.PrimeModel.Quant
