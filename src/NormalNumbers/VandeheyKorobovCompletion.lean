/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobov

/-!
# Completion of Vandehey's Korobov power sums

This file proves the repaired `d = 1` case of Vandehey's Lemma 2.2.  The key analytic
input is the sharp interval-Fourier estimate

`τ⁻¹ ∑ h, |∑_{j < N} e(hj/τ)| ≤ 1 + log τ`.

Together with the completed twisted power-sum bound in `VandeheyKorobov`, finite Fourier
inversion gives the desired incomplete power-sum estimate.
-/

open scoped BigOperators
open Finset
open NormalNumbers.G4
open Erdos438.Fourier

namespace NormalNumbers.VandeheyKorobov

open Literature.VandeheyDiff

lemma two_mul_le_log_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx0 hx1 1
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  linarith

lemma centered_harmonic_odd (n : ℕ) :
    (∑ i ∈ range n, (1 : ℝ) / (i + 1)) ≤ Real.log (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let x : ℝ := 1 / (2 * (n : ℝ) + 2)
      have hx0 : 0 ≤ x := by positivity
      have hx1 : x < 1 := by
        dsimp [x]
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast n.zero_le
        have hd : (0 : ℝ) < 2 * (n : ℝ) + 2 := by linarith
        exact (div_lt_one hd).2 (by linarith)
      have hlog := two_mul_le_log_div hx0 hx1
      have hratio : (1 + x) / (1 - x) = ((2 : ℝ) * n + 3) / ((2 : ℝ) * n + 1) := by
        apply (div_eq_div_iff (sub_ne_zero.mpr (ne_of_gt hx1))
          (show (2 : ℝ) * (n : ℝ) + 1 ≠ 0 by positivity)).2
        dsimp [x]
        field_simp [show (2 : ℝ) * (n : ℝ) + 2 ≠ 0 by positivity]
        ring
      rw [hratio, Real.log_div (by positivity) (by positivity)] at hlog
      rw [sum_range_succ]
      push_cast
      dsimp [x] at hlog
      have hterm : (1 : ℝ) / (↑n + 1) = 2 * (1 / (2 * (n : ℝ) + 2)) := by
        field_simp
      rw [hterm]
      have hsucc : (2 : ℝ) * ((n : ℝ) + 1) + 1 = 2 * (n : ℝ) + 3 := by ring
      rw [hsucc]
      linarith

lemma centered_harmonic_even (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1)) + 1 / (2 * n) ≤
      Real.log (2 * n) := by
  have hodd := centered_harmonic_odd (n - 1)
  let x : ℝ := 1 / ((4 : ℝ) * n - 1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1pos : (0 : ℝ) < 4 * n - 1 := by linarith
  have hd2pos : (0 : ℝ) < 2 * n - 1 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hd1pos).2 (by linarith)
  have hlog := two_mul_le_log_div hx0 hx1
  have hratio : (1 + x) / (1 - x) = ((2 : ℝ) * n) / ((2 : ℝ) * n - 1) := by
    apply (div_eq_div_iff (sub_ne_zero.mpr (ne_of_gt hx1)) hd2pos.ne').2
    dsimp [x]
    field_simp [hd1pos.ne']
    ring
  rw [hratio, Real.log_div (by positivity) (by positivity)] at hlog
  have hcast : (2 : ℝ) * (↑(n - 1) : ℝ) + 1 = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    ring
  rw [hcast] at hodd
  dsimp [x] at hlog
  have hterm : (1 : ℝ) / (2 * n) ≤ 2 * (1 / (4 * (n : ℝ) - 1)) := by
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * n by positivity)]
    field_simp [hd1pos.ne']
    nlinarith
  linarith

lemma norm_ePhase_sub_one_eq (x : ℝ) :
    ‖ePhase x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  rw [ePhase]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) by push_cast; ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  norm_num [abs_mul]
  congr 2
  ring

lemma four_mul_le_norm_ePhase_sub_one {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    4 * x ≤ ‖ePhase x - 1‖ := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hx0]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hscale : 2 / Real.pi * |Real.pi * x| = 2 * x := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hx0]
    field_simp [Real.pi_ne_zero]
  rw [hscale] at hsin
  rw [norm_ePhase_sub_one_eq]
  nlinarith

lemma phase_nat_right (T : ℕ) (h : ℤ) (j : ℕ) :
    phase T h (j : ℤ) = phase T h 1 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.cast_succ, phase_add_right, ih, pow_succ]

lemma norm_geom_sum_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ j ∈ range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  rw [div_le_div_iff_of_pos_right hden]
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

lemma norm_phase_sub_one_lower (T h : ℕ) (hT : 0 < T) (hh0 : 0 < h) (hhT : h < T) :
    4 * ((min h (T - h) : ℕ) : ℝ) / T ≤
      ‖phase T (h : ℤ) 1 - 1‖ := by
  rw [phase_eq_ePhase]
  push_cast
  simp only [mul_one]
  by_cases hhalf : h ≤ T - h
  · rw [min_eq_left (by exact_mod_cast hhalf)]
    have h2 : 2 * h ≤ T := by omega
    have hratio0 : (0 : ℝ) ≤ (h : ℝ) / T := by positivity
    have hratiohalf : (h : ℝ) / T ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hT)]
      have h2R : (2 : ℝ) * h ≤ T := by exact_mod_cast h2
      nlinarith
    convert four_mul_le_norm_ePhase_sub_one hratio0 hratiohalf using 1
    all_goals ring
  · have hhalf' : T - h ≤ h := by omega
    rw [min_eq_right (by exact_mod_cast hhalf')]
    have h2 : 2 * (T - h) ≤ T := by omega
    have hratio0 : (0 : ℝ) ≤ ((T - h : ℕ) : ℝ) / T := by positivity
    have hratiohalf : ((T - h : ℕ) : ℝ) / T ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hT)]
      have h2R : (2 : ℝ) * (T - h : ℕ) ≤ T := by exact_mod_cast h2
      nlinarith
    have hlow := four_mul_le_norm_ePhase_sub_one hratio0 hratiohalf
    rw [norm_ePhase_sub_one_eq] at hlow ⊢
    have hangle : Real.pi * (((T - h : ℕ) : ℝ) / T) =
        Real.pi - Real.pi * ((h : ℝ) / T) := by
      rw [Nat.cast_sub hhT.le]
      field_simp
    rw [hangle, Real.sin_pi_sub] at hlow
    convert hlow using 1
    all_goals ring

lemma norm_initial_phase_sum_le (T N h : ℕ) (hT : 0 < T) (hh0 : 0 < h) (hhT : h < T) :
    ‖∑ j ∈ range N, phase T (h : ℤ) (j : ℤ)‖ ≤
      (T : ℝ) / (2 * (min h (T - h) : ℕ)) := by
  let z := phase T (h : ℤ) 1
  have hz : ‖z‖ = 1 := norm_phase _ _ _
  have hdpos : (0 : ℝ) < (min h (T - h) : ℕ) := by
    exact_mod_cast lt_min hh0 (Nat.sub_pos_of_lt hhT)
  have hchord := norm_phase_sub_one_lower T h hT hh0 hhT
  have hchordpos : 0 < ‖z - 1‖ := lt_of_lt_of_le (by positivity) hchord
  have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchordpos)
  rw [show (∑ j ∈ range N, phase T (h : ℤ) (j : ℤ)) =
      ∑ j ∈ range N, z ^ j by
        apply Finset.sum_congr rfl
        intro j _
        exact phase_nat_right T h j]
  refine (norm_geom_sum_le z hz hz1 N).trans ?_
  rw [div_le_div_iff₀ hchordpos (by positivity : (0 : ℝ) < 2 * (min h (T - h) : ℕ))]
  calc
    2 * (2 * (min h (T - h) : ℕ)) =
        (4 * ((min h (T - h) : ℕ) : ℝ) / T) * T := by
          field_simp
          norm_num
    _ ≤ ‖z - 1‖ * T := mul_le_mul_of_nonneg_right hchord (by positivity)
    _ = T * ‖z - 1‖ := by ring

noncomputable def centeredWeight (T h : ℕ) : ℝ :=
  1 / (2 * (min h (T - h) : ℕ))

lemma sum_centeredWeight_odd (n : ℕ) :
    (∑ h ∈ Ico 1 (2 * n + 1), centeredWeight (2 * n + 1) h) =
      ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by
  let f : ℕ → ℝ := fun h => 1 / (2 * (h : ℝ))
  have hlow :
      (∑ h ∈ Ico 1 (n + 1), centeredWeight (2 * n + 1) h) =
        ∑ h ∈ Ico 1 (n + 1), f h := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhI := Finset.mem_Ico.mp hh
    rw [centeredWeight, min_eq_left (by omega)]
  have hupp :
      (∑ h ∈ Ico (n + 1) (2 * n + 1), centeredWeight (2 * n + 1) h) =
        ∑ h ∈ Ico (n + 1) (2 * n + 1), f (2 * n + 1 - h) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhI := Finset.mem_Ico.mp hh
    rw [centeredWeight, min_eq_right (by omega)]
  have hreflect :
      (∑ h ∈ Ico (n + 1) (2 * n + 1), f (2 * n + 1 - h)) =
        ∑ h ∈ Ico 1 (n + 1), f h := by
    have heq : 2 * n + 1 - n = n + 1 := by omega
    simpa [heq] using
      (Finset.sum_Ico_reflect f (n + 1) (m := 2 * n + 1) (n := 2 * n + 1) (by omega))
  calc
    (∑ h ∈ Ico 1 (2 * n + 1), centeredWeight (2 * n + 1) h) =
        (∑ h ∈ Ico 1 (n + 1), centeredWeight (2 * n + 1) h) +
          ∑ h ∈ Ico (n + 1) (2 * n + 1), centeredWeight (2 * n + 1) h := by
            symm
            exact Finset.sum_Ico_consecutive _ (by omega) (by omega)
    _ = (∑ h ∈ Ico 1 (n + 1), f h) + ∑ h ∈ Ico 1 (n + 1), f h := by
      rw [hlow, hupp, hreflect]
    _ = ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      push_cast
      field_simp
      ring

lemma sum_centeredWeight_even (n : ℕ) (hn : 1 ≤ n) :
    (∑ h ∈ Ico 1 (2 * n), centeredWeight (2 * n) h) =
      (∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1)) + 1 / (2 * n) := by
  let f : ℕ → ℝ := fun h => 1 / (2 * (h : ℝ))
  have hlow :
      (∑ h ∈ Ico 1 (n + 1), centeredWeight (2 * n) h) =
        ∑ h ∈ Ico 1 (n + 1), f h := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhI := Finset.mem_Ico.mp hh
    rw [centeredWeight, min_eq_left (by omega)]
  have hupp :
      (∑ h ∈ Ico (n + 1) (2 * n), centeredWeight (2 * n) h) =
        ∑ h ∈ Ico (n + 1) (2 * n), f (2 * n - h) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hhI := Finset.mem_Ico.mp hh
    rw [centeredWeight, min_eq_right (by omega)]
  have hreflect :
      (∑ h ∈ Ico (n + 1) (2 * n), f (2 * n - h)) =
        ∑ h ∈ Ico 1 n, f h := by
    have heq : 2 * n - n = n := by omega
    simpa [heq] using
      (Finset.sum_Ico_reflect f (n + 1) (m := 2 * n) (n := 2 * n) (by omega))
  have hpair :
      (∑ i ∈ range (n - 1), f (1 + i)) + (∑ i ∈ range (n - 1), f (1 + i)) =
        ∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    push_cast
    field_simp
    ring
  calc
    (∑ h ∈ Ico 1 (2 * n), centeredWeight (2 * n) h) =
        (∑ h ∈ Ico 1 (n + 1), centeredWeight (2 * n) h) +
          ∑ h ∈ Ico (n + 1) (2 * n), centeredWeight (2 * n) h := by
            symm
            exact Finset.sum_Ico_consecutive _ (by omega) (by omega)
    _ = (∑ h ∈ Ico 1 (n + 1), f h) + ∑ h ∈ Ico 1 n, f h := by
      rw [hlow, hupp, hreflect]
    _ = ((∑ i ∈ range (n - 1), f (1 + i)) +
          ∑ i ∈ range (n - 1), f (1 + i)) + f n := by
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_eq_sum_range]
      ring
    _ = (∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1)) + 1 / (2 * n) := by
      rw [hpair]

lemma sum_centeredWeight_le_log (T : ℕ) (hT : 0 < T) :
    (∑ h ∈ Ico 1 T, centeredWeight T h) ≤ Real.log T := by
  let n := T / 2
  have hdiv := Nat.div_add_mod T 2
  rcases Nat.mod_two_eq_zero_or_one T with heven | hodd
  · have hform : T = 2 * n := by
      dsimp [n]
      omega
    have hn : 1 ≤ n := by omega
    rw [hform, sum_centeredWeight_even n hn]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using centered_harmonic_even n hn
  · have hform : T = 2 * n + 1 := by
      dsimp [n]
      omega
    rw [hform, sum_centeredWeight_odd]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      centered_harmonic_odd n

noncomputable def intervalCoefficient (T N h : ℕ) : ℂ :=
  ∑ j ∈ range N, phase T (h : ℤ) (j : ℤ)

@[simp] lemma intervalCoefficient_zero (T N : ℕ) :
    intervalCoefficient T N 0 = N := by
  simp [intervalCoefficient]

/-- The sharp `L¹` mass estimate for Fourier coefficients of an initial interval. -/
lemma sum_norm_intervalCoefficient_div_le (T N : ℕ) (hT : 0 < T) (hNT : N ≤ T) :
    (∑ h ∈ range T, ‖intervalCoefficient T N h‖) / T ≤ 1 + Real.log T := by
  have hrest :
      (∑ h ∈ Ico 1 T, ‖intervalCoefficient T N h‖) ≤
        (T : ℝ) * Real.log T := by
    calc
      (∑ h ∈ Ico 1 T, ‖intervalCoefficient T N h‖) ≤
          ∑ h ∈ Ico 1 T, (T : ℝ) * centeredWeight T h := by
            apply Finset.sum_le_sum
            intro h hh
            have hhI := Finset.mem_Ico.mp hh
            unfold intervalCoefficient centeredWeight
            simpa only [div_eq_mul_inv, one_mul] using
              norm_initial_phase_sum_le T N h hT hhI.1 hhI.2
      _ = (T : ℝ) * ∑ h ∈ Ico 1 T, centeredWeight T h := by
        rw [Finset.mul_sum]
      _ ≤ (T : ℝ) * Real.log T :=
        mul_le_mul_of_nonneg_left (sum_centeredWeight_le_log T hT) (by positivity)
  rw [Finset.sum_range_eq_add_Ico _ hT, intervalCoefficient_zero, norm_natCast]
  calc
    ((N : ℝ) + ∑ h ∈ Ico 1 T, ‖intervalCoefficient T N h‖) / T ≤
        ((N : ℝ) + T * Real.log T) / T := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
    _ = (N : ℝ) / T + Real.log T := by
      field_simp
    _ ≤ 1 + Real.log T := by
      gcongr
      exact (div_le_one (by exact_mod_cast hT)).2 (by exact_mod_cast hNT)

lemma sum_zmod_eq_sum_range {T : ℕ} [NeZero T]
    {R : Type*} [AddCommMonoid R] (g : ZMod T → R) :
    ∑ x : ZMod T, g x = ∑ n ∈ range T, g (n : ZMod T) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv T).toEquiv
  intro n
  have hn : (n.val : ZMod T) = (ZMod.finEquiv T).toEquiv n := by
    cases T with
    | zero => exact Fin.elim0 n
    | succ T =>
        simp only [ZMod.finEquiv, RingEquiv.toEquiv_eq_coe]
        apply Fin.ext
        change n.val % (T + 1) = n.val
        exact Nat.mod_eq_of_lt n.isLt
  exact congrArg g hn

/-- The sharp interval-coefficient estimate indexed by the exponent group `ZMod T`. -/
lemma sum_norm_intervalCoefficient_zmod_div_le
    (T N : ℕ) [NeZero T] (hNT : N ≤ T) :
    (∑ h : ZMod T, ‖intervalCoefficient T N h.val‖) / T ≤ 1 + Real.log T := by
  rw [sum_zmod_eq_sum_range]
  have hsum :
      (∑ n ∈ range T, ‖intervalCoefficient T N ((n : ZMod T).val)‖) =
        ∑ n ∈ range T, ‖intervalCoefficient T N n‖ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
  rw [hsum]
  exact sum_norm_intervalCoefficient_div_le T N (NeZero.pos T) hNT

noncomputable def negIntervalCoefficient {T : ℕ} (N : ℕ) (h : ZMod T) : ℂ :=
  ∑ j ∈ range N, phase T (-(h.val : ℤ)) (j : ℤ)

lemma norm_negIntervalCoefficient {T : ℕ} (N : ℕ) (h : ZMod T) :
    ‖negIntervalCoefficient N h‖ = ‖intervalCoefficient T N h.val‖ := by
  have hconj : negIntervalCoefficient N h =
      starRingEnd ℂ (intervalCoefficient T N h.val) := by
    unfold negIntervalCoefficient intervalCoefficient
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [conj_phase, phase_neg_left, phase_neg_right]
  rw [hconj]
  exact norm_star _

lemma sum_norm_negIntervalCoefficient_div_le
    (T N : ℕ) [NeZero T] (hNT : N ≤ T) :
    (∑ h : ZMod T, ‖negIntervalCoefficient N h‖) / T ≤ 1 + Real.log T := by
  simp_rw [norm_negIntervalCoefficient]
  exact sum_norm_intervalCoefficient_zmod_div_le T N hNT

lemma phase_orthogonality_zmod (T : ℕ) [NeZero T] (x : ℤ) :
    (∑ h : ZMod T, phase T (h.val : ℤ) x) =
      if (x : ZMod T) = 0 then (T : ℂ) else 0 := by
  rw [sum_zmod_eq_sum_range]
  have hsum :
      (∑ h ∈ range T, phase T (((h : ZMod T).val : ℕ) : ℤ) x) =
        ∑ h ∈ range T, phase T (h : ℤ) x := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hh)]
  rw [hsum]
  exact phase_orthogonality T x

/-- Finite Fourier inversion of an initial interval in `ZMod T`. -/
lemma interval_completion_identity {T : ℕ} [NeZero T]
    (N : ℕ) (hNT : N ≤ T) (B : ZMod T → ℂ) :
    (∑ r ∈ range N, B (r : ZMod T)) =
      (T : ℂ)⁻¹ * ∑ h : ZMod T, negIntervalCoefficient N h *
        ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j := by
  have horth (r : ℕ) (hr : r < N) (j : ZMod T) :
      (∑ h : ZMod T, phase T (h.val : ℤ) ((j.val : ℤ) - r)) =
        if j.val = r then (T : ℂ) else 0 := by
    rw [phase_orthogonality_zmod]
    have hcond : (((j.val : ℤ) - r : ℤ) : ZMod T) = 0 ↔ j.val = r := by
      push_cast
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
      constructor
      · intro hmod
        exact hmod.eq_of_lt_of_lt j.val_lt (hr.trans_le hNT)
      · rintro rfl
        rfl
    simp only [hcond]
  have hexpand :
      (∑ h : ZMod T, negIntervalCoefficient N h *
          ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j) =
        (T : ℂ) * ∑ r ∈ range N, B (r : ZMod T) := by
    calc
      (∑ h : ZMod T, negIntervalCoefficient N h *
          ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j) =
          ∑ h : ZMod T, ∑ r ∈ range N, ∑ j : ZMod T,
            (phase T (-(h.val : ℤ)) (r : ℤ) *
              phase T (h.val : ℤ) (j.val : ℤ)) * B j := by
            apply Finset.sum_congr rfl
            intro h _
            unfold negIntervalCoefficient
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ r ∈ range N, ∑ j : ZMod T, ∑ h : ZMod T,
          (phase T (-(h.val : ℤ)) (r : ℤ) *
            phase T (h.val : ℤ) (j.val : ℤ)) * B j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
      _ = ∑ r ∈ range N, ∑ j : ZMod T,
          B j * ∑ h : ZMod T, phase T (h.val : ℤ) ((j.val : ℤ) - r) := by
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h _
            rw [phase_neg_left, ← phase_neg_right, ← phase_add_right]
            rw [show -(r : ℤ) + (j.val : ℤ) = (j.val : ℤ) - r by ring]
            ring
      _ = ∑ r ∈ range N, ∑ j : ZMod T,
          B j * (if j.val = r then (T : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro j _
            rw [horth r (Finset.mem_range.mp hr) j]
      _ = ∑ r ∈ range N, (T : ℂ) * B (r : ZMod T) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrT : r < T := (Finset.mem_range.mp hr).trans_le hNT
            rw [Finset.sum_eq_single (r : ZMod T)]
            · simp [ZMod.val_natCast_of_lt hrT]
              ring
            · intro j _ hj
              have hjval : j.val ≠ r := by
                intro hv
                apply hj
                apply ZMod.val_injective
                simpa [ZMod.val_natCast_of_lt hrT] using hv
              simp [hjval]
            · simp
      _ = (T : ℂ) * ∑ r ∈ range N, B (r : ZMod T) := by
        rw [Finset.mul_sum]
  rw [hexpand, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne T), one_mul]

/-- Completion transfers a uniform bound for all additive twists to an incomplete interval,
with exactly the factor `1 + log T`. -/
lemma norm_interval_sum_le_of_completed {T : ℕ} [NeZero T]
    (N : ℕ) (hNT : N ≤ T) (B : ZMod T → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hcompleted : ∀ h : ZMod T,
      ‖∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j‖ ≤ C) :
    ‖∑ r ∈ range N, B (r : ZMod T)‖ ≤ C * (1 + Real.log T) := by
  rw [interval_completion_identity N hNT B]
  calc
    ‖(T : ℂ)⁻¹ * ∑ h : ZMod T, negIntervalCoefficient N h *
        ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j‖ =
        (1 / (T : ℝ)) * ‖∑ h : ZMod T, negIntervalCoefficient N h *
          ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j‖ := by
            rw [norm_mul, norm_inv, norm_natCast]
            simp [one_div]
    _ ≤ (1 / (T : ℝ)) * ∑ h : ZMod T,
        ‖negIntervalCoefficient N h *
          ∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j‖ := by
            gcongr
            exact norm_sum_le _ _
    _ = (1 / (T : ℝ)) * ∑ h : ZMod T,
        ‖negIntervalCoefficient N h‖ *
          ‖∑ j : ZMod T, phase T (h.val : ℤ) (j.val : ℤ) * B j‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro h _
            rw [norm_mul]
    _ ≤ (1 / (T : ℝ)) * ∑ h : ZMod T, ‖negIntervalCoefficient N h‖ * C := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro h _
            exact mul_le_mul_of_nonneg_left (hcompleted h) (norm_nonneg _)
    _ = C * ((∑ h : ZMod T, ‖negIntervalCoefficient N h‖) / T) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ C * (1 + Real.log T) :=
      mul_le_mul_of_nonneg_left (sum_norm_negIntervalCoefficient_div_le T N hNT) hC

/-- Split a sum of a periodic sequence into full periods and one initial remainder. -/
lemma sum_range_mul_add_of_periodic {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (T q r : ℕ) (hper : Function.Periodic f T) :
    (∑ n ∈ range (q * T + r), f n) =
      q • (∑ n ∈ range T, f n) + ∑ n ∈ range r, f n := by
  have hblocks (q : ℕ) :
      (∑ n ∈ range (q * T), f n) = q • (∑ n ∈ range T, f n) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul]
      rw [Finset.sum_range_add, ih]
      have hq (x : ℕ) : f (q * T + x) = f x := by
        simpa [Nat.add_comm] using (hper.nat_mul q x)
      simp_rw [hq]
      rw [succ_nsmul]
  rw [Finset.sum_range_add, hblocks]
  have hq (x : ℕ) : f (q * T + x) = f x := by
    simpa [Nat.add_comm] using (hper.nat_mul q x)
  simp_rw [hq]

lemma phase_power_succ {m : ℕ} [NeZero m] (a g : ZMod m) (j : ℕ) :
    phase m (a.val : ℤ) ((g ^ (j + 1)).val : ℤ) =
      phase m ((a * g).val : ℤ) ((g ^ j).val : ℤ) := by
  rw [phase_val_mul, phase_val_mul]
  congr 1
  rw [pow_succ]
  ring

/-- Completion of a power orbit, retaining the sharper logarithm of its order. -/
theorem norm_power_sum_Icc_le_sqrt_mul_log_order
    {b m : ℕ} [NeZero m] [NeZero (orderOf (b : ZMod m))]
    (hbm : Nat.Coprime b m) (a : ZMod m) (ha : IsUnit a)
    (N : ℕ) (hNτ : N ≤ orderOf (b : ZMod m)) :
    ‖∑ n ∈ Icc 1 N,
        phase m (a.val : ℤ) (((b : ZMod m) ^ n).val : ℤ)‖ ≤
      Real.sqrt m * (1 + Real.log (orderOf (b : ZMod m))) := by
  let g : ZMod m := b
  let τ := orderOf g
  let a' := a * g
  have hg : IsUnit g := (ZMod.isUnit_iff_coprime b m).mpr hbm
  have ha' : IsUnit a' := ha.mul hg
  let B : ZMod τ → ℂ := fun j =>
    phase m (a.val : ℤ) ((g ^ (j.val + 1)).val : ℤ)
  have hcompleted (h : ZMod τ) :
      ‖∑ j : ZMod τ, phase τ (h.val : ℤ) (j.val : ℤ) * B j‖ ≤ Real.sqrt m := by
    have heq :
        (∑ j : ZMod τ, phase τ (h.val : ℤ) (j.val : ℤ) * B j) =
          ∑ j : ZMod τ, phase τ (h.val : ℤ) (j.val : ℤ) *
            phase m (a'.val : ℤ) ((g ^ j.val).val : ℤ) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact phase_power_succ a g j.val
    rw [heq]
    exact norm_completed_power_sum_le_sqrt hbm a' ha' h
  have hbound := norm_interval_sum_le_of_completed N hNτ B (Real.sqrt m)
    (Real.sqrt_nonneg _) hcompleted
  have hrewrite :
      (∑ n ∈ Icc 1 N,
          phase m (a.val : ℤ) ((g ^ n).val : ℤ)) =
        ∑ r ∈ range N, B (r : ZMod τ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r hr
    have hrτ : r < τ := (Finset.mem_range.mp hr).trans_le hNτ
    simp only [B, ZMod.val_natCast_of_lt hrτ]
    congr 2
    rw [Nat.add_comm r 1]
  change ‖∑ n ∈ Icc 1 N, phase m (a.val : ℤ) ((g ^ n).val : ℤ)‖ ≤ _
  rw [hrewrite]
  exact hbound

lemma phase_int_pow_eq_phase_val {m b n : ℕ} [NeZero m] (a : ℤ) :
    phase m a ((b : ℤ) ^ n) =
      phase m (((a : ZMod m).val : ℕ) : ℤ)
        ((((b : ZMod m) ^ n).val : ℕ) : ℤ) := by
  rw [phase_eq_stdAddChar_zmod, phase_val_mul]
  congr 2
  push_cast
  ring

/-- **Vandehey, Lemma 2.2, repaired coprime case.**

For a unit frequency and an interval no longer than the multiplicative order, the incomplete
power sum is bounded by `√m (1 + log m)`. -/
theorem norm_power_sum_Icc_le_sqrt_mul_log
    {b m : ℕ} (hm : 1 < m) (hbm : Nat.Coprime b m)
    (a : ℤ) (ha : IsCoprime a (m : ℤ))
    (N : ℕ) (hNτ : N ≤ orderOf (b : ZMod m)) :
    ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
      Real.sqrt m * (1 + Real.log m) := by
  let _ : NeZero m := ⟨by omega⟩
  have hbunit : IsUnit (b : ZMod m) := (ZMod.isUnit_iff_coprime b m).2 hbm
  let _ : NeZero (orderOf (b : ZMod m)) :=
    ⟨Nat.ne_of_gt hbunit.isOfFinOrder.orderOf_pos⟩
  let az : ZMod m := a
  have haz : IsUnit az := by
    exact (ZMod.coe_int_isUnit_iff_isCoprime a m).2 ha.symm
  have hbase := norm_power_sum_Icc_le_sqrt_mul_log_order hbm az haz N hNτ
  have hsum :
      (∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)) =
        ∑ n ∈ Icc 1 N,
          phase m (az.val : ℤ) (((b : ZMod m) ^ n).val : ℤ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [show (b : ℝ) ^ n = (((b : ℤ) ^ n : ℤ) : ℝ) by norm_num]
    rw [← phase_eq_ePhase m a ((b : ℤ) ^ n)]
    exact phase_int_pow_eq_phase_val a
  rw [hsum]
  refine hbase.trans ?_
  have hlog : Real.log (orderOf (b : ZMod m)) ≤ Real.log m :=
    Real.log_le_log (by exact_mod_cast hbunit.isOfFinOrder.orderOf_pos) (by
      exact_mod_cast (ZMod.orderOf_lt hm (b : ZMod m)).le)
  have hone : 1 + Real.log (orderOf (b : ZMod m)) ≤ 1 + Real.log m := by
    linarith
  exact mul_le_mul_of_nonneg_left hone (Real.sqrt_nonneg _)

/-- **Vandehey, Lemma 2.3 (`k = 0` case).**

An arbitrary interval consists of full multiplicative-order periods and one remainder.  Applying
Lemma 2.2 to each, and using `m ≤ M(P) * ord(b,m)`, gives the stated two-term bound. -/
theorem norm_power_sum_Icc_le_k_zero
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (a : ℤ) (ha : IsCoprime a (m : ℤ)) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
      (Real.sqrt m + (bigM b P : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) * N) *
        (1 + Real.log m) := by
  have hbm : Nat.Coprime b m := by
    apply Nat.coprime_of_dvd
    intro p hp hpb hpm
    exact ((hp.coprime_iff_not_dvd).mp (hP p (hsupp p hp hpm)).2) hpb
  let _ : NeZero m := ⟨by omega⟩
  have hbunit : IsUnit (b : ZMod m) := (ZMod.isUnit_iff_coprime b m).2 hbm
  let τ := orderOf (b : ZMod m)
  have hτpos : 0 < τ := hbunit.isOfFinOrder.orderOf_pos
  let _ : NeZero τ := ⟨hτpos.ne'⟩
  let az : ZMod m := a
  let B : ℕ → ℂ := fun r =>
    phase m (az.val : ℤ) (((b : ZMod m) ^ (r + 1)).val : ℤ)
  have hBper : Function.Periodic B τ := by
    intro r
    dsimp [B, τ]
    congr 2
    apply congrArg ZMod.val
    rw [show r + orderOf (b : ZMod m) + 1 =
        (r + 1) + orderOf (b : ZMod m) by omega]
    rw [pow_add, pow_orderOf_eq_one, mul_one]
  have hBsum (L : ℕ) (hL : L ≤ τ) :
      ‖∑ r ∈ range L, B r‖ ≤ Real.sqrt m * (1 + Real.log m) := by
    have hbound := norm_power_sum_Icc_le_sqrt_mul_log hm hbm a ha L (by simpa [τ] using hL)
    have heq :
        (∑ r ∈ range L, B r) =
          ∑ n ∈ Icc 1 L, ePhase ((a : ℝ) * (b : ℝ) ^ n / m) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      dsimp [B, az]
      rw [← phase_int_pow_eq_phase_val a]
      rw [phase_eq_ePhase]
      norm_num
      congr 2
      ring
    rw [heq]
    exact hbound
  let q := N / τ
  let r := N % τ
  have hNdecomp : q * τ + r = N := by
    dsimp [q, r]
    exact Nat.div_add_mod' N τ
  have hrτ : r ≤ τ := (Nat.mod_lt N hτpos).le
  have hsumB :
      (∑ x ∈ range N, B x) =
        q • (∑ x ∈ range τ, B x) + ∑ x ∈ range r, B x := by
    rw [← hNdecomp]
    exact sum_range_mul_add_of_periodic B τ q r hBper
  have hphase :
      (∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)) =
        ∑ x ∈ range N, B x := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [B, az]
    rw [← phase_int_pow_eq_phase_val a]
    rw [phase_eq_ePhase]
    norm_num
    congr 2
    ring
  rw [hphase, hsumB]
  have hblocks := hBsum τ le_rfl
  have hrem := hBsum r hrτ
  have hnorm :
      ‖q • (∑ x ∈ range τ, B x) + ∑ x ∈ range r, B x‖ ≤
        ((q : ℝ) + 1) * (Real.sqrt m * (1 + Real.log m)) := by
    calc
      ‖q • (∑ x ∈ range τ, B x) + ∑ x ∈ range r, B x‖ ≤
          ‖q • (∑ x ∈ range τ, B x)‖ + ‖∑ x ∈ range r, B x‖ := norm_add_le _ _
      _ ≤ (q : ℝ) * (Real.sqrt m * (1 + Real.log m)) +
          Real.sqrt m * (1 + Real.log m) := by
            apply add_le_add _ hrem
            exact norm_nsmul_le.trans
              (mul_le_mul_of_nonneg_left hblocks (Nat.cast_nonneg q))
      _ = ((q : ℝ) + 1) * (Real.sqrt m * (1 + Real.log m)) := by ring
  refine hnorm.trans ?_
  have hmMτ : m ≤ bigM b P * τ := by
    simpa [τ] using le_bigM_mul_orderOf b hb P hP m hm hsupp hbm
  have hqτN : q * τ ≤ N := by
    dsimp [q]
    exact Nat.div_mul_le_self N τ
  have hqmN : q * m ≤ bigM b P * N := by
    calc
      q * m ≤ q * (bigM b P * τ) := Nat.mul_le_mul_left q hmMτ
      _ = bigM b P * (q * τ) := by ring
      _ ≤ bigM b P * N := Nat.mul_le_mul_left _ hqτN
  have hscaled := mul_le_mul_of_nonneg_right
    (show (q : ℝ) * m ≤ bigM b P * N by exact_mod_cast hqmN)
    (show 0 ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) by positivity)
  have hmhalf : (m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt m := by
    calc
      (m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) =
          (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = (m : ℝ) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ = Real.sqrt m := by rw [Real.sqrt_eq_rpow]; norm_num
  have hqbound :
      (q : ℝ) * Real.sqrt m ≤
        (bigM b P : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) * N := by
    rw [← hmhalf]
    nlinarith
  have hlognonneg : 0 ≤ 1 + Real.log m := by
    have : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    linarith
  calc
    ((q : ℝ) + 1) * (Real.sqrt m * (1 + Real.log m)) =
        (((q : ℝ) + 1) * Real.sqrt m) * (1 + Real.log m) := by ring
    _ ≤ (Real.sqrt m + (bigM b P : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) * N) *
        (1 + Real.log m) := mul_le_mul_of_nonneg_right (by
          calc
            ((q : ℝ) + 1) * Real.sqrt m =
                Real.sqrt m + (q : ℝ) * Real.sqrt m := by ring
            _ ≤ Real.sqrt m +
                (bigM b P : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) * N := by
              linarith) hlognonneg

/-- The `k = 0` specialization in exactly the constants and exponents used by the frozen
statement of Vandehey's Theorem 5.1. -/
theorem vandeheyThm51_k_zero
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (a : ℤ) (ha : IsCoprime a (m : ℤ)) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
      ((constPair b P 0).1 * (m : ℝ) ^ alpha 0 * (N : ℝ) ^ (expPair 0).1
        + (constPair b P 0).2 * (m : ℝ) ^ (-alpha 0) * (N : ℝ) ^ (expPair 0).2)
        * (1 + Real.log m) ^ ((2 : ℝ) ^ (-((0 : ℕ) : ℝ))) := by
  have h := norm_power_sum_Icc_le_k_zero b hb P hP m hm hsupp a ha N
  convert h using 1
  all_goals norm_num [constPair, alpha, expPair, Real.sqrt_eq_rpow]

end NormalNumbers.VandeheyKorobov
