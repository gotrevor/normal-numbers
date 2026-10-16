/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterKicked
import NormalNumbers.Furstenberg
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart

/-!
# Hypothesis A and the base-four logarithm family

Arithmetic prerequisites for the Bailey--Crandall Hypothesis A consequence that every nonzero
rational combination of `log 2` and `log 3` is normal in base four.
-/

namespace NormalNumbers.MasterConjectures

open Polynomial Filter

/-- Hermite's theorem in the form needed for affine independence of logarithms: a positive
integral power of `e` is not rational.  This is the `X - j` specialization of mathlib's
`LindemannWeierstrass.exp_polynomial_approx`. -/
theorem exp_nat_ne_rat {j : ℕ} (hj : 1 ≤ j) (q : ℚ) : Real.exp j ≠ q := by
  intro hq
  set f : ℤ[X] := X - C (j : ℤ) with hf
  have hf0 : f.eval 0 ≠ 0 := by simp [hf]; omega
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  have hlim : Tendsto (fun p : ℕ => q.den * (c ^ p / ((p - 1).factorial : ℝ)))
      atTop (nhds 0) := by
    have h := (FloorSemiring.tendsto_pow_div_factorial_atTop c).const_mul c
    rw [mul_zero] at h
    have h2 := h.comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun p : ℕ => c ^ p / ((p - 1).factorial : ℝ)) atTop (nhds 0) := by
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with p hp
      simp only [Function.comp_apply]
      rw [← mul_div_assoc, ← pow_succ', Nat.sub_add_cancel hp]
    simpa using h3.const_mul (q.den : ℝ)
  obtain ⟨P, hP⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds one_pos))
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (P + j + q.num.natAbs + q.den + 2)
  have hpc : q.den * (c ^ p / ((p - 1).factorial : ℝ)) < 1 := hP p (by omega)
  have hpf : p > (f.eval 0).natAbs := by simp [hf]; omega
  obtain ⟨n, hn, gp, -, hbound⟩ := hc p hpf hp
  have hroot : (j : ℂ) ∈ f.aroots ℂ := by rw [hf, aroots_X_sub_C]; simp
  have hb := hbound hroot
  have hexp : Complex.exp (j : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_exp, hq]
    simp
  have hae : aeval (j : ℂ) gp = ((gp.eval (j : ℤ) : ℤ) : ℂ) := by
    rw [show (j : ℂ) = algebraMap ℤ ℂ (j : ℤ) by simp,
      aeval_algebraMap_apply_eq_algebraMap_eval]
    simp
  rw [hexp, hae, zsmul_eq_mul, nsmul_eq_mul] at hb
  set z : ℤ := n * q.num - p * q.den * gp.eval (j : ℤ) with hz
  have hden : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.pos.ne'
  have hzC : (q.den : ℂ) *
        ((n : ℂ) * (q : ℂ) - (p : ℂ) * ((gp.eval (j : ℤ) : ℤ) : ℂ)) = (z : ℂ) := by
    rw [Rat.cast_def]
    field_simp [hden]
    rw [hz]
    push_cast
    ring
  have hb' : ‖(z : ℂ)‖ ≤ q.den * (c ^ p / ((p - 1).factorial : ℝ)) := by
    rw [← hzC, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hz0 : z = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hne
    linarith
  have hdvd : (p : ℤ) ∣ n * q.num :=
    ⟨q.den * gp.eval (j : ℤ), by rw [hz] at hz0; linarith⟩
  rcases (Int.Prime.dvd_mul' hp hdvd) with h | h
  · exact hn h
  · have hnum0 : q.num ≠ 0 := by
      intro h0
      have : (q : ℝ) = 0 := by simp [Rat.cast_def, h0]
      rw [this] at hq
      exact (Real.exp_pos j).ne' hq
    have hpnum : p ∣ q.num.natAbs := by
      rw [← Int.natCast_dvd_natCast]
      simpa using (Int.dvd_natAbs.mpr h)
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hnum0) hpnum
    omega

/-- No nonzero integral power of `e` is rational. -/
theorem exp_int_ne_rat {j : ℤ} (hj : j ≠ 0) (q : ℚ) : Real.exp j ≠ q := by
  intro hq
  rcases lt_or_gt_of_ne hj with hjneg | hjpos
  · have hpos : 1 ≤ (-j).natAbs := by omega
    apply exp_nat_ne_rat hpos q⁻¹
    have hjcast : (((-j).natAbs : ℕ) : ℝ) = -(j : ℝ) := by
      have hnon : 0 ≤ -j := by omega
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnon)
      simpa using h
    rw [hjcast, Real.exp_neg, hq]
    norm_num
  · have hpos : 1 ≤ j.natAbs := by omega
    apply exp_nat_ne_rat hpos q
    have hjcast : ((j.natAbs : ℕ) : ℝ) = (j : ℝ) := by
      have hnon : 0 ≤ j := by omega
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnon)
      simpa using h
    rwa [hjcast]

private theorem exp_int_mul_log_nat (a : ℤ) (m : ℕ) (hm : 0 < m) :
    Real.exp ((a : ℝ) * Real.log m) = (((m : ℚ) ^ a : ℚ) : ℝ) := by
  rw [mul_comm, Real.exp_mul, Real.exp_log (by exact_mod_cast hm), Real.rpow_intCast,
    Rat.cast_zpow]
  norm_num

/-- Hermite plus unique factorization: every nontrivial integral combination of `log 2` and
`log 3` is irrational. -/
theorem irrational_int_log_combination (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Irrational ((a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3) := by
  intro hrat
  obtain ⟨q, hq⟩ := hrat
  have hscaled :
      ((q.den : ℤ) * a : ℝ) * Real.log 2 + ((q.den : ℤ) * b : ℝ) * Real.log 3 = q.num := by
    have hden : (q.den : ℝ) ≠ 0 := by positivity
    calc
      ((q.den : ℤ) * a : ℝ) * Real.log 2 + ((q.den : ℤ) * b : ℝ) * Real.log 3 =
          (q.den : ℝ) * ((a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3) := by push_cast; ring
      _ = (q.den : ℝ) * (q : ℝ) := by rw [← hq]
      _ = q.num := by rw [Rat.cast_def]; field_simp
  by_cases hnum : q.num = 0
  · have hzero : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 = 0 := by
      have hden : (q.den : ℝ) ≠ 0 := by positivity
      push_cast at hscaled
      rw [hnum] at hscaled
      apply (mul_eq_zero.mp ?_).resolve_left hden
      convert hscaled using 1 <;> ring
    by_cases ha : a = 0
    · subst a
      have hb : b ≠ 0 := hab.resolve_left (by simp)
      have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      simp only [Int.cast_zero, zero_mul, zero_add] at hzero
      have hbR : (b : ℝ) = 0 := (mul_eq_zero.mp hzero).resolve_right hlog3
      exact hb (by exact_mod_cast hbR)
    · have hirr : Irrational (Real.log 2 / Real.log 3) :=
        Furstenberg.multIndep_two_three.irrational_log_div_log (by norm_num) (by norm_num)
      rw [irrational_iff_ne_rational] at hirr
      apply hirr (-b) a ha
      have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      rw [div_eq_iff hlog3]
      field_simp [Int.cast_ne_zero.mpr ha]
      push_cast
      linarith
  · apply exp_int_ne_rat hnum (((2 : ℚ) ^ ((q.den : ℤ) * a)) *
        ((3 : ℚ) ^ ((q.den : ℤ) * b)))
    rw [← hscaled, Real.exp_add]
    have h2 := exp_int_mul_log_nat ((q.den : ℤ) * a) 2 (by norm_num)
    have h3 := exp_int_mul_log_nat ((q.den : ℤ) * b) 3 (by norm_num)
    push_cast at h2 h3
    push_cast
    rw [← h2, ← h3]

/-- Every nontrivial rational combination of `log 2` and `log 3` is irrational. -/
theorem irrational_rat_log_combination (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Irrational ((a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3) := by
  let A : ℤ := a.num * b.den
  let B : ℤ := b.num * a.den
  let D : ℕ := a.den * b.den
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    rcases hab with ha | hb
    · left
      exact mul_ne_zero (Rat.num_ne_zero.mpr ha) (by exact_mod_cast b.pos.ne')
    · right
      exact mul_ne_zero (Rat.num_ne_zero.mpr hb) (by exact_mod_cast a.pos.ne')
  have hD : D ≠ 0 := Nat.mul_ne_zero a.pos.ne' b.pos.ne'
  have hi := (irrational_int_log_combination A B hAB).div_natCast hD
  convert hi using 1
  rw [Rat.cast_def, Rat.cast_def]
  dsimp [A, B, D]
  push_cast
  field_simp

end NormalNumbers.MasterConjectures
