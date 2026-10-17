/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovDifferencing
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor sums for Vandehey's Korobov estimate

This file proves Vandehey's Lemma 4.2.  The negative-power estimate follows by factoring
the divisor sum into finite geometric series.  The positive-power estimate then follows
from the involution `d ↦ n / d` on the divisors of `n`.
-/

open scoped BigOperators ArithmeticFunction.zeta
open Finset Nat

namespace NormalNumbers.VandeheyKorobov

noncomputable section

private def rpowAF (x : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else (n : ℝ) ^ x
  map_zero' := if_pos rfl

private lemma rpowAF_apply {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    rpowAF x n = (n : ℝ) ^ x := by
  simp [rpowAF, hn]

private lemma rpowAF_isMultiplicative (x : ℝ) : (rpowAF x).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [rpowAF], ?_⟩
  intro m n hm hn hmn
  rw [rpowAF_apply (Nat.mul_ne_zero hm hn), rpowAF_apply hm, rpowAF_apply hn]
  push_cast
  exact Real.mul_rpow (by positivity) (by positivity)

/-- Factor a real-power divisor sum prime by prime. -/
lemma sum_divisors_rpow_eq_prod (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (d : ℝ) ^ x) =
      ∏ p ∈ n.primeFactors,
        ∑ j ∈ range (n.factorization p + 1), ((p : ℝ) ^ x) ^ j := by
  let f := (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) * rpowAF x
  have hf : f.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.mul
      ArithmeticFunction.isMultiplicative_zeta.natCast (rpowAF_isMultiplicative x)
  have hfac := hf.multiplicative_factorization f hn
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hfac
  rw [show (∑ d ∈ n.divisors, (d : ℝ) ^ x) =
      ∑ d ∈ n.divisors, rpowAF x d by
        apply Finset.sum_congr rfl
        intro d hd
        exact (rpowAF_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))).symm]
  rw [hfac, Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [show f (p ^ n.factorization p) =
      ∑ d ∈ (p ^ n.factorization p).divisors, rpowAF x d by
        exact ArithmeticFunction.coe_zeta_mul_apply]
  rw [Nat.sum_divisors_prime_pow hpp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rpowAF_apply (pow_ne_zero _ hpp.ne_zero)]
  push_cast
  rw [← Real.rpow_natCast_mul (by positivity) j x, mul_comm,
    Real.rpow_mul_natCast (by positivity)]

private lemma inv_one_sub_rpow_neg_eq_factor {p : ℕ} (hp : 2 ≤ p)
    {x : ℝ} (hx : 0 < x) :
    (1 - (p : ℝ) ^ (-x))⁻¹ = (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have ht : 1 < (p : ℝ) ^ x := Real.one_lt_rpow hpR hx
  have ht0 : (p : ℝ) ^ x ≠ 0 := by positivity
  have ht1 : (p : ℝ) ^ x - 1 ≠ 0 := by linarith
  rw [Real.rpow_neg (by positivity)]
  field_simp [ht0, ht1]

private lemma sum_prime_rpow_neg_le_factor {p k : ℕ} (hp : 2 ≤ p)
    {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ range (k + 1), ((p : ℝ) ^ (-x)) ^ j) ≤
      (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ (p : ℝ) ^ (-x) := Real.rpow_nonneg (by positivity) _
  have hr1 : (p : ℝ) ^ (-x) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_neg_of_pos hx)
  have hgeom := geom_sum_Ico_le_of_lt_one (x := (p : ℝ) ^ (-x))
    (m := 0) (n := k + 1) hr0 hr1
  rw [Nat.Ico_zero_eq_range, pow_zero, one_div] at hgeom
  exact hgeom.trans_eq (inv_one_sub_rpow_neg_eq_factor hp hx)

private lemma one_le_prime_factor {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 0 < x) :
    1 ≤ (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have ht : 1 < (p : ℝ) ^ x := Real.one_lt_rpow hpR hx
  rw [le_div_iff₀ (sub_pos.mpr ht)]
  linarith

/-- Every Euler factor in `C_{P,x}` is positive for a positive exponent. -/
theorem cP_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {x : ℝ} (hx : 0 < x) :
    0 < Literature.VandeheyDiff.cP P x := by
  unfold Literature.VandeheyDiff.cP
  apply Finset.prod_pos
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).two_le
  have hpow : 1 < (p : ℝ) ^ x := Real.one_lt_rpow hpR hx
  exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (sub_pos.mpr hpow)

/-- Vandehey's Lemma 4.2, negative-power half. -/
theorem sum_divisors_rpow_neg_le_cP (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0)
    (hsupp : n.primeFactors ⊆ P) {x : ℝ} (hx : 0 < x) :
    (∑ d ∈ n.divisors, (d : ℝ) ^ (-x)) ≤
      Literature.VandeheyDiff.cP P x := by
  rw [sum_divisors_rpow_eq_prod (-x) hn]
  unfold Literature.VandeheyDiff.cP
  calc
    (∏ p ∈ n.primeFactors,
        ∑ j ∈ range (n.factorization p + 1), ((p : ℝ) ^ (-x)) ^ j) ≤
        ∏ p ∈ n.primeFactors, (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact sum_prime_rpow_neg_le_factor
          (Nat.prime_of_mem_primeFactors hp).two_le hx
    _ ≤ ∏ p ∈ P, (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsupp
      · intro p hp
        exact (show (0 : ℝ) ≤ 1 by norm_num).trans
          (one_le_prime_factor (Nat.prime_of_mem_primeFactors hp).two_le hx)
      · intro p hp hpn
        exact one_le_prime_factor (hP p hp).two_le hx

/-- Vandehey's Lemma 4.2, positive-power half. -/
theorem sum_divisors_rpow_le_cP_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0)
    (hsupp : n.primeFactors ⊆ P) {x : ℝ} (hx : 0 < x) :
    (∑ d ∈ n.divisors, (d : ℝ) ^ x) ≤
      Literature.VandeheyDiff.cP P x * (n : ℝ) ^ x := by
  calc
    (∑ d ∈ n.divisors, (d : ℝ) ^ x) =
        ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ x := by
      exact (Nat.sum_div_divisors n (fun d : ℕ => (d : ℝ) ^ x)).symm
    _ = ∑ d ∈ n.divisors, (n : ℝ) ^ x * (d : ℝ) ^ (-x) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      rw [Nat.cast_div_charZero hdvd, Real.div_rpow (by positivity) (by positivity),
        Real.rpow_neg (by positivity), div_eq_mul_inv]
    _ = (n : ℝ) ^ x * ∑ d ∈ n.divisors, (d : ℝ) ^ (-x) := by
      rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ x * Literature.VandeheyDiff.cP P x :=
      mul_le_mul_of_nonneg_left (sum_divisors_rpow_neg_le_cP P hP hn hsupp hx)
        (Real.rpow_nonneg (by positivity) _)
    _ = Literature.VandeheyDiff.cP P x * (n : ℝ) ^ x := by
      ring

end

end NormalNumbers.VandeheyKorobov
