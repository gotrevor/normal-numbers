/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.Screen

/-!
# Norm and coefficient scale for Pell certificates

The norm of a linear combination of adjacent Pell pairs is independent of
the index up to the alternating sign.  A dyadic denominator with residual
at least `a` therefore requires coefficient size at least `sqrt (a * 2^m)`.
-/

namespace NormalNumbers.SqrtTwoRoutes

/-- The norm of a linear combination of adjacent Pell pairs. -/
@[blueprint (title := "Norm identity for every adjacent-Pell coefficient pair")]
theorem pell_linear_combination_norm (n : ℕ) (u v : ℤ) :
    (u * pellP n + v * pellP (n + 1)) ^ 2 -
      2 * (u * pellQ n + v * pellQ (n + 1)) ^ 2 =
    (-1) ^ n * (u ^ 2 + 2 * u * v - v ^ 2) := by
  have hnorm := pell_norm n
  have hnext := pell_norm (n + 1)
  have hcross : pellP n * pellP (n + 1) -
      2 * pellQ n * pellQ (n + 1) = (-1) ^ n := by
    rw [pellP_succ, pellQ_succ]
    nlinarith [hnorm]
  calc
    _ = u ^ 2 * (pellP n ^ 2 - 2 * pellQ n ^ 2) +
          2 * u * v * (pellP n * pellP (n + 1) -
            2 * pellQ n * pellQ (n + 1)) +
          v ^ 2 * (pellP (n + 1) ^ 2 - 2 * pellQ (n + 1) ^ 2) := by ring
    _ = _ := by rw [hnorm, hcross, hnext, pow_succ]; ring

/-- A dyadic residual bounded below by `a` forces large Pell coefficients.

The interval factorization and the Pell norm identity give a lower bound
directly on the absolute value of the coefficient norm. -/
@[blueprint (title := "A dyadic residual lower-bounds the Pell coefficient norm")]
theorem pell_dyadic_norm_lower
    (n m : ℕ) (P u v : ℤ) (a : ℝ)
    (ha : 0 ≤ a)
    (hP : u * pellP n + v * pellP (n + 1) = P)
    (hQ : u * pellQ n + v * pellQ (n + 1) = 2 ^ m)
    (hwindow : a ≤ (2 : ℝ) ^ m * Real.sqrt 2 - P ∧
      (2 : ℝ) ^ m * Real.sqrt 2 - P ≤ 1) :
    a * (2 : ℝ) ^ m ≤
      |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| := by
  have hQcast : (1 : ℝ) ≤ (2 : ℝ) ^ m :=
    one_le_pow₀ (by norm_num)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hnorm := pell_linear_combination_norm n u v
  have hnormReal :
      ((u * pellP n + v * pellP (n + 1) : ℤ) : ℝ) ^ 2 -
        2 * ((u * pellQ n + v * pellQ (n + 1) : ℤ) : ℝ) ^ 2 =
      ((-1 : ℤ) ^ n : ℝ) *
        ((u ^ 2 + 2 * u * v - v ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast hnorm
  have hPsum :
      ((u * pellP n + v * pellP (n + 1) : ℤ) : ℝ) = (P : ℝ) := by
    exact_mod_cast hP
  have hQsum :
      ((u * pellQ n + v * pellQ (n + 1) : ℤ) : ℝ) = (2 : ℝ) ^ m := by
    exact_mod_cast hQ
  rw [hPsum, hQsum] at hnormReal
  have htheta : 0 ≤ (2 : ℝ) ^ m * Real.sqrt 2 - P :=
    le_trans ha hwindow.1
  have hsum : (2 : ℝ) ^ m ≤ (P : ℝ) + (2 : ℝ) ^ m * Real.sqrt 2 := by
    nlinarith [hwindow.2, hQcast, hsqrt]
  have hQnonneg : 0 ≤ (2 : ℝ) ^ m := le_trans (by norm_num) hQcast
  have hprod :
      a * (2 : ℝ) ^ m ≤
        ((2 : ℝ) ^ m * Real.sqrt 2 - P) *
          ((P : ℝ) + (2 : ℝ) ^ m * Real.sqrt 2) := by
    calc
      a * (2 : ℝ) ^ m ≤
          ((2 : ℝ) ^ m * Real.sqrt 2 - P) * (2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hwindow.1 hQnonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum htheta
  have hnormAbs :
      |(P : ℝ) ^ 2 - 2 * ((2 : ℝ) ^ m) ^ 2| =
        |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| := by
    rw [hnormReal]
    simp
  have hfactor :
      |(P : ℝ) ^ 2 - 2 * ((2 : ℝ) ^ m) ^ 2| =
        ((2 : ℝ) ^ m * Real.sqrt 2 - P) *
          ((P : ℝ) + (2 : ℝ) ^ m * Real.sqrt 2) := by
    rw [show (P : ℝ) ^ 2 - 2 * ((2 : ℝ) ^ m) ^ 2 =
        -(((2 : ℝ) ^ m * Real.sqrt 2 - P) *
          ((P : ℝ) + (2 : ℝ) ^ m * Real.sqrt 2)) by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
    rw [abs_neg, abs_of_nonneg (mul_nonneg htheta (le_trans hQnonneg hsum))]

  calc
    a * (2 : ℝ) ^ m ≤
        ((2 : ℝ) ^ m * Real.sqrt 2 - P) *
          ((P : ℝ) + (2 : ℝ) ^ m * Real.sqrt 2) := hprod
    _ = |(P : ℝ) ^ 2 - 2 * ((2 : ℝ) ^ m) ^ 2| := hfactor.symm
    _ = |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| := hnormAbs

/-- The coefficient quadratic form is bounded by the square of the
coefficient `ℓ¹` size. -/
@[blueprint (title := "Universal absolute bound for the Pell coefficient norm")]
theorem pell_coefficient_norm_bound (u v : ℤ) :
    |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| ≤
      ((|u| : ℝ) + (|v| : ℝ)) ^ 2 := by
  have hcoeff :
      |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| ≤
        ((|u| : ℝ) + (|v| : ℝ)) ^ 2 := by
    calc
      |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| =
          |((u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ)) +
            (-(v : ℝ) ^ 2)| := by ring_nf
      _ ≤ |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ)| + |-(v : ℝ) ^ 2| :=
        abs_add_le _ _
      _ ≤ (|u| : ℝ) ^ 2 + 2 * (|u| : ℝ) * (|v| : ℝ) +
            (|v| : ℝ) ^ 2 := by
        have hsumAbs' :
            |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ)| ≤
              (|u| : ℝ) ^ 2 + 2 * (|u| : ℝ) * (|v| : ℝ) := by
          calc
            _ ≤ |(u : ℝ) ^ 2| + |2 * (u : ℝ) * (v : ℝ)| :=
              abs_add_le _ _
            _ = _ := by simp [abs_mul]
        simp only [abs_neg, abs_pow]
        nlinarith [hsumAbs']
      _ = ((|u| : ℝ) + (|v| : ℝ)) ^ 2 := by ring
  exact hcoeff

/-- Compose the dyadic norm lower bound with the universal coefficient
bound. -/
@[blueprint (title := "Dyadic residual forces quantitative Pell coefficient growth")]
theorem pell_dyadic_coefficient_growth
    (n m : ℕ) (P u v : ℤ) (a : ℝ)
    (ha : 0 ≤ a)
    (hP : u * pellP n + v * pellP (n + 1) = P)
    (hQ : u * pellQ n + v * pellQ (n + 1) = 2 ^ m)
    (hwindow : a ≤ (2 : ℝ) ^ m * Real.sqrt 2 - P ∧
      (2 : ℝ) ^ m * Real.sqrt 2 - P ≤ 1) :
    a * (2 : ℝ) ^ m ≤ ((|u| : ℝ) + (|v| : ℝ)) ^ 2 := by
  exact le_trans (pell_dyadic_norm_lower n m P u v a ha hP hQ hwindow)
    (pell_coefficient_norm_bound u v)

/-- If the coefficient norm is bounded by `K`, then no dyadic certificate
in the stated residual window can have `a * 2^m > K`. -/
@[blueprint (title := "Bounded Pell norm bounds the dyadic exponent scale")]
theorem pell_dyadic_bounded_norm
    (n m : ℕ) (P u v : ℤ) (a K : ℝ)
    (ha : 0 ≤ a)
    (hP : u * pellP n + v * pellP (n + 1) = P)
    (hQ : u * pellQ n + v * pellQ (n + 1) = 2 ^ m)
    (hwindow : a ≤ (2 : ℝ) ^ m * Real.sqrt 2 - P ∧
      (2 : ℝ) ^ m * Real.sqrt 2 - P ≤ 1)
    (hK : |(u : ℝ) ^ 2 + 2 * (u : ℝ) * (v : ℝ) - (v : ℝ) ^ 2| ≤ K) :
    a * (2 : ℝ) ^ m ≤ K :=
  le_trans (pell_dyadic_norm_lower n m P u v a ha hP hQ hwindow) hK

end NormalNumbers.SqrtTwoRoutes
