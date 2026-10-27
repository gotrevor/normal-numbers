/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.Screen

/-!
# Balanced adjacent-Pell coordinates

For a near-integer target with denominator `Q`, choose the last adjacent
Pell denominator below `sqrt Q`.  Both synthesis coefficients then have
height at most `4 * sqrt Q`.
-/

namespace NormalNumbers.SqrtTwoRoutes

theorem pellQ_ge_nat (n : ℕ) : (n : ℤ) ≤ pellQ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := pell_positive n
      rw [pellQ_succ]
      omega

theorem pellP_le_two_pellQ (n : ℕ) (hn : 1 ≤ n) :
    pellP n ≤ 2 * pellQ n := by
  cases n with
  | zero => omega
  | succ m =>
      rw [pellP_succ, pellQ_succ]
      have hp := pell_positive m
      omega

theorem pellQ_succ_le_three (n : ℕ) (hn : 1 ≤ n) :
    pellQ (n + 1) ≤ 3 * pellQ n := by
  rw [pellQ_succ]
  have hp := pellP_le_two_pellQ n hn
  omega

theorem pellQ_pos_of_pos_index (n : ℕ) (hn : 1 ≤ n) :
    0 < pellQ n := by
  have h := pell_positive n
  cases n with
  | zero => omega
  | succ m =>
      have hp := pell_positive m
      rw [pellQ_succ]
      omega

theorem pellError_abs_le_inv_pellQ (n : ℕ) (hn : 1 ≤ n) :
    |pellError n| ≤ 1 / (pellQ n : ℝ) := by
  have hqposZ := pellQ_pos_of_pos_index n hn
  have hqpos : 0 < (pellQ n : ℝ) := by exact_mod_cast hqposZ
  have hp := pell_positive n
  have hs2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnorm : (pellP n : ℝ) ^ 2 - 2 * (pellQ n : ℝ) ^ 2 = ((-1 : ℤ) ^ n : ℝ) := by
    exact_mod_cast pell_norm n
  have hnormR : (pellP n : ℝ) ^ 2 - 2 * (pellQ n : ℝ) ^ 2 = (-1 : ℝ) ^ n := by
    simpa using hnorm
  have hfactor : pellError n * ((pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ)) =
      ((-1 : ℝ) ^ n) := by
    unfold pellError
    nlinarith [hnormR, hs2]
  have hq : 0 ≤ (pellQ n : ℝ) := by exact_mod_cast hp.2.1
  have hpR : 0 ≤ (pellP n : ℝ) := by exact_mod_cast hp.1.le
  have hden : (pellQ n : ℝ) ≤ (pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ) := by
    have hs : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hq]
  have hdenpos : 0 < (pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ) := by
    have hp' : 0 < (pellP n : ℝ) := by exact_mod_cast hp.1
    nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hq]
  have habs : |pellError n| * ((pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ)) = 1 := by
    calc
      |pellError n| * ((pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ)) =
          |pellError n| * |(pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ)| := by
            rw [abs_of_pos hdenpos]
      _ = |pellError n * ((pellP n : ℝ) + Real.sqrt 2 * (pellQ n : ℝ))| :=
          (abs_mul _ _).symm
      _ = 1 := by rw [hfactor]; simp
  rw [le_div_iff₀ hqpos]
  nlinarith [abs_nonneg (pellError n), mul_nonneg (abs_nonneg (pellError n)) (sub_nonneg.mpr hden)]

theorem sqrtQ_pos (Q : ℤ) (hQ : 1 ≤ Q) :
    0 < Real.sqrt (Q : ℝ) := by
  apply Real.sqrt_pos.2
  exact_mod_cast (show 0 < Q by omega)

theorem exists_pellQ_succ_above_sqrt (Q : ℤ) (_hQ : 1 ≤ Q) :
    ∃ m : ℕ, Real.sqrt (Q : ℝ) < (pellQ (m + 1) : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.sqrt (Q : ℝ))
  refine ⟨m, ?_⟩
  have hq := pellQ_ge_nat (m + 1)
  have hm' : Real.sqrt (Q : ℝ) < (m : ℝ) := hm
  have hq' : (m + 1 : ℝ) ≤ (pellQ (m + 1) : ℝ) := by exact_mod_cast hq
  linarith

/-- Adjacent Pell coordinates at the sqrt-denominator scale keep both
synthesis coefficients below four times that scale for every target within
one unit of `Q * sqrt 2`. -/
@[blueprint (title := "Balanced Pell coordinates have square-root height")]
theorem balanced_pell_coefficients (Q P : ℤ) (hQ : 1 ≤ Q)
    (hP : |(P : ℝ) - (Q : ℝ) * Real.sqrt 2| ≤ 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (pellQ n : ℝ) ≤ Real.sqrt (Q : ℝ) ∧
      Real.sqrt (Q : ℝ) < (pellQ (n + 1) : ℝ) ∧
      |(coeffU n P Q : ℝ)| ≤ 4 * Real.sqrt (Q : ℝ) ∧
      |(coeffV n P Q : ℝ)| ≤ 4 * Real.sqrt (Q : ℝ) := by
  obtain ⟨n, hn⟩ := Nat.findX (exists_pellQ_succ_above_sqrt Q hQ)
  have hsuccess : Real.sqrt (Q : ℝ) < (pellQ (n + 1) : ℝ) := hn.1
  have hleast : ∀ m < n, ¬ Real.sqrt (Q : ℝ) < (pellQ (m + 1) : ℝ) := by
    exact hn.2
  have hnpos : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have hroot' : (1 : ℝ) ≤ Real.sqrt (Q : ℝ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by exact_mod_cast hQ)
    have hq1 : pellQ (0 + 1) = 1 := by norm_num [pellQ, pellPair]
    have hq1R : (pellQ (0 + 1) : ℝ) = 1 := by exact_mod_cast hq1
    rw [hq1R] at hsuccess
    linarith
  have hqle : (pellQ n : ℝ) ≤ Real.sqrt (Q : ℝ) := by
    by_contra h
    have hlt : Real.sqrt (Q : ℝ) < (pellQ n : ℝ) := lt_of_not_ge h
    have hn' : n - 1 < n := by omega
    have := hleast (n - 1) hn'
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx] at this
    exact this hlt
  have hqnposZ := pellQ_pos_of_pos_index n hnpos
  have hqnpos : 0 < (pellQ n : ℝ) := by exact_mod_cast hqnposZ
  have hqnext : (pellQ (n + 1) : ℝ) ≤ 3 * (pellQ n : ℝ) := by
    exact_mod_cast pellQ_succ_le_three n hnpos
  have hqnle : (pellQ n : ℝ) ≤ Real.sqrt (Q : ℝ) := hqle
  have hspos := sqrtQ_pos Q hQ
  have hqn_gt : Real.sqrt (Q : ℝ) / 3 < (pellQ n : ℝ) := by
    nlinarith [hqnext, hsuccess]
  have hqnext_gt : Real.sqrt (Q : ℝ) < (pellQ (n + 1) : ℝ) := hsuccess
  have hroot_sq : (Real.sqrt (Q : ℝ)) ^ 2 = (Q : ℝ) := Real.sq_sqrt (by positivity)
  have hdelta : |(P : ℝ) - (Q : ℝ) * Real.sqrt 2| ≤ 1 := hP
  have hpbound : (pellP n : ℝ) ≤ 2 * (pellQ n : ℝ) := by
    exact_mod_cast pellP_le_two_pellQ n hnpos
  have hpn := pell_positive (n + 1)
  have hpnextbound : (pellP (n + 1) : ℝ) ≤ 2 * (pellQ (n + 1) : ℝ) := by
    exact_mod_cast pellP_le_two_pellQ (n + 1) (by omega)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm_error_n : |pellError n| ≤ 1 / (pellQ n : ℝ) :=
    pellError_abs_le_inv_pellQ n hnpos
  have hnorm_error_next : |pellError (n + 1)| ≤ 1 / (pellQ (n + 1) : ℝ) :=
    pellError_abs_le_inv_pellQ (n + 1) (by omega)
  have hu_identity :
      (coeffU n P Q : ℝ) = (-1 : ℝ)^n *
        (((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ (n + 1) : ℝ) -
          (Q : ℝ) * pellError (n + 1)) := by
    simp only [coeffU, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_sub]
    unfold pellError
    ring
  have hv_identity :
      (coeffV n P Q : ℝ) = (-1 : ℝ)^n *
        ((Q : ℝ) * pellError n -
          ((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ n : ℝ)) := by
    simp only [coeffV, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_sub]
    unfold pellError
    ring
  refine ⟨n, hnpos, hqle, hsuccess, ?_, ?_⟩
  · rw [hu_identity]
    have hsign : |(-1 : ℝ)^n| = 1 := by simp
    rw [abs_mul, hsign, one_mul]
    have hqposnext : 0 < (pellQ (n + 1) : ℝ) := by
      exact_mod_cast pellQ_pos_of_pos_index (n + 1) (by omega)
    have hE := hnorm_error_next
    have hQnonneg : 0 ≤ (Q : ℝ) := by exact_mod_cast (show 0 ≤ Q by omega)
    have hmul : (Q : ℝ) * |pellError (n + 1)| ≤ (Q : ℝ) / (pellQ (n + 1) : ℝ) := by
      calc
        (Q : ℝ) * |pellError (n + 1)| ≤ (Q : ℝ) * (1 / (pellQ (n + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hE hQnonneg
        _ = (Q : ℝ) / (pellQ (n + 1) : ℝ) := by ring
    have hQroot : (Q : ℝ) / (pellQ (n + 1) : ℝ) ≤ Real.sqrt (Q : ℝ) := by
      rw [div_le_iff₀ hqposnext]
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Q : ℝ))
        (sub_nonneg.mpr (le_of_lt hqnext_gt)), hroot_sq]
    calc
      |((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ (n + 1) : ℝ) -
          (Q : ℝ) * pellError (n + 1)|
          ≤ |(P : ℝ) - (Q : ℝ) * Real.sqrt 2| * (pellQ (n + 1) : ℝ) +
              (Q : ℝ) * |pellError (n + 1)| := by
                calc
                  _ ≤ |((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ (n + 1) : ℝ)| +
                      |(Q : ℝ) * pellError (n + 1)| := abs_sub _ _
                  _ = _ := by rw [abs_mul, abs_of_pos hqposnext, abs_mul,
                    abs_of_nonneg hQnonneg]
      _ ≤ (pellQ (n + 1) : ℝ) + Real.sqrt (Q : ℝ) := by
            nlinarith [hmul, hQroot, hdelta]
      _ ≤ 4 * Real.sqrt (Q : ℝ) := by nlinarith [hqnext, hqle]
  · rw [hv_identity]
    have hsign : |(-1 : ℝ)^n| = 1 := by simp
    rw [abs_mul, hsign]
    have hE := hnorm_error_n
    have hQnonneg : 0 ≤ (Q : ℝ) := by exact_mod_cast (show 0 ≤ Q by omega)
    have hmul : (Q : ℝ) * |pellError n| ≤ (Q : ℝ) / (pellQ n : ℝ) := by
      calc
        (Q : ℝ) * |pellError n| ≤ (Q : ℝ) * (1 / (pellQ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hE hQnonneg
        _ = (Q : ℝ) / (pellQ n : ℝ) := by ring
    have hQroot : (Q : ℝ) / (pellQ n : ℝ) ≤ 3 * Real.sqrt (Q : ℝ) := by
      rw [div_le_iff₀ hqnpos]
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Q : ℝ))
        (sub_nonneg.mpr (by linarith [hqn_gt])), hroot_sq]
    calc
      1 * |(Q : ℝ) * pellError n -
          ((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ n : ℝ)| =
          |(Q : ℝ) * pellError n -
            ((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ n : ℝ)| := by ring
      _ ≤ (Q : ℝ) * |pellError n| +
              |(P : ℝ) - (Q : ℝ) * Real.sqrt 2| * (pellQ n : ℝ) := by
                calc
                  _ ≤ |(Q : ℝ) * pellError n| +
                      |((P : ℝ) - (Q : ℝ) * Real.sqrt 2) * (pellQ n : ℝ)| := abs_sub _ _
                  _ = _ := by rw [abs_mul, abs_of_nonneg hQnonneg, abs_mul,
                    abs_of_pos hqnpos]
      _ ≤ 3 * Real.sqrt (Q : ℝ) + (pellQ n : ℝ) := by
            nlinarith [hmul, hQroot, hdelta]
      _ ≤ 4 * Real.sqrt (Q : ℝ) := by nlinarith [hqle]

end NormalNumbers.SqrtTwoRoutes
