/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.WordCertificate

/-!
# A 2-adic Pell-index lift: exact effect and scale

If a Pell index makes `q_n` divisible by a word modulus, then the denominator
equation forces the coefficient of the adjacent denominator to be divisible
by that modulus, provided the adjacent denominator is a unit modulo it.
The scale bounds below are necessary costs, not an existence construction.
The synthesis-coefficient congruences hold for every numerator and do not
select the word interval.
-/

namespace NormalNumbers.SqrtTwoRoutes

/-- If a lifted index and a dyadic denominator both contain `2^L`, the
crossing condition `q_n^2≤2^m` forces `m≥2n−2`.  Since a nonzero index
divisible by `2^L` is at least `2^L`, this makes the exponent scale at least
`2^(L+1)−2`. -/
@[blueprint (title := "Balanced lifted Pell indices require an exponential word-length scale")]
theorem pell_index_lift_size_lower_bound
    (L n m : ℕ) (hn : 1 ≤ n) (hnL : 2 ^ L ≤ n)
    (hcross : pellQ n ^ 2 ≤ (2 : ℤ) ^ m) :
    2 * n ≤ m + 2 ∧ 2 ^ (L + 1) ≤ m + 2 := by
  have hqlo : (2 : ℤ) ^ (n - 1) ≤ pellQ n := by
    have h := pell_denominator_growth (n - 1)
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx] at h
    exact h
  have hqnonneg : 0 ≤ pellQ n := (pell_positive n).2.1
  have hsq : ((2 : ℤ) ^ (n - 1)) ^ 2 ≤ (pellQ n) ^ 2 :=
    (sq_le_sq₀ (by positivity) hqnonneg).mpr hqlo
  have hpowInt : (2 : ℤ) ^ (2 * (n - 1)) ≤ (2 : ℤ) ^ m := by
    calc
      (2 : ℤ) ^ (2 * (n - 1)) = (2 : ℤ) ^ ((n - 1) * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℤ) ^ (n - 1)) ^ 2 := by rw [← pow_mul]
      _ ≤ (pellQ n) ^ 2 := hsq
      _ ≤ (2 : ℤ) ^ m := hcross
  have hpowNat : 2 ^ (2 * (n - 1)) ≤ 2 ^ m := by exact_mod_cast hpowInt
  have hexp : 2 * (n - 1) ≤ m :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowNat
  constructor
  · omega
  · calc
      2 ^ (L + 1) = 2 ^ L * 2 := by rw [pow_succ]
      _ ≤ 2 * n := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hnL
      _ ≤ m + 2 := by omega

/-- A denominator congruence transfers to the adjacent coefficient when the
adjacent Pell denominator is a unit modulo the selected word modulus.  The
unit is supplied as an explicit Bezout identity. -/
theorem pell_index_lift_forces_adjacent_coefficient_divisible
    (S Q u v q qnext : ℤ)
    (hden : u * q + v * qnext = Q)
    (hQ : S ∣ Q) (hq : S ∣ q)
    (hunit : ∃ x y : ℤ, x * qnext + y * S = 1) :
    S ∣ v := by
  have hqterm : S ∣ u * q := by
    rcases hq with ⟨k, hk⟩
    exact ⟨u * k, by rw [hk]; ring⟩
  have hprod : S ∣ v * qnext := by
    have hdiff : S ∣ Q - u * q := dvd_sub hQ hqterm
    have heq : Q - u * q = v * qnext := by linarith
    rw [heq] at hdiff
    exact hdiff
  rcases hprod with ⟨k, hk⟩
  rcases hunit with ⟨x, y, hxy⟩
  refine ⟨x * k + y * v, ?_⟩
  calc
    v = v * (x * qnext + y * S) := by rw [hxy]; ring
    _ = x * (v * qnext) + y * (v * S) := by ring
    _ = x * (S * k) + y * (v * S) := by rw [hk]
    _ = S * (x * k + y * v) := by ring

/-- Whenever `S` divides both `Q` and `q_n`, the coefficient `v` from the
adjacent-Pell synthesis is divisible by `S`, for every numerator `P`.  The
numerator cancels identically from this coordinate. -/
@[blueprint (title := "Pell index-lift coefficient divisibility holds for every numerator")]
theorem pell_index_lift_coeffV_divisible_for_every_numerator
    (S : ℤ) (n : ℕ) (P Q : ℤ)
    (hQ : S ∣ Q) (hq : S ∣ pellQ n) :
    S ∣ coeffV n P Q := by
  have hfirst : S ∣ Q * pellP n := by
    rcases hQ with ⟨k, hk⟩
    exact ⟨k * pellP n, by rw [hk]; ring⟩
  have hsecond : S ∣ P * pellQ n := by
    rcases hq with ⟨k, hk⟩
    exact ⟨P * k, by rw [hk]; ring⟩
  have hterm : S ∣ Q * pellP n - P * pellQ n := dvd_sub hfirst hsecond
  rcases hterm with ⟨k, hk⟩
  refine ⟨(-1 : ℤ) ^ n * k, ?_⟩
  unfold coeffV
  rw [hk]
  ring

/-- Under the same hypotheses, `coeffU` is congruent modulo `S` to its
`P*q_(n+1)` term.  This congruence also holds for every numerator `P`. -/
theorem pell_index_lift_coeffU_congruent_for_every_numerator
    (S : ℤ) (n : ℕ) (P Q : ℤ)
    (hQ : S ∣ Q) :
    S ∣ coeffU n P Q - (-1 : ℤ) ^ n * P * pellQ (n + 1) := by
  rcases hQ with ⟨k, hk⟩
  refine ⟨(-1 : ℤ) ^ n * (-k * pellP (n + 1)), ?_⟩
  unfold coeffU
  rw [hk]
  ring

/-- A nonzero coefficient divisible by `2^L` must pay at least `2^L` in
absolute value.  Under the balanced Pell box this only requires
`2^L ≤ 4*sqrt(Q)`. -/
theorem pell_index_lift_archimedean_cost
    (L : ℕ) (Q v : ℤ)
    (hvne : v ≠ 0)
    (hdiv : (2 : ℤ) ^ L ∣ v)
    (hbound : |(v : ℝ)| ≤ 4 * Real.sqrt (Q : ℝ)) :
    (2 : ℝ) ^ L ≤ 4 * Real.sqrt (Q : ℝ) := by
  rcases hdiv with ⟨k, hk⟩
  have hkne : k ≠ 0 := by
    intro hk0
    rw [hk0] at hk
    simp at hk
    exact hvne hk
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hi : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
    exact_mod_cast hi
  have hpow : 0 < ((2 : ℤ) ^ L : ℝ) := by positivity
  have hkR : (v : ℝ) = ((2 : ℤ) ^ L : ℝ) * (k : ℝ) := by exact_mod_cast hk
  rw [hkR, abs_mul, abs_of_pos hpow] at hbound
  calc
    (2 : ℝ) ^ L = (2 : ℝ) ^ L * 1 := by ring
    _ ≤ (2 : ℝ) ^ L * |(k : ℝ)| := mul_le_mul_of_nonneg_left hkabs hpow.le
    _ ≤ 4 * Real.sqrt (Q : ℝ) := hbound

/-- A reachable scale control: index `n=4` has `q₄=12`, `q₅=29`, so
`q₄²≤2⁸<q₅²`; the denominator `2⁸` has bounded synthesis coefficients
`(u,v)=(2,8)`, with `4∣q₄` and `4∣v`.  It certifies the word `00`. -/
@[blueprint (title := "A 2-adically lifted index reaches a bounded 00 certificate")]
theorem exponent_lift_00_control :
    PellWordCertificate 2 0 8 4 2 8 := by
  norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]

theorem exponent_lift_00_values :
    pellQ 4 = 12 ∧ pellQ 5 = 29 ∧
      coeffU 4 362 256 = 2 ∧ coeffV 4 362 256 = 8 ∧
      (4 : ℤ) ∣ pellQ 4 ∧ (4 : ℤ) ∣ coeffV 4 362 256 := by
  norm_num [coeffU, coeffV, pellP, pellQ, pellPair]

/-- The same reachable state fails the neighboring `01` cylinder.  Thus the
index divisibility and coefficient box do not themselves certify the word
value; the signed square window remains the discriminating condition. -/
@[blueprint (title := "The lifted-index control does not certify the neighboring word")]
theorem exponent_lift_neighbor_rejected :
    ¬ PellWordCertificate 2 1 8 4 2 8 := by
  norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]

end NormalNumbers.SqrtTwoRoutes
