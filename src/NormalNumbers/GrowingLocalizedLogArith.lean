/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# N3–N5: the arithmetic of the truncated sums `R_n`

For a set of indices `S`, `R_n = Σ_{m ≤ n, m ∈ S} 2^{n−m}/m`.  At a *clean* time `n`
(every `m ∈ S` with `m ≤ n` has `m < 2^{n−m}`), we write `R_n = T/D`, where
`D = oddD Z n = ∏_{p ≤ Z odd prime} p^{⌊log_p n⌋}` and `T ∈ ℕ`.  Then:

* `D` is odd, its prime factors are `≤ Z`, and `D ≤ n^{π(Z)}`;
* `3 ∤ T`, because only `3^K` and `2·3^K` (with `K = ⌊log₃ n⌋`) carry the full `3^K`, and their
  numerators `2^a + 2^{a − 3^K − 1}` have an even exponent gap.  So `3^K ∣ den R_n`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset

/-- `D = ∏_{p ≤ Z odd prime} p^{⌊log_p n⌋}`. -/
def oddD (Z n : ℕ) : ℕ := ∏ p ∈ (Nat.primesLE Z).filter (· ≠ 2), p ^ Nat.log p n

lemma mem_oddPrimes {Z p : ℕ} : p ∈ (Nat.primesLE Z).filter (· ≠ 2) ↔ p.Prime ∧ p ≤ Z ∧ p ≠ 2 := by
  simp [Nat.primesLE_eq_filter_range]; tauto

lemma oddD_pos (Z n : ℕ) : 0 < oddD Z n :=
  Finset.prod_pos fun p hp => pow_pos (mem_oddPrimes.1 hp).1.pos _

lemma prime_dvd_oddD {Z n q : ℕ} (hq : q.Prime) (h : q ∣ oddD Z n) : q ≤ Z ∧ q ≠ 2 := by
  obtain ⟨p, hp, hd⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h
  have hp' := mem_oddPrimes.1 hp
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp'.1).1 (hq.dvd_of_dvd_pow hd)
  subst this; exact ⟨hp'.2.1, hp'.2.2⟩

lemma two_not_dvd_oddD (Z n : ℕ) : ¬ 2 ∣ oddD Z n := fun h =>
  (prime_dvd_oddD Nat.prime_two h).2 rfl

lemma oddD_le (Z n : ℕ) (hn : 1 ≤ n) : oddD Z n ≤ n ^ Z.primeCounting := by
  unfold oddD
  calc ∏ p ∈ (Nat.primesLE Z).filter (· ≠ 2), p ^ Nat.log p n
      ≤ n ^ ((Nat.primesLE Z).filter (· ≠ 2)).card :=
        Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p (by omega)
    _ ≤ n ^ Z.primeCounting := by
        apply Nat.pow_le_pow_right hn
        rw [← Nat.primesLE_card_eq_primeCounting]; exact Finset.card_filter_le _ _

/-- Every clean index divides `2^{n−m} D`. -/
lemma dvd_two_pow_mul_oddD {Z n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hsupp : ∀ p, p.Prime → p ∣ m → p ≤ Z) (hgap : m < 2 ^ (n - m)) :
    m ∣ 2 ^ (n - m) * oddD Z n := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpm : p ∣ m := (dvd_pow_self p hk.ne').trans hpk
  have hle : p ^ k ≤ m := Nat.le_of_dvd (by omega) hpk
  by_cases h2 : p = 2
  · subst h2
    apply Dvd.dvd.mul_right
    apply pow_dvd_pow
    have : 2 ^ k < 2 ^ (n - m) := lt_of_le_of_lt hle hgap
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 this).le
  · apply Dvd.dvd.mul_left
    have hmem : p ∈ (Nat.primesLE Z).filter (· ≠ 2) :=
      mem_oddPrimes.2 ⟨hp, hsupp p hp hpm, h2⟩
    refine (pow_dvd_pow p ?_).trans (Finset.dvd_prod_of_mem _ hmem)
    exact Nat.le_log_of_pow_le hp.one_lt (hle.trans hmn)

/-- The `3`-part of `D`: `D = 3^{⌊log₃ n⌋} · D'` with `3 ∤ D'`. -/
def oddD' (Z n : ℕ) : ℕ := ∏ p ∈ ((Nat.primesLE Z).filter (· ≠ 2)).erase 3, p ^ Nat.log p n

lemma oddD_eq (Z n : ℕ) (h3 : 3 ≤ Z) : oddD Z n = 3 ^ Nat.log 3 n * oddD' Z n := by
  unfold oddD oddD'
  exact (Finset.mul_prod_erase _ (fun p => p ^ Nat.log p n)
    (mem_oddPrimes.2 ⟨Nat.prime_three, h3, by norm_num⟩)).symm

lemma three_not_dvd_oddD' (Z n : ℕ) : ¬ 3 ∣ oddD' Z n := by
  intro h
  obtain ⟨p, hp, hd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).1 h
  have hp3 := Finset.ne_of_mem_erase hp
  have hp' := mem_oddPrimes.1 (Finset.mem_of_mem_erase hp)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp'.1).1
    (Nat.prime_three.dvd_of_dvd_pow hd)).symm

/-- Clean time `n` for the index set `S` and prime bound `Z`. -/
structure CleanAt (S : ℕ → Prop) (Z n : ℕ) : Prop where
  supp : ∀ m p, S m → 1 ≤ m → m ≤ n → p.Prime → p ∣ m → p ≤ Z
  gap : ∀ m, S m → 1 ≤ m → m ≤ n → m < 2 ^ (n - m)

/-- Indices not divisible by `3^K` contribute a multiple of `3`. -/
lemma three_mul_dvd {S : ℕ → Prop} {Z n m : ℕ} (h : CleanAt S Z n) (h3 : 3 ≤ Z)
    (hS : S m) (hm : 1 ≤ m) (hmn : m ≤ n) (hK : ¬ 3 ^ Nat.log 3 n ∣ m) :
    3 * m ∣ 2 ^ (n - m) * oddD Z n := by
  have hbase := dvd_two_pow_mul_oddD hm hmn (fun p hp hpm => h.supp m p hS hm hmn hp hpm)
    (h.gap m hS hm hmn)
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hp3 : p = 3
  · subst hp3
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ', Nat.mul_dvd_mul_iff_left (by norm_num)] at hpk
    have hjK : j < Nat.log 3 n := by
      by_contra hc; push Not at hc
      exact hK ((pow_dvd_pow 3 hc).trans hpk)
    apply Dvd.dvd.mul_left
    rw [oddD_eq Z n h3]
    exact (pow_dvd_pow 3 (by omega)).trans (dvd_mul_right _ _)
  · have hcop : Nat.Coprime (p ^ k) 3 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    exact (hcop.dvd_of_dvd_mul_left hpk).trans hbase

open Classical in
/-- `R_n = Σ_{m ≤ n, m ∈ S} 2^{n−m}/m`. -/
noncomputable def Rs (S : ℕ → Prop) (n : ℕ) : ℚ :=
  ∑ m ∈ Icc 1 n, if S m then (2 : ℚ) ^ (n - m) / m else 0

open Classical in
/-- The numerator `T = Σ_{m ≤ n, m ∈ S} 2^{n−m} D / m`. -/
noncomputable def Tnum (S : ℕ → Prop) (Z n : ℕ) : ℕ :=
  ∑ m ∈ Icc 1 n, if S m then 2 ^ (n - m) * oddD Z n / m else 0

theorem Rs_eq {S : ℕ → Prop} {Z n : ℕ} (h : CleanAt S Z n) :
    Rs S n = (Tnum S Z n : ℚ) / oddD Z n := by
  classical
  have hD : (oddD Z n : ℚ) ≠ 0 := by exact_mod_cast (oddD_pos Z n).ne'
  unfold Rs Tnum
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  split_ifs with hS
  · have hdv := dvd_two_pow_mul_oddD hm.1 hm.2 (fun p hp hpm => h.supp m p hS hm.1 hm.2 hp hpm)
      (h.gap m hS hm.1 hm.2)
    rw [Nat.cast_div hdv (by exact_mod_cast (by omega : m ≠ 0))]
    push_cast
    have : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    field_simp
  · simp

lemma two_pow_even_zmod3 (j : ℕ) : (2 : ZMod 3) ^ (2 * j) = 1 := by
  rw [pow_mul]; norm_num
  rw [show (4 : ZMod 3) = 1 from rfl, one_pow]

/-- **N4: `3 ∤ T`.** -/
theorem three_not_dvd_Tnum {S : ℕ → Prop} {Z n : ℕ} (h : CleanAt S Z n) (h3 : 3 ≤ Z)
    (hn : 1 ≤ n) (hS1 : S (3 ^ Nat.log 3 n)) (hS2 : S (2 * 3 ^ Nat.log 3 n)) :
    ¬ 3 ∣ Tnum S Z n := by
  classical
  set K := Nat.log 3 n with hKdef
  set D' := oddD' Z n
  have hKn : 3 ^ K ≤ n := Nat.pow_log_le_self 3 (by omega)
  have hnK : n < 3 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hK1 : 1 ≤ 3 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hDeq := oddD_eq Z n h3
  have hD'3 : (D' : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact three_not_dvd_oddD' Z n
  -- termwise values mod 3
  let g : ℕ → ZMod 3 := fun m =>
    if m = 3 ^ K then (2 : ZMod 3) ^ (n - 3 ^ K) * D'
    else if m = 2 * 3 ^ K then (2 : ZMod 3) ^ (n - 2 * 3 ^ K - 1) * D' else 0
  have hterm : ∀ m ∈ Icc 1 n,
      (((if S m then 2 ^ (n - m) * oddD Z n / m else 0 : ℕ)) : ZMod 3) = g m := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    simp only [g]
    by_cases e1 : m = 3 ^ K
    · subst e1
      rw [if_pos hS1, if_pos rfl, hDeq]
      rw [show 2 ^ (n - 3 ^ K) * (3 ^ K * D') = 3 ^ K * (2 ^ (n - 3 ^ K) * D') by ring,
        Nat.mul_div_cancel_left _ (by positivity)]
      push_cast; ring
    by_cases e2 : m = 2 * 3 ^ K
    · subst e2
      have hgap := h.gap _ hS2 hm.1 hm.2
      have h1 : 1 ≤ n - 2 * 3 ^ K := by
        by_contra hc; push Not at hc
        rw [show n - 2 * 3 ^ K = 0 by omega] at hgap; omega
      rw [if_pos hS2, if_neg e1, if_pos rfl, hDeq]
      have : 2 ^ (n - 2 * 3 ^ K) = 2 * 2 ^ (n - 2 * 3 ^ K - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this, show 2 * 2 ^ (n - 2 * 3 ^ K - 1) * (3 ^ K * D') =
        (2 * 3 ^ K) * (2 ^ (n - 2 * 3 ^ K - 1) * D') by ring,
        Nat.mul_div_cancel_left _ (by positivity)]
      push_cast; ring
    rw [if_neg e1, if_neg e2]
    split_ifs with hS
    · have hnd : ¬ 3 ^ K ∣ m := by
        rintro ⟨c, rfl⟩
        have hc : c < 3 := by
          by_contra hc; push Not at hc
          have : 3 ^ K * 3 ≤ 3 ^ K * c := Nat.mul_le_mul_left _ hc
          rw [← pow_succ] at this; omega
        interval_cases c
        · omega
        · exact e1 (by ring)
        · exact e2 (by ring)
      have h3m := three_mul_dvd h h3 hS hm.1 hm.2 hnd
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at h3m)
    · simp
  rw [← ZMod.natCast_eq_zero_iff, Tnum, Nat.cast_sum]
  rw [Finset.sum_congr rfl hterm]
  have hne : 2 * 3 ^ K ≠ 3 ^ K := by omega
  set A : ZMod 3 := (2 : ZMod 3) ^ (n - 3 ^ K) * D'
  set B : ZMod 3 := (2 : ZMod 3) ^ (n - 2 * 3 ^ K - 1) * D'
  have hg : ∀ m, g m = (if 3 ^ K = m then A else 0) + (if 2 * 3 ^ K = m then B else 0) := by
    intro m; simp only [g]
    by_cases e1 : m = 3 ^ K
    · subst e1; simp [hne, A]
    · rw [if_neg e1, if_neg (Ne.symm e1), zero_add]
      by_cases e2 : m = 2 * 3 ^ K
      · subst e2; simp [B]
      · rw [if_neg e2, if_neg (Ne.symm e2)]
  rw [Finset.sum_congr rfl (fun m _ => hg m), Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  have hmem1 : 3 ^ K ∈ Icc 1 n := Finset.mem_Icc.2 ⟨hK1, hKn⟩
  rw [if_pos hmem1]
  have hodd : Odd (3 ^ K) := Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hodd
  by_cases h2n : 2 * 3 ^ K ≤ n
  · rw [if_pos (Finset.mem_Icc.2 ⟨by omega, h2n⟩)]
    have hgap := h.gap _ hS2 (by omega) h2n
    have h1 : 1 ≤ n - 2 * 3 ^ K := by
      by_contra hc; push Not at hc
      rw [show n - 2 * 3 ^ K = 0 by omega] at hgap; omega
    have hexp : n - 3 ^ K = (n - 2 * 3 ^ K - 1) + 2 * (j + 1) := by omega
    simp only [A, B]
    rw [hexp, pow_add, two_pow_even_zmod3]
    have : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → y * 1 * x + y * x ≠ 0 := by decide
    exact this _ _ hD'3 (pow_ne_zero _ (by decide))
  · rw [if_neg (fun hm => h2n (Finset.mem_Icc.1 hm).2), add_zero]
    exact mul_ne_zero (pow_ne_zero _ (by decide)) hD'3

/-- **N5 (denominator bounds).**  At a clean time, `den(h R_n)` divides the odd number
`D = oddD Z n`, and `3^{⌊log₃ n⌋} ≤ den(h R_n) · |h|`. -/
theorem den_bounds {S : ℕ → Prop} {Z n : ℕ} (h : CleanAt S Z n) (h3 : 3 ≤ Z)
    (hn : 1 ≤ n) (hS1 : S (3 ^ Nat.log 3 n)) (hS2 : S (2 * 3 ^ Nat.log 3 n)) (a : ℤ)
    (ha : a ≠ 0) :
    ((a : ℚ) * Rs S n).den ∣ oddD Z n ∧
      3 ^ Nat.log 3 n ≤ ((a : ℚ) * Rs S n).den * a.natAbs := by
  have hR := Rs_eq h
  set T := Tnum S Z n
  set D := oddD Z n
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (oddD_pos Z n).ne'
  constructor
  · have e : (a : ℚ) * Rs S n = Rat.divInt (a * T) D := by
      rw [hR, Rat.divInt_eq_div]; push_cast; ring
    rw [e]
    have := Rat.den_dvd (a * T) D
    exact_mod_cast this
  · -- `3^K ∣ den R_n`
    set q := Rs S n
    have hK : 3 ^ Nat.log 3 n ∣ q.den := by
      have hq : (q.num : ℚ) / q.den = (T : ℚ) / D := by rw [Rat.num_div_den, hR]
      have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
      have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
      rw [div_eq_div_iff hqd hDq] at hq
      have hz : q.num * (D : ℤ) = (T : ℤ) * q.den := by exact_mod_cast hq
      have h3D : (3 ^ Nat.log 3 n : ℤ) ∣ (T : ℤ) * q.den := by
        rw [← hz]; apply Dvd.dvd.mul_left
        rw [show D = oddD Z n from rfl, oddD_eq Z n h3]; push_cast; exact dvd_mul_right _ _
      have hcop : IsCoprime ((3 : ℤ) ^ Nat.log 3 n) (T : ℤ) := by
        apply IsCoprime.pow_left
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime 3 T :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (three_not_dvd_Tnum h h3 hn hS1 hS2)
        exact_mod_cast this
      have := hcop.dvd_of_dvd_mul_left h3D
      exact_mod_cast this
    have hmul : q = ((a : ℚ) * q) * (a : ℚ)⁻¹ := by
      field_simp
    have hd : q.den ∣ ((a : ℚ) * q).den * (a : ℚ)⁻¹.den := by
      conv_lhs => rw [hmul]
      exact Rat.mul_den_dvd _ _
    rw [Rat.inv_intCast_den, if_neg ha] at hd
    exact Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos _) (Int.natAbs_pos.2 ha)) (hK.trans hd)

end NormalNumbers.GrowingLocalizedLog
