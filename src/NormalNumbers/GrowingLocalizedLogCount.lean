/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# N1, and a Chebyshev bound on the prime cut

* `card_smooth_le`: `#{1 ≤ m ≤ N : P⁺(m) ≤ Z} ≤ (⌊log₂ N⌋ + 1)^{π(Z)}`.  The exponent vector
  `(v_p(m))_{p ≤ Z}` determines `m`, and each entry is `≤ log₂ N`.
* `le_of_primeCounting`: `Z ≤ 17 (π(Z) + 1)²`, from Chebyshev's
  `Z log 2 − log(Z+1) ≤ ψ(Z) ≤ π(Z) log Z`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset

open Classical in
theorem card_smooth_le (Z N : ℕ) :
    ((Icc 1 N).filter (fun m => ∀ p, p.Prime → p ∣ m → p ≤ Z)).card ≤
      (Nat.log 2 N + 1) ^ Z.primeCounting := by
  classical
  set A := (Icc 1 N).filter (fun m => ∀ p, p.Prime → p ∣ m → p ≤ Z)
  let t : (Nat.primesLE Z) → Finset ℕ := fun _ => range (Nat.log 2 N + 1)
  have hcard : (Fintype.piFinset t).card = (Nat.log 2 N + 1) ^ Z.primeCounting := by
    rw [Fintype.card_piFinset]
    simp only [t, card_range, prod_const, card_univ, Fintype.card_coe,
      Nat.primesLE_card_eq_primeCounting]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun m p => m.factorization p) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro p
    simp only [t, mem_range, Nat.lt_succ_iff]
    have hp : (p : ℕ).Prime := (Nat.mem_primesLE.1 p.2).2
    apply Nat.le_log_of_pow_le (by norm_num)
    calc 2 ^ m.factorization p ≤ (p : ℕ) ^ m.factorization p :=
          Nat.pow_le_pow_left hp.two_le _
      _ ≤ m := Nat.ordProj_le _ (by omega)
      _ ≤ N := hm.1.2
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    apply Nat.eq_of_factorization_eq (by omega) (by omega)
    intro p
    by_cases hpZ : p.Prime ∧ p ≤ Z
    · have := congrFun hab ⟨p, Nat.mem_primesLE.2 ⟨hpZ.2, hpZ.1⟩⟩
      simpa using this
    · have h0 : ∀ m, (∀ q, q.Prime → q ∣ m → q ≤ Z) → m ≠ 0 → m.factorization p = 0 := by
        intro m hm hm0
        by_contra hne
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors
          (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 hne)
        have hdvd : p ∣ m := Nat.dvd_of_mem_primeFactors
          (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 hne)
        exact hpZ ⟨hpp, hm p hpp hdvd⟩
      rw [h0 a ha.2 (by omega), h0 b hb.2 (by omega)]

theorem le_of_primeCounting (Z : ℕ) : (Z : ℝ) ≤ 17 * ((Z.primeCounting : ℝ) + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos Z with rfl | hZ
  · simp
  have h1 := Chebyshev.psi_ge Z
  have h2 := Chebyshev.psi_le_primeCounting_mul_log Z
  set a : ℝ := (Z.primeCounting : ℝ)
  set x : ℝ := (Z : ℝ)
  have hx1 : 1 ≤ x := by simp only [x]; exact_mod_cast hZ
  have ha0 : 0 ≤ a := by positivity
  have hlogZ : Real.log x ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlogZ0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  set t := Real.sqrt (x + 1)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hlt : Real.log (x + 1) ≤ 2 * t := by
    have : Real.log (x + 1) = 2 * Real.log t := by
      rw [← htt, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show 0 < t by rw [Real.sqrt_pos]; linarith)
    linarith
  have hl2 := Real.log_two_gt_d9
  -- `x log 2 ≤ (a+1) · 2t`
  have hmain : x * Real.log 2 ≤ (a + 1) * (2 * t) := by
    have : x * Real.log 2 ≤ a * Real.log x + Real.log (x + 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlogZ ha0]
  have hsq : (x * Real.log 2) ^ 2 ≤ ((a + 1) * (2 * t)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmain 2
  have : x ^ 2 * 0.48 ≤ 4 * (a + 1) ^ 2 * (2 * x) := by
    have e : ((a + 1) * (2 * t)) ^ 2 = 4 * (a + 1) ^ 2 * (x + 1) := by rw [← htt]; ring
    have hl : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg x), sq_nonneg (a + 1)]
  nlinarith [sq_nonneg (a + 1)]

end NormalNumbers.GrowingLocalizedLog
