/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.JointLambertRescaledTail

/-!
# Exact valuation witnesses on the rescaled Lambert schedule

The analytic tail construction already supplies the progression and the selected survivor
prime.  This file retains the prime allocation and turns the CRT residues into exact
factorization exponents, with no additional analytic input.
-/

namespace NormalNumbers.JointLambert

open Finset
open NormalNumbers.SwingC2

@[blueprint (title := "Exact prime valuations survive Lambert carry-tail selection")]
theorem exists_exact_valuation_small_tail
    (e E r : ℕ) (he : 1 ≤ e) (hE : 1 ≤ E) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) (K N : ℕ) :
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j, j < k → j ≠ r →
        ∃ P : Finset ℕ, P.card = j + 1 ∧
          ∀ p ∈ P, p.Prime ∧ (n + j).factorization p = e) ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n + r = q ^ E * p) ∧
      (∑' t : ℕ, (tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) < ε) := by
  classical
  have hc : 2 ≤ e + 1 := by omega
  have ha : 2 ≤ E + 1 := by omega
  obtain ⟨k, n, q, p, R, A, u, m, hkK, hkr, hn1, hnN, hkill, hsurv, htail,
    hqprime, hpdata, hpinj, hRu, hA, hres, hn, hmprime, humod⟩ :=
    exists_joint_small_tail_rescaled_with_witnesses (c := e + 1) (a := E + 1) hc ha hr
      hε K N
  refine ⟨k, n, hkK, hkr, hn1, hnN, ?_, ?_, htail⟩
  · intro j hj hjr
    let P : Finset ℕ := (range (j + 1)).image (p j)
    refine ⟨P, ?_, ?_⟩
    · dsimp [P]
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro t ht t' ht' heq
      exact (hpinj j t j t' hj hjr (Finset.mem_range.mp ht) hj hjr
        (Finset.mem_range.mp ht') heq).2
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      have htr : t < j + 1 := Finset.mem_range.mp ht
      have hpp := (hpdata j t hj hjr htr).1
      refine ⟨hpp, ?_⟩
      have hslotA : slotProd p j ^ (e + 1) ∣ A := by
        rw [hA]
        simp only [jointA, killCore, killedIdx]
        exact Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem _
            (Finset.mem_erase.mpr ⟨hjr, Finset.mem_range.mpr hj⟩)) _
      have hnmod : n + j ≡ slotProd p j ^ e [MOD slotProd p j ^ (e + 1)] := by
        rw [hn]
        have heq : R + m * A + j = (R + j) + m * A := by omega
        rw [heq]
        have hstep : (R + j) + m * A ≡ (R + j) + 0
            [MOD slotProd p j ^ (e + 1)] :=
          Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hslotA m))
        have hres' := hres j hj hjr
        simpa [show e + 1 - 1 = e by omega] using hstep.trans hres'
      have hSW : slotProd p j = p j t * ∏ t' ∈ (range (j + 1)).erase t, p j t' := by
        simp only [slotProd]
        exact (Finset.mul_prod_erase _ _ ht).symm
      have hcopW : Nat.Coprime (p j t) (∏ t' ∈ (range (j + 1)).erase t, p j t') := by
        refine Nat.Coprime.prod_right fun t' ht' => ?_
        have ht'r := Finset.mem_range.mp (Finset.mem_of_mem_erase ht')
        refine (Nat.coprime_primes hpp (hpdata j t' hj hjr ht'r).1).2 fun heq => ?_
        exact (Finset.mem_erase.mp ht').1
          ((hpinj j t j t' hj hjr htr hj hjr ht'r heq).2).symm
      have hPW : ¬ p j t ∣ (∏ t' ∈ (range (j + 1)).erase t, p j t') ^ e := by
        intro hd
        exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcopW
          (hpp.prime.dvd_of_dvd_pow hd)
      have hpow : p j t ^ (e + 1) ∣ slotProd p j ^ (e + 1) := by
        refine pow_dvd_pow_of_dvd ?_ _
        simp only [slotProd]
        exact Finset.dvd_prod_of_mem _ ht
      have hcong : n + j ≡
          p j t ^ e * (∏ t' ∈ (range (j + 1)).erase t, p j t') ^ e
          [MOD p j t ^ (e + 1)] := by
        have h1 := hnmod.of_dvd hpow
        rw [hSW, mul_pow] at h1
        exact h1
      have hn0 : n + j ≠ 0 := by omega
      have hfac := factorization_eq_of_modEq_unit hpp hn0 hPW hcong
      simpa using hfac
  · have hqB : q ∣ jointB (e + 1) k r q p := by
      simp [jointB]
    have hzero : Nat.ModEq q (m * jointB (e + 1) k r q p) 0 :=
      (Nat.modEq_zero_iff_dvd).2 (dvd_mul_of_dvd_right hqB m)
    have hxmod : Nat.ModEq q (u + m * jointB (e + 1) k r q p) 1 := by
      have h1 := humod.add_right (m * jointB (e + 1) k r q p)
      have h2 := Nat.ModEq.add_left 1 hzero
      simpa using h1.trans h2
    have hne : q ≠ u + m * jointB (e + 1) k r q p := by
      intro heq
      have hqdiv : q ∣ u + m * jointB (e + 1) k r q p := by
        rw [← heq]
      have hmod0 : Nat.ModEq q (u + m * jointB (e + 1) k r q p) 0 :=
        (Nat.modEq_zero_iff_dvd).2 hqdiv
      have honezero : Nat.ModEq q 1 0 := hxmod.symm.trans hmod0
      have hqone : q ∣ 1 := (Nat.modEq_zero_iff_dvd).mp honezero
      exact hqprime.not_dvd_one hqone
    have hsurveq : n + r = q ^ E * (u + m * jointB (e + 1) k r q p) := by
      rw [hn]
      have h1 : R + m * A + r = (R + r) + m * A := by omega
      rw [h1, hRu, hA]
      simp [jointA, jointB, jointQ, show (E + 1) - 1 = E by omega]
      ring
    exact ⟨u + m * jointB (e + 1) k r q p, q, hmprime, hqprime,
      hne.symm, hsurveq⟩

end NormalNumbers.JointLambert

#print axioms NormalNumbers.JointLambert.exists_exact_valuation_small_tail
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail_rescaled
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail_all_bases_rescaled
#print axioms NormalNumbers.JointLambert.exists_joint_prime_candidates_rescaled
