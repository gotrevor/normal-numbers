/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassCyclotomic

/-!
# Finite Teichmuller representatives for one prime Stoneham class

For `d = ord_p(b)`, the integer `b^(p^K)` is an approximate primitive `d`-th root of unity.
This file proves the finite-level divisibility statement needed to transfer cyclotomic relations
to the Stoneham numerator arithmetic.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset Polynomial

/-- Reduction of the finite Teichmuller representative modulo its defining prime. -/
lemma teichmullerRepresentative_mod_prime (p b K : ℕ) (hp : p.Prime) :
    ((b : ZMod p) ^ (p ^ K)) = b := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ZMod.pow_card_pow (b : ZMod p)

/-- No cyclotomic factor indexed by a proper divisor of `ord_p(b)` vanishes at the finite
Teichmuller representative modulo `p`. -/
lemma prime_not_dvd_eval_proper_cyclotomic_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    {i : ℕ} (hi : i ∈ (orderOf (b : ZMod p)).properDivisors) :
    ¬ (p : ℤ) ∣ (cyclotomic i ℤ).eval ((b : ℤ) ^ (p ^ K)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (b : ZMod p)
  have hbne : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hp.coprime_iff_not_dvd.mp hbp.symm)
  have hdpred : d ∣ p - 1 := by
    dsimp [d]
    exact ZMod.orderOf_dvd_card_sub_one hbne
  have hp2 : 2 ≤ p := hp.two_le
  have hdle : d ≤ p - 1 := Nat.le_of_dvd (by omega) hdpred
  have hipos : 0 < i := Nat.pos_of_mem_properDivisors hi
  have hilt : i < d := (Nat.mem_properDivisors.mp hi).2
  have hip : i < p := lt_of_lt_of_le hilt (by omega)
  letI : NeZero (i : ZMod p) := ⟨by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hipos hip)
      ((ZMod.natCast_eq_zero_iff i p).mp hzero)⟩
  intro hdiv
  have hzero :
      (((cyclotomic i ℤ).eval ((b : ℤ) ^ (p ^ K)) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
  have hroot : IsRoot (cyclotomic i (ZMod p))
      (((b : ℤ) ^ (p ^ K) : ℤ) : ZMod p) := by
    rw [IsRoot.def, ← map_cyclotomic i (Int.castRingHom (ZMod p))]
    change (Polynomial.map (Int.castRingHom (ZMod p)) (cyclotomic i ℤ)).eval
      ((Int.castRingHom (ZMod p)) ((b : ℤ) ^ (p ^ K))) = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact hzero
  have hprim : IsPrimitiveRoot (b : ZMod p) i := by
    have hw : (((b : ℤ) ^ (p ^ K) : ℤ) : ZMod p) = (b : ZMod p) := by
      simpa only [Int.cast_pow, Int.cast_natCast] using
        teichmullerRepresentative_mod_prime p b K hp
    rw [hw] at hroot
    exact isRoot_cyclotomic_iff.mp hroot
  exact (Nat.ne_of_lt hilt) hprim.eq_orderOf

/-- The proper-divisor cofactor in the factorization of `X^d - 1` is a `p`-adic unit at the
finite Teichmuller representative. -/
lemma prime_not_dvd_proper_cyclotomic_product_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p) :
    ¬ (p : ℤ) ∣
      (∏ i ∈ (orderOf (b : ZMod p)).properDivisors, cyclotomic i ℤ).eval
        ((b : ℤ) ^ (p ^ K)) := by
  rw [eval_prod]
  exact (Nat.prime_iff_prime_int.mp hp).not_dvd_finsetProd fun i hi =>
    prime_not_dvd_eval_proper_cyclotomic_teichmuller p b K hp hbp hi

/-- All of the `p`-power in `b^(d*p^K) - 1`, where `d = ord_p(b)`, lies in the `d`-th
cyclotomic factor.  The other factors are units modulo `p` by the preceding lemma. -/
lemma prime_pow_dvd_cyclotomic_eval_teichmuller_of_pow_sub_one
    (p b K N : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    (hlift : (p : ℤ) ^ N ∣
      ((b : ℤ) ^ (p ^ K)) ^ orderOf (b : ZMod p) - 1) :
    (p : ℤ) ^ N ∣
      (cyclotomic (orderOf (b : ZMod p)) ℤ).eval ((b : ℤ) ^ (p ^ K)) := by
  let d := orderOf (b : ZMod p)
  have hdpos : 0 < d := by
    dsimp [d]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  let Q : ℤ[X] := ∏ i ∈ d.properDivisors, cyclotomic i ℤ
  have hfactor :
      (cyclotomic d ℤ).eval ((b : ℤ) ^ (p ^ K)) *
          Q.eval ((b : ℤ) ^ (p ^ K)) =
        ((b : ℤ) ^ (p ^ K)) ^ d - 1 := by
    have hpoly := (eq_cyclotomic_iff (R := ℤ) hdpos (cyclotomic d ℤ)).mp rfl
    have heval := congrArg (Polynomial.eval ((b : ℤ) ^ (p ^ K))) hpoly
    simpa [Q, eval_prod] using heval
  apply (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right N
    (prime_not_dvd_proper_cyclotomic_product_teichmuller p b K hp hbp)
  rw [hfactor]
  exact hlift

/-- At depth `K`, the value of the `ord_p(b)`-th cyclotomic polynomial at `b^(p^K)` contains
at least `K` copies of `p`.  This includes the dyadic case and is the uniform finite-level
bridge used below. -/
lemma prime_pow_dvd_cyclotomic_eval_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p) :
    (p : ℤ) ^ K ∣
      (cyclotomic (orderOf (b : ZMod p)) ℤ).eval ((b : ℤ) ^ (p ^ K)) := by
  let d := orderOf (b : ZMod p)
  have hbne : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hbp.symm
  have hdpos : 0 < d := by
    dsimp [d]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    simp only [Nat.coprime_zero_left] at hbp
    exact hp.ne_one hbp
  have hbaseOne : 1 ≤ b ^ d := Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.2 hb0)
  have hbaseMod : b ^ d ≡ 1 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [d] using pow_orderOf_eq_one (b : ZMod p)
  have hbaseDvd : p ∣ b ^ d - 1 := hbaseMod.symm.dvd'
  obtain ⟨a, ha⟩ := hbaseDvd
  have hshape : b ^ d = 1 + p * a := by omega
  have hliftNat : p ^ K ∣ (b ^ (p ^ K)) ^ d - 1 := by
    have hlift := pow_pow_modEq_one p K a
    rw [← hshape] at hlift
    rw [show (b ^ d) ^ (p ^ K) = (b ^ (p ^ K)) ^ d by
      rw [← pow_mul, ← pow_mul, mul_comm]] at hlift
    exact hlift.symm.dvd'
  have hliftInt : (p : ℤ) ^ K ∣ ((b : ℤ) ^ (p ^ K)) ^ d - 1 := by
    obtain ⟨c, hc⟩ := hliftNat
    refine ⟨(c : ℤ), ?_⟩
    have hge : 1 ≤ (b ^ (p ^ K)) ^ d :=
      Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.2 hb0))
    exact_mod_cast hc
  exact prime_pow_dvd_cyclotomic_eval_teichmuller_of_pow_sub_one
    p b K K hp hbp (by simpa [d] using hliftInt)

/-- For an odd prime, lifting the exponent supplies the extra digit predicted by Lemma 3' (K):
`Phi_d(b^(p^K))` is divisible by `p^(K+1)`. -/
lemma odd_prime_pow_succ_dvd_cyclotomic_eval_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hb : 2 ≤ b)
    (hbp : Nat.Coprime b p) :
    (p : ℤ) ^ (K + 1) ∣
      (cyclotomic (orderOf (b : ZMod p)) ℤ).eval ((b : ℤ) ^ (p ^ K)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (b : ZMod p)
  have hdpos : 0 < d := by
    dsimp [d]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  have hbaseMod : b ^ d ≡ 1 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [d] using pow_orderOf_eq_one (b : ZMod p)
  have hbaseDvd : p ∣ b ^ d - 1 := hbaseMod.symm.dvd'
  have hpnb : ¬ p ∣ b := hp.coprime_iff_not_dvd.mp hbp.symm
  have hpbase : ¬ p ∣ b ^ d := fun h => hpnb (hp.dvd_of_dvd_pow h)
  have hbasegt : 1 < b ^ d := Nat.one_lt_pow hdpos.ne' (by omega)
  have hpowne : (b ^ d) ^ (p ^ K) - 1 ≠ 0 := by
    have : 1 < (b ^ d) ^ (p ^ K) := Nat.one_lt_pow (pow_ne_zero K hp.ne_zero) hbasegt
    omega
  have hlte := padicValNat.pow_sub_pow (p := p) (x := b ^ d) (y := 1)
    (hp.odd_of_ne_two hp2) hbasegt hbaseDvd hpbase (pow_ne_zero K hp.ne_zero)
  rw [one_pow, padicValNat.prime_pow] at hlte
  have hbaseVal : 1 ≤ padicValNat p (b ^ d - 1) :=
    one_le_padicValNat_of_dvd (by omega) hbaseDvd
  have hval : K + 1 ≤ padicValNat p ((b ^ d) ^ (p ^ K) - 1) := by
    rw [hlte]
    omega
  have hliftNat : p ^ (K + 1) ∣ (b ^ (p ^ K)) ^ d - 1 := by
    have h := (padicValNat_dvd_iff_le hpowne).2 hval
    rw [show (b ^ d) ^ (p ^ K) = (b ^ (p ^ K)) ^ d by
      rw [← pow_mul, ← pow_mul, mul_comm]] at h
    exact h
  have hliftInt : (p : ℤ) ^ (K + 1) ∣ ((b : ℤ) ^ (p ^ K)) ^ d - 1 := by
    obtain ⟨c, hc⟩ := hliftNat
    refine ⟨(c : ℤ), ?_⟩
    have hge : 1 ≤ (b ^ (p ^ K)) ^ d :=
      Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by omega))
    exact_mod_cast hc
  exact prime_pow_dvd_cyclotomic_eval_teichmuller_of_pow_sub_one
    p b K (K + 1) hp hbp (by simpa [d] using hliftInt)

/-- Dyadic extra precision in Lemma 3' (K).  For odd `b`, the representative
`b^(2^(K+1))` is a root of `Phi_1 = X - 1` modulo `2^(K+3)`. -/
lemma two_pow_add_three_dvd_cyclotomic_eval_teichmuller
    (b K : ℕ) (hb : 2 ≤ b) (hb2 : Nat.Coprime b 2) :
    (2 : ℤ) ^ (K + 3) ∣
      (cyclotomic (orderOf (b : ZMod 2)) ℤ).eval ((b : ℤ) ^ (2 ^ (K + 1))) := by
  have h2nb : ¬ 2 ∣ b := Nat.prime_two.coprime_iff_not_dvd.mp hb2.symm
  have hbodd : Odd b := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hd : orderOf (b : ZMod 2) = 1 := by
    rw [orderOf_eq_one_iff]
    exact ZMod.natCast_eq_one_iff_odd.mpr hbodd
  have hnne : 2 ^ (K + 1) ≠ 0 := by positivity
  have hneven : Even (2 ^ (K + 1)) := by
    rw [even_iff_two_dvd]
    exact dvd_pow_self 2 (by omega)
  have hpowne : b ^ (2 ^ (K + 1)) - 1 ≠ 0 := by
    have : 1 < b ^ (2 ^ (K + 1)) := Nat.one_lt_pow hnne (by omega)
    omega
  have hval0 := padicValNat.pow_two_sub_one_ge (x := b) (n := 2 ^ (K + 1))
    (by omega) h2nb hnne hneven
  rw [padicValNat.prime_pow] at hval0
  have hval : K + 3 ≤ padicValNat 2 (b ^ (2 ^ (K + 1)) - 1) := by omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hliftNat : 2 ^ (K + 3) ∣ (b ^ (2 ^ (K + 1))) ^ orderOf (b : ZMod 2) - 1 := by
    rw [hd, pow_one]
    exact (padicValNat_dvd_iff_le hpowne).2 hval
  have hliftInt : (2 : ℤ) ^ (K + 3) ∣
      ((b : ℤ) ^ (2 ^ (K + 1))) ^ orderOf (b : ZMod 2) - 1 := by
    obtain ⟨c, hc⟩ := hliftNat
    refine ⟨(c : ℤ), ?_⟩
    have hge : 1 ≤ (b ^ (2 ^ (K + 1))) ^ orderOf (b : ZMod 2) := by
      rw [hd, pow_one]
      exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast hc
  exact prime_pow_dvd_cyclotomic_eval_teichmuller_of_pow_sub_one
    2 b (K + 1) (K + 3) Nat.prime_two hb2 hliftInt

/-- A cleared cyclotomic relation therefore vanishes modulo `p^K` at the finite Teichmuller
representative. -/
lemma prime_pow_dvd_integerRelation_eval_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic (orderOf (b : ZMod p)) ℤ ∣ integerRelationPolynomial m a) :
    (p : ℤ) ^ K ∣ ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^ m i := by
  exact (prime_pow_dvd_cyclotomic_eval_teichmuller p b K hp hbp).trans
    (cyclotomic_eval_dvd_integerRelation_eval m a ((b : ℤ) ^ (p ^ K)) hdiv)

/-- The odd-prime precision survives evaluation of any cleared cyclotomic relation. -/
lemma odd_prime_pow_succ_dvd_integerRelation_eval_teichmuller
    (p b K : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hb : 2 ≤ b)
    (hbp : Nat.Coprime b p) {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic (orderOf (b : ZMod p)) ℤ ∣ integerRelationPolynomial m a) :
    (p : ℤ) ^ (K + 1) ∣ ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^ m i := by
  exact (odd_prime_pow_succ_dvd_cyclotomic_eval_teichmuller p b K hp hp2 hb hbp).trans
    (cyclotomic_eval_dvd_integerRelation_eval m a ((b : ℤ) ^ (p ^ K)) hdiv)

/-- The extra dyadic precision likewise survives evaluation of a cleared relation. -/
lemma two_pow_add_three_dvd_integerRelation_eval_teichmuller
    (b K : ℕ) (hb : 2 ≤ b) (hb2 : Nat.Coprime b 2)
    {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic (orderOf (b : ZMod 2)) ℤ ∣ integerRelationPolynomial m a) :
    (2 : ℤ) ^ (K + 3) ∣ ∑ i, a i * ((b : ℤ) ^ (2 ^ (K + 1))) ^ m i := by
  exact (two_pow_add_three_dvd_cyclotomic_eval_teichmuller b K hb hb2).trans
    (cyclotomic_eval_dvd_integerRelation_eval m a ((b : ℤ) ^ (2 ^ (K + 1))) hdiv)

/-- A dependent family admits one nonzero integral relation whose value at every finite
Teichmuller representative contains the full prescribed power of `p`. -/
lemma exists_integerRelation_prime_pow_dvd_teichmuller_of_not_linearIndependent
    (p b : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p) {r : ℕ} (m : Fin r → ℕ)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hdep : ¬ LinearIndependent ℚ (fun i ↦ ζ ^ m i)) :
    ∃ a : Fin r → ℤ, a ≠ 0 ∧
      ∀ K, (p : ℤ) ^ K ∣ ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^ m i := by
  have hd : orderOf (b : ZMod p) ≠ 0 :=
    orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  obtain ⟨a, ha, hdiv⟩ :=
    (not_linearIndependent_powers_iff_exists_integer_cyclotomic hd hζ m).mp hdep
  exact ⟨a, ha, fun K =>
    prime_pow_dvd_integerRelation_eval_teichmuller p b K hp hbp m a hdiv⟩

end NormalNumbers.StonehamPrimeClass
