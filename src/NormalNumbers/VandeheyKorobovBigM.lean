/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovGcd

/-!
# The fixed `M(P)` factor in Vandehey's differencing step

This file proves Claim 4.6 in Vandehey's Proposition 4.1.  If `m'` is the
rounded divisor, `τ = ord(b,m')`, and `m̄ = gcd(b^τ-1,m)`, the claim is
`m̄ / m' ∣ M(P)`, hence `m̄ ≤ M(P)m'`.

The proof avoids importing the paper's exact order formula.  Put
`q = 2 ord(b,∏ P)`.  Exact LTE gives
`v_p(b^(q m')-1) = v_p(b^q-1) + v_p(m')` at every `p ∈ P`, including
`p = 2` because `q` is even.  This first shows `ord(b,m') ∣ q m'`; therefore
`m̄ ∣ b^(q m')-1`, and the same valuation identity bounds the quotient
`m̄/m'` by the corresponding factor of `M(P)`.
-/

open scoped BigOperators
open Finset Nat

namespace NormalNumbers.VandeheyKorobov

open Literature.VandeheyDiff

private lemma four_dvd_odd_sq_sub_one {x : ℕ} (hx : Odd x) :
    4 ∣ x ^ 2 - 1 := by
  obtain ⟨k, hk⟩ := hx
  subst x
  refine ⟨k * (k + 1), ?_⟩
  have hsq : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  omega

/-- `M(P)` is nonzero when `P` consists of primes. -/
lemma bigM_ne_zero (b : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    bigM b P ≠ 0 := by
  unfold bigM
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (hP p hp).ne_zero

/-- The exact prime factorization of Vandehey's fixed factor `M(P)`. -/
lemma bigM_factorization (b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (bigM b P).factorization q =
      if q ∈ P then
        padicValNat q (b ^ (2 * orderOf (b : ZMod (primeProd P))) - 1)
      else 0 := by
  unfold bigM
  rw [Nat.factorization_prod_apply]
  · by_cases hq : q ∈ P
    · rw [if_pos hq, Finset.sum_eq_single q]
      · rw [(hP q hq).factorization_pow]
        exact Finsupp.single_eq_same
      · intro p hp hpq
        rw [(hP p hp).factorization_pow]
        simp [hpq]
      · simp [hq]
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro p hp
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      rw [(hP p hp).factorization_pow]
      simp [hpq]
  · intro p hp
    exact pow_ne_zero _ (hP p hp).ne_zero

/-- Local exact-LTE identity for the exponent used to compare `m'` with `M(P)`. -/
lemma fixed_pow_factorization_eq
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    {m' p : ℕ} (hm' : m' ≠ 0) (hp : p.Prime) (hpP : p ∈ P) :
    (b ^ ((2 * orderOf (b : ZMod (primeProd P))) * m') - 1).factorization p =
      padicValNat p (b ^ (2 * orderOf (b : ZMod (primeProd P))) - 1) +
        m'.factorization p := by
  let Q := primeProd P
  let L := orderOf (b : ZMod Q)
  let q := 2 * L
  have hbQ : Nat.Coprime b Q := by
    dsimp [Q, primeProd]
    rw [Nat.coprime_prod_right_iff]
    intro r hr
    exact (hP r hr).2.symm
  have hLpos : 0 < L := by
    dsimp [L]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b Q).mpr hbQ).isOfFinOrder
  have hq0 : q ≠ 0 := by
    dsimp [q]
    omega
  have hpQ : p ∣ Q := by
    dsimp [Q, primeProd]
    exact Finset.dvd_prod_of_mem _ hpP
  have hpowQ : (b : ZMod Q) ^ L = 1 := by
    dsimp [L]
    exact pow_orderOf_eq_one _
  have hpowpL : (b : ZMod p) ^ L = 1 := by
    have h := congrArg (ZMod.castHom hpQ (ZMod p)) hpowQ
    rwa [map_pow, map_one, map_natCast] at h
  have hpowpq : (b : ZMod p) ^ q = 1 := by
    dsimp [q]
    rw [mul_comm, pow_mul, hpowpL, one_pow]
  have hbqgt : 1 < b ^ q := Nat.one_lt_pow hq0 (by omega)
  have hpq : p ∣ b ^ q - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hbqgt.le]
    push_cast
    rw [hpowpq]
    simp
  have hpb : ¬ p ∣ b := hp.coprime_iff_not_dvd.mp (hP p hpP).2
  have hpnbq : ¬ p ∣ b ^ q := fun h => hpb (hp.dvd_of_dvd_pow h)
  have hfour : p = 2 → 4 ∣ b ^ q - 1 := by
    intro hp2
    subst p
    have hbodd : Odd b := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hpb)
    have hsq : 4 ∣ (b ^ L) ^ 2 - 1 := four_dvd_odd_sq_sub_one hbodd.pow
    have heq : b ^ q = (b ^ L) ^ 2 := by
      dsimp [q]
      rw [show 2 * L = L * 2 by omega, pow_mul]
    rw [heq]
    exact hsq
  rw [show 2 * orderOf (b : ZMod (primeProd P)) = q by rfl,
    pow_mul, Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padicValNat_pow_sub_one_eq_add hp hbqgt hm' hpq hpnbq hfour]

/-- The order modulo `m'` divides the fixed exponent
`2 * ord(b,∏ P) * m'`.  This is the order-lifting interface behind Claim 4.6. -/
lemma orderOf_dvd_fixedExponent_mul_modulus
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m' : ℕ) (hm' : m' ≠ 0) (hsupp : m'.primeFactors ⊆ P) :
    orderOf (b : ZMod m') ∣
      (2 * orderOf (b : ZMod (primeProd P))) * m' := by
  let E := (2 * orderOf (b : ZMod (primeProd P))) * m'
  have hE0 : E ≠ 0 := by
    dsimp [E]
    have hQcop : Nat.Coprime b (primeProd P) := by
      unfold primeProd
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact (hP p hp).2.symm
    have hLpos : 0 < orderOf (b : ZMod (primeProd P)) :=
      orderOf_pos_iff.mpr
        ((ZMod.isUnit_iff_coprime b (primeProd P)).mpr hQcop).isOfFinOrder
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) hLpos.ne') hm'
  have hpow0 : b ^ E - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_iff_lt.mpr (Nat.one_lt_pow hE0 (by omega))
  have hm'pow : m' ∣ b ^ E - 1 := by
    apply (Nat.factorization_le_iff_dvd hm' hpow0).1
    intro p
    by_cases hp : p.Prime
    · by_cases hpm' : p ∣ m'
      · have hpP : p ∈ P :=
          hsupp ((Nat.mem_primeFactors_of_ne_zero hm').2 ⟨hp, hpm'⟩)
        rw [fixed_pow_factorization_eq b hb P hP hm' hp hpP]
        omega
      · simp [Nat.factorization_eq_zero_of_not_dvd hpm']
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  apply orderOf_dvd_of_pow_eq_one
  have hEgt : 1 < b ^ E := Nat.one_lt_pow hE0 (by omega)
  have hz : ((b ^ E - 1 : ℕ) : ZMod m') = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hm'pow
  rw [Nat.cast_sub hEgt.le] at hz
  push_cast at hz
  exact sub_eq_zero.mp hz

/-- **Vandehey, Claim 4.6.**  If `τ = ord(b,m')` and
`m̄ = gcd(b^τ-1,m)`, then `m̄/m'` divides the fixed factor `M(P)`. -/
theorem gcd_pow_orderOf_div_dvd_bigM
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m m' : ℕ) (hm : m ≠ 0) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    mbar / m' ∣ bigM b P := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  have hm' : m' ≠ 0 := by
    intro hz
    subst m'
    simp only [zero_dvd_iff] at hm'dvd
    exact hm hm'dvd
  have hbm' : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b m').mpr hbm').isOfFinOrder
  have hm'pow : m' ∣ b ^ τ - 1 := by
    have hpowgt : 1 < b ^ τ := Nat.one_lt_pow hτpos.ne' (by omega)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpowgt.le]
    push_cast
    dsimp [τ]
    rw [pow_orderOf_eq_one]
    simp
  have hm'mbar : m' ∣ mbar := by
    dsimp [mbar]
    exact Nat.dvd_gcd hm'pow hm'dvd
  have hmbar0 : mbar ≠ 0 := by
    dsimp [mbar]
    exact Nat.gcd_ne_zero_right hm
  have hquot0 : mbar / m' ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hmbar0) hm'mbar)
      (Nat.pos_of_ne_zero hm')).ne'
  have hmbar_m : mbar ∣ m := by
    dsimp [mbar]
    exact Nat.gcd_dvd_right _ _
  have hsuppm' : m'.primeFactors ⊆ P := by
    intro p hp
    exact hsuppm p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hm'dvd)
  have hτdvd : τ ∣ (2 * orderOf (b : ZMod (primeProd P))) * m' := by
    dsimp [τ]
    exact orderOf_dvd_fixedExponent_mul_modulus b hb P hP m' hm' hsuppm'
  let E := (2 * orderOf (b : ZMod (primeProd P))) * m'
  have hE0 : E ≠ 0 := by
    dsimp [E]
    have hQcop : Nat.Coprime b (primeProd P) := by
      unfold primeProd
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact (hP p hp).2.symm
    have hLpos : 0 < orderOf (b : ZMod (primeProd P)) :=
      orderOf_pos_iff.mpr
        ((ZMod.isUnit_iff_coprime b (primeProd P)).mpr hQcop).isOfFinOrder
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) hLpos.ne') hm'
  have hfinal0 : b ^ E - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_iff_lt.mpr (Nat.one_lt_pow hE0 (by omega))
  have hmbar_final : mbar ∣ b ^ E - 1 := by
    have hmbar_tau : mbar ∣ b ^ τ - 1 := by
      dsimp [mbar]
      exact Nat.gcd_dvd_left _ _
    exact hmbar_tau.trans (Nat.pow_sub_one_dvd_pow_sub_one b hτdvd)
  apply (Nat.factorization_le_iff_dvd hquot0
    (bigM_ne_zero b P fun p hp => (hP p hp).1)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpP : p ∈ P
    · have hpmbarfac : mbar.factorization p ≤ (b ^ E - 1).factorization p :=
        (Nat.factorization_le_iff_dvd hmbar0 hfinal0).2 hmbar_final p
      have hfinaleq : (b ^ E - 1).factorization p =
          padicValNat p
              (b ^ (2 * orderOf (b : ZMod (primeProd P))) - 1) +
            m'.factorization p := by
        simpa [E] using fixed_pow_factorization_eq b hb P hP hm' hp hpP
      rw [Nat.factorization_div hm'mbar, Finsupp.tsub_apply, bigM_factorization b P
        (fun p hp => (hP p hp).1), if_pos hpP]
      rw [hfinaleq] at hpmbarfac
      omega
    · have hpnmbar : ¬ p ∣ mbar := by
        intro hpmbar
        exact hpP (hsuppm p hp (hpmbar.trans hmbar_m))
      rw [Nat.factorization_div hm'mbar, Finsupp.tsub_apply, bigM_factorization b P
        (fun p hp => (hP p hp).1), if_neg hpP]
      simp [Nat.factorization_eq_zero_of_not_dvd hpnmbar]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The inequality form of Claim 4.6 used in Proposition 4.1. -/
theorem gcd_pow_orderOf_le_bigM_mul
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m m' : ℕ) (hm : m ≠ 0) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    mbar ≤ bigM b P * m' := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  have hm' : m' ≠ 0 := by
    intro hz
    subst m'
    simp only [zero_dvd_iff] at hm'dvd
    exact hm hm'dvd
  have hbm' : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b m').mpr hbm').isOfFinOrder
  have hm'pow : m' ∣ b ^ τ - 1 := by
    have hpowgt : 1 < b ^ τ := Nat.one_lt_pow hτpos.ne' (by omega)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpowgt.le]
    push_cast
    dsimp [τ]
    rw [pow_orderOf_eq_one]
    simp
  have hm'mbar : m' ∣ mbar := by
    dsimp [mbar]
    exact Nat.dvd_gcd hm'pow hm'dvd
  have hdiv : mbar / m' ∣ bigM b P :=
    gcd_pow_orderOf_div_dvd_bigM b hb P hP m m' hm hm'dvd hbm hsuppm
  have hMpos : 0 < bigM b P :=
    Nat.pos_of_ne_zero (bigM_ne_zero b P fun p hp => (hP p hp).1)
  have hquotle : mbar / m' ≤ bigM b P := Nat.le_of_dvd hMpos hdiv
  calc
    mbar = mbar / m' * m' := (Nat.div_mul_cancel hm'mbar).symm
    _ ≤ bigM b P * m' := Nat.mul_le_mul_right m' hquotle

/-- Claim 4.6 specialized to the rounded divisor from equations (12)--(13). -/
theorem gcd_pow_rounded_orderOf_div_dvd_bigM
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : m ≠ 0) (hbm : Nat.Coprime b m)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    let m' := roundedDivisor m x
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    mbar / m' ∣ bigM b P := by
  exact gcd_pow_orderOf_div_dvd_bigM b hb P hP m (roundedDivisor m x) hm
    (roundedDivisor_dvd hm hx0 hx1) hbm hsuppm

/-- The rounded-divisor inequality `m̄ ≤ M(P)m'` consumed by Proposition 4.1. -/
theorem gcd_pow_rounded_orderOf_le_bigM_mul
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : m ≠ 0) (hbm : Nat.Coprime b m)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    let m' := roundedDivisor m x
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    mbar ≤ bigM b P * m' := by
  exact gcd_pow_orderOf_le_bigM_mul b hb P hP m (roundedDivisor m x) hm
    (roundedDivisor_dvd hm hx0 hx1) hbm hsuppm

end NormalNumbers.VandeheyKorobov
