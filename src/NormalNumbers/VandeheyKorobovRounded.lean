/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovCounting

/-!
# Rounded supported divisors for Vandehey's Korobov estimate

This file formalizes equations (12)--(13) in the proof of Vandehey's Proposition 4.1.
The paper's `Q` there is the product of the distinct primes actually dividing `m`.  The
frozen Lean theorem instead packages its constants using the product over the ambient set
`P`, which may contain primes not dividing `m`.  We perform the rounding over the actual
prime support of `m`, as in the paper, and then bound that support product by the ambient
prime product.

At each supported prime the exponent is `⌊x v_p(m)⌋ + 1`.  If `4 ∣ m` and this gives
only one factor of `2`, one further factor of `2` is inserted.  Thus the construction
preserves the exceptional `4 ∣ m` case used in Claim 4.5.
-/

open scoped BigOperators
open Finset Nat

namespace NormalNumbers.VandeheyKorobov

/-- The one extra factor of `2` needed when the ordinary rounding would lose `4 ∣ m`. -/
noncomputable def roundedCorrection (m : ℕ) (x : ℝ) (p : ℕ) : ℕ :=
  if p = 2 ∧ 4 ∣ m ∧ ⌊x * m.factorization p⌋₊ = 0 then 1 else 0

/-- The exponent used for `p` in the rounded supported divisor. -/
noncomputable def roundedExponent (m : ℕ) (x : ℝ) (p : ℕ) : ℕ :=
  ⌊x * m.factorization p⌋₊ + 1 + roundedCorrection m x p

/-- Vandehey's rounded divisor, with rounding over the actual prime support of `m`. -/
noncomputable def roundedDivisor (m : ℕ) (x : ℝ) : ℕ :=
  ∏ p ∈ m.primeFactors, p ^ roundedExponent m x p

/-- The squarefree product of the prime support of `m`. -/
def supportProd (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

lemma roundedExponent_pos (m : ℕ) (x : ℝ) (p : ℕ) :
    0 < roundedExponent m x p := by
  unfold roundedExponent
  omega

lemma roundedExponent_le_factorization {m : ℕ} (hm : m ≠ 0) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) {p : ℕ} (hp : p ∈ m.primeFactors) :
    roundedExponent m x p ≤ m.factorization p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 0 < m.factorization p :=
    hpp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)
  have hxe0 : 0 ≤ x * (m.factorization p : ℝ) := mul_nonneg hx0 (by positivity)
  have hxe : x * (m.factorization p : ℝ) < (m.factorization p : ℝ) := by
    have heR : (0 : ℝ) < m.factorization p := by exact_mod_cast he
    simpa using mul_lt_mul_of_pos_right hx1 heR
  have hfloor : ⌊x * (m.factorization p : ℝ)⌋₊ < m.factorization p :=
    (Nat.floor_lt hxe0).2 hxe
  unfold roundedExponent roundedCorrection
  split_ifs with hcorr
  · have hp2 : p = 2 := hcorr.1
    subst p
    have htwo : 2 ≤ m.factorization 2 := by
      rw [← Nat.prime_two.pow_dvd_iff_le_factorization hm]
      norm_num
      exact hcorr.2.1
    simp only [hcorr.2.2, zero_add]
    omega
  · omega

lemma roundedDivisor_dvd {m : ℕ} (hm : m ≠ 0) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) : roundedDivisor m x ∣ m := by
  unfold roundedDivisor
  calc
    (∏ p ∈ m.primeFactors, p ^ roundedExponent m x p) ∣
        ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
        pow_dvd_pow p (roundedExponent_le_factorization hm hx0 hx1 hp)
    _ = m := by
      simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hm

lemma roundedDivisor_ne_zero (m : ℕ) (x : ℝ) :
    roundedDivisor m x ≠ 0 := by
  unfold roundedDivisor
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma roundedDivisor_factorization (m : ℕ) (x : ℝ) (q : ℕ) :
    (roundedDivisor m x).factorization q =
      if q ∈ m.primeFactors then roundedExponent m x q else 0 := by
  unfold roundedDivisor
  rw [Nat.factorization_prod_apply]
  · by_cases hq : q ∈ m.primeFactors
    · rw [if_pos hq, Finset.sum_eq_single q]
      · rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow]
        exact Finsupp.single_eq_same
      · intro p hp hpq
        rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow]
        simp [hpq]
      · simp [hq]
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro p hp
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow]
      simp [hpq]
  · intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma roundedDivisor_primeFactors {m : ℕ} (hm : m ≠ 0) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (roundedDivisor m x).primeFactors = m.primeFactors := by
  apply Finset.Subset.antisymm
  · exact Nat.primeFactors_mono (roundedDivisor_dvd hm hx0 hx1) hm
  · intro p hp
    apply (Nat.mem_primeFactors_of_ne_zero (roundedDivisor_ne_zero m x)).2
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    apply Nat.dvd_of_factorization_pos
    rw [roundedDivisor_factorization m x p, if_pos hp]
    exact (roundedExponent_pos m x p).ne'

lemma four_dvd_roundedDivisor {m : ℕ} (hm : m ≠ 0) (x : ℝ) (h4 : 4 ∣ m) :
    4 ∣ roundedDivisor m x := by
  have h2m : 2 ∈ m.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hm).2 ⟨Nat.prime_two, dvd_trans (by norm_num) h4⟩
  rw [show 4 = 2 ^ 2 by norm_num,
    Nat.prime_two.pow_dvd_iff_le_factorization (roundedDivisor_ne_zero m x),
    roundedDivisor_factorization m x 2, if_pos h2m]
  unfold roundedExponent roundedCorrection
  by_cases hf : ⌊x * (m.factorization 2 : ℝ)⌋₊ = 0
  · simp [h4, hf]
  · have : 1 ≤ ⌊x * (m.factorization 2 : ℝ)⌋₊ := Nat.one_le_iff_ne_zero.mpr hf
    split <;> omega

lemma natCast_rpow_eq_prod_primeFactors {m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    (m : ℝ) ^ x =
      ∏ p ∈ m.primeFactors, (p : ℝ) ^ (x * m.factorization p) := by
  have hmprod : (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m := by
    simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hm
  have hmprodR : (∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p) = (m : ℝ) := by
    exact_mod_cast hmprod
  rw [← hmprodR]
  induction m.primeFactors using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp,
        Real.mul_rpow (by positivity) (by positivity), ih]
      congr 1
      rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ p by positivity)]
      congr 1
      ring

lemma prime_rpow_le_roundedFactor {m : ℕ} {x : ℝ} {p : ℕ}
    (hp : p ∈ m.primeFactors) :
    (p : ℝ) ^ (x * m.factorization p) ≤
      (p : ℝ) ^ roundedExponent m x p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hbase : (1 : ℝ) ≤ p := by exact_mod_cast hpp.two_le.trans' (by omega)
  have hfloor : x * (m.factorization p : ℝ) <
      (⌊x * (m.factorization p : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hexp : x * (m.factorization p : ℝ) ≤ (roundedExponent m x p : ℕ) := by
    unfold roundedExponent
    push_cast
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le hbase hexp
  simpa only [Real.rpow_natCast] using h

lemma roundedFactor_le {m : ℕ} {x : ℝ} (hx0 : 0 ≤ x)
    {p : ℕ} (hp : p ∈ m.primeFactors) :
    (p : ℝ) ^ roundedExponent m x p ≤
      (p : ℝ) ^ roundedCorrection m x p * p *
        (p : ℝ) ^ (x * m.factorization p) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.two_le.trans' (by omega)
  have hxe0 : 0 ≤ x * (m.factorization p : ℝ) := mul_nonneg hx0 (by positivity)
  have hfloor : (⌊x * (m.factorization p : ℝ)⌋₊ : ℝ) ≤
      x * m.factorization p := Nat.floor_le hxe0
  have hexp : (roundedExponent m x p : ℕ) ≤
      x * m.factorization p + 1 + roundedCorrection m x p := by
    unfold roundedExponent
    push_cast
    linarith
  calc
    (p : ℝ) ^ roundedExponent m x p =
        (p : ℝ) ^ (roundedExponent m x p : ℝ) := by
          rw [Real.rpow_natCast]
    _ ≤ (p : ℝ) ^
        (x * m.factorization p + 1 + roundedCorrection m x p) :=
      Real.rpow_le_rpow_of_exponent_le hp1 hexp
    _ = (p : ℝ) ^ roundedCorrection m x p * p *
        (p : ℝ) ^ (x * m.factorization p) := by
      rw [Real.rpow_add hp0, Real.rpow_add hp0, Real.rpow_one,
        Real.rpow_natCast]
      ring

lemma correction_prod_le_two {m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    (∏ p ∈ m.primeFactors, (p : ℝ) ^ roundedCorrection m x p) ≤ 2 := by
  by_cases h : 4 ∣ m ∧ ⌊x * (m.factorization 2 : ℝ)⌋₊ = 0
  · have h2m : 2 ∈ m.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hm).2
        ⟨Nat.prime_two, dvd_trans (by norm_num) h.1⟩
    rw [← Finset.mul_prod_erase m.primeFactors
      (fun p => (p : ℝ) ^ roundedCorrection m x p) h2m]
    have herase : (∏ p ∈ m.primeFactors.erase 2,
        (p : ℝ) ^ roundedCorrection m x p) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
      simp [roundedCorrection, hpne]
    rw [herase]
    simp [roundedCorrection, h]
  · have hz : ∀ p, roundedCorrection m x p = 0 := by
      intro p
      by_cases hp2 : p = 2
      · subst p
        by_cases h4 : 4 ∣ m
        · have hf : ⌊x * (m.factorization 2 : ℝ)⌋₊ ≠ 0 := fun hf => h ⟨h4, hf⟩
          simp [roundedCorrection, h4, hf]
        · simp [roundedCorrection, h4]
      · simp [roundedCorrection, hp2]
    simp_rw [hz]
    simp

lemma roundedDivisor_lower {m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    (m : ℝ) ^ x ≤ roundedDivisor m x := by
  rw [natCast_rpow_eq_prod_primeFactors hm x]
  unfold roundedDivisor
  push_cast
  exact Finset.prod_le_prod (fun p hp => Real.rpow_nonneg (by positivity) _)
    (fun p hp => prime_rpow_le_roundedFactor hp)

lemma roundedDivisor_upper {m : ℕ} (hm : m ≠ 0) {x : ℝ} (hx0 : 0 ≤ x) :
    (roundedDivisor m x : ℝ) ≤
      2 * supportProd m * (m : ℝ) ^ x := by
  have hfactor : (roundedDivisor m x : ℝ) ≤
      ∏ p ∈ m.primeFactors,
        ((p : ℝ) ^ roundedCorrection m x p * p *
          (p : ℝ) ^ (x * m.factorization p)) := by
    unfold roundedDivisor
    push_cast
    exact Finset.prod_le_prod (fun p hp => by positivity)
      (fun p hp => roundedFactor_le hx0 hp)
  rw [show (∏ p ∈ m.primeFactors,
        ((p : ℝ) ^ roundedCorrection m x p * p *
          (p : ℝ) ^ (x * m.factorization p))) =
      (∏ p ∈ m.primeFactors, (p : ℝ) ^ roundedCorrection m x p) *
        (∏ p ∈ m.primeFactors, (p : ℝ)) *
          (∏ p ∈ m.primeFactors, (p : ℝ) ^ (x * m.factorization p)) by
            simp only [Finset.prod_mul_distrib]] at hfactor
  unfold supportProd
  push_cast
  rw [← natCast_rpow_eq_prod_primeFactors hm x] at hfactor
  calc
    (roundedDivisor m x : ℝ) ≤
        (∏ p ∈ m.primeFactors, (p : ℝ) ^ roundedCorrection m x p) *
          (∏ p ∈ m.primeFactors, (p : ℝ)) * (m : ℝ) ^ x := hfactor
    _ ≤ 2 * (∏ p ∈ m.primeFactors, (p : ℝ)) * (m : ℝ) ^ x := by
      gcongr
      exact correction_prod_le_two hm x

lemma supportProd_le_primeProd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {m : ℕ} (hsupp : m.primeFactors ⊆ P) :
    supportProd m ≤ Literature.VandeheyDiff.primeProd P := by
  unfold supportProd Literature.VandeheyDiff.primeProd
  exact Finset.prod_le_prod_of_subset_of_one_le hsupp
    (fun _ _ => Nat.zero_le _) fun p hp _ => (hP p hp).one_le

lemma roundedDivisor_upper_primeProd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {m : ℕ} (hm : m ≠ 0) (hsupp : m.primeFactors ⊆ P)
    {x : ℝ} (hx0 : 0 ≤ x) :
    (roundedDivisor m x : ℝ) ≤
      2 * Literature.VandeheyDiff.primeProd P * (m : ℝ) ^ x := by
  refine (roundedDivisor_upper hm hx0).trans ?_
  have hsupport : (supportProd m : ℝ) ≤
      Literature.VandeheyDiff.primeProd P := by
    exact_mod_cast supportProd_le_primeProd P hP hsupp
  have hrpow : 0 ≤ (m : ℝ) ^ x := Real.rpow_nonneg (by positivity) _
  gcongr

/-- The ambient prime product cannot be substituted for the support product in equation
(12): it need not divide an `ℕ_P` modulus when `P` contains an unused prime. -/
theorem ambient_primeProd_need_not_dvd :
    ¬ Literature.VandeheyDiff.primeProd ({2, 3} : Finset ℕ) ∣ 2 := by
  norm_num [Literature.VandeheyDiff.primeProd]

/-- Equations (12)--(13), with the displayed product taken over the actual support of
`m` and then bounded by the ambient prime product. -/
theorem roundedDivisor_spec (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {m : ℕ} (hm : m ≠ 0) (hsupp : m.primeFactors ⊆ P)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    roundedDivisor m x ∣ m ∧
      (roundedDivisor m x).primeFactors = m.primeFactors ∧
      (4 ∣ m → 4 ∣ roundedDivisor m x) ∧
      (m : ℝ) ^ x ≤ roundedDivisor m x ∧
      (roundedDivisor m x : ℝ) ≤
        2 * Literature.VandeheyDiff.primeProd P * (m : ℝ) ^ x := by
  exact ⟨roundedDivisor_dvd hm hx0 hx1,
    roundedDivisor_primeFactors hm hx0 hx1,
    four_dvd_roundedDivisor hm x,
    roundedDivisor_lower hm x,
    roundedDivisor_upper_primeProd P hP hm hsupp hx0⟩

end NormalNumbers.VandeheyKorobov
