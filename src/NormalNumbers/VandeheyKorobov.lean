/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandeheyDifferencing
import ErdosProblems.Erdos67b.PrimeGraphFourier

/-!
# Finite Fourier input for Vandehey's Korobov estimate

This file develops the Parseval--orbit mechanism used in rung 2 of the proof of Vandehey's
Theorem 5.1.  A twisted subgroup sum has constant norm on the multiplicative orbit of a unit.
The orbit has as many elements as the subgroup, while Parseval says that the total Fourier
mass is the modulus times the subgroup size.  The lemma below isolates the resulting square-root
bound from the later arithmetic verification of the orbit identity.
-/

open scoped BigOperators
open Finset
open Erdos67b

namespace NormalNumbers.VandeheyKorobov

noncomputable section

open Literature.VandeheyDiff
open Erdos438.Fourier
open NormalNumbers.G4

/-! ## Rung 1: the order lower bound -/

/-- The odd-prime valuation comparison behind Vandehey's Lemma 2.1.

If an odd prime `p` divides `b^q - 1`, LTE applied to `(b^q)^n - 1` shows that
the `p`-adic valuation gained by passing to any exponent `n` is at most `v_p(n)`.
The formulation as an inequality (rather than an equality involving the local order) is
exactly what is needed to compare the prime-power part of `m` with `M(P) * ord(b,m)`. -/
lemma padicValNat_pow_sub_one_le_add_of_odd_prime
    {p b q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 < b)
    (hq : q ≠ 0) (hn : n ≠ 0) (hpq : p ∣ b ^ q - 1) (hpb : ¬ p ∣ b) :
    padicValNat p (b ^ n - 1) ≤
      padicValNat p (b ^ q - 1) + padicValNat p n := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hbq : 1 < b ^ q := Nat.one_lt_pow hq hb
  have hpbq : ¬ p ∣ b ^ q := fun h ↦ hpb (hp.dvd_of_dvd_pow h)
  have hlte := padicValNat.pow_sub_pow (p := p) hodd (y := 1) hbq hpq hpbq hn
  rw [one_pow] at hlte
  have hpow_ne : b ^ (q * n) - 1 ≠ 0 := by
    have : 1 < b ^ (q * n) := Nat.one_lt_pow (Nat.mul_ne_zero hq hn) hb
    omega
  have hdiv : b ^ n - 1 ∣ b ^ (q * n) - 1 := by
    exact Nat.pow_sub_one_dvd_pow_sub_one b (dvd_mul_left n q)
  have hval : padicValNat p (b ^ n - 1) ≤ padicValNat p (b ^ (q * n) - 1) := by
    exact (padicValNat_dvd_iff_le hpow_ne).mp (pow_padicValNat_dvd.trans hdiv)
  rw [← pow_mul] at hlte
  exact hval.trans_eq hlte

/-- Odd-prime local factor of equation (5): every `p^t` dividing `b^n - 1` is absorbed by
the fixed `p`-part of `M(P)` and by the exponent `n`. -/
lemma prime_pow_le_fixedPart_mul_exponent_of_odd
    {p b q n t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 < b)
    (hq : q ≠ 0) (hn : n ≠ 0) (hpq : p ∣ b ^ q - 1) (hpb : ¬ p ∣ b)
    (hpt : p ^ t ∣ b ^ n - 1) :
    p ^ t ≤ p ^ padicValNat p (b ^ q - 1) * n := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hbn : b ^ n - 1 ≠ 0 := by
    have : 1 < b ^ n := Nat.one_lt_pow hn hb
    omega
  have ht : t ≤ padicValNat p (b ^ n - 1) :=
    (padicValNat_dvd_iff_le hbn).mp hpt
  have hval := padicValNat_pow_sub_one_le_add_of_odd_prime hp hp2 hb hq hn hpq hpb
  calc
    p ^ t ≤ p ^ (padicValNat p (b ^ q - 1) + padicValNat p n) :=
      Nat.pow_le_pow_right hp.pos (ht.trans hval)
    _ = p ^ padicValNat p (b ^ q - 1) * p ^ padicValNat p n := by rw [pow_add]
    _ ≤ p ^ padicValNat p (b ^ q - 1) * n :=
      Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd)

/-- Divisibility form of the odd-prime local bound: the part of `p^t` above the fixed
`p`-part of `b^q - 1` divides the exponent `n`.  This is the form that aggregates over
the distinct prime factors of a modulus without multiplying one copy of `n` per prime. -/
lemma prime_pow_excess_dvd_exponent_of_odd
    {p b q n t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 < b)
    (hq : q ≠ 0) (hn : n ≠ 0) (hpq : p ∣ b ^ q - 1) (hpb : ¬ p ∣ b)
    (hpt : p ^ t ∣ b ^ n - 1) :
    p ^ (t - padicValNat p (b ^ q - 1)) ∣ n := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hbn : b ^ n - 1 ≠ 0 := by
    have : 1 < b ^ n := Nat.one_lt_pow hn hb
    omega
  have ht : t ≤ padicValNat p (b ^ n - 1) :=
    (padicValNat_dvd_iff_le hbn).mp hpt
  have hval := padicValNat_pow_sub_one_le_add_of_odd_prime hp hp2 hb hq hn hpq hpb
  apply (padicValNat_dvd_iff_le hn).mpr
  omega

/-- The exceptional `2`-adic valuation comparison in Vandehey's Lemma 2.1.  Taking the
fixed exponent `q` even is precisely what absorbs the extra `v₂(b+1)` term in 2-adic LTE. -/
lemma padicValNat_two_pow_sub_one_le_add
    {b q n : ℕ} (hb : 1 < b) (hq : q ≠ 0) (hqeven : Even q)
    (hn : n ≠ 0) (hbod : ¬ 2 ∣ b) :
    padicValNat 2 (b ^ n - 1) ≤
      padicValNat 2 (b ^ q - 1) + padicValNat 2 n := by
  have hfixed := padicValNat.pow_two_sub_one hb hbod hq hqeven
  have htwon : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn
  have hdouble := padicValNat.pow_two_sub_one hb hbod htwon (even_two_mul n)
  have hdouble_ne : b ^ (2 * n) - 1 ≠ 0 := by
    have : 1 < b ^ (2 * n) := Nat.one_lt_pow htwon hb
    omega
  have hdiv : b ^ n - 1 ∣ b ^ (2 * n) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one b (dvd_mul_left n 2)
  have hval : padicValNat 2 (b ^ n - 1) ≤ padicValNat 2 (b ^ (2 * n) - 1) := by
    exact (padicValNat_dvd_iff_le hdouble_ne).mp (pow_padicValNat_dvd.trans hdiv)
  have hvq : 1 ≤ padicValNat 2 q := one_le_padicValNat_of_dvd hq hqeven.two_dvd
  have hv2n : padicValNat 2 (2 * n) = 1 + padicValNat 2 n := by
    rw [padicValNat.mul (by norm_num) hn, padicValNat_self]
  omega

/-- The `p = 2` local factor of equation (5). -/
lemma two_pow_le_fixedPart_mul_exponent
    {b q n t : ℕ} (hb : 1 < b) (hq : q ≠ 0) (hqeven : Even q)
    (hn : n ≠ 0) (hbod : ¬ 2 ∣ b) (hpt : 2 ^ t ∣ b ^ n - 1) :
    2 ^ t ≤ 2 ^ padicValNat 2 (b ^ q - 1) * n := by
  have hbn : b ^ n - 1 ≠ 0 := by
    have : 1 < b ^ n := Nat.one_lt_pow hn hb
    omega
  have ht : t ≤ padicValNat 2 (b ^ n - 1) :=
    (padicValNat_dvd_iff_le hbn).mp hpt
  have hval := padicValNat_two_pow_sub_one_le_add hb hq hqeven hn hbod
  calc
    2 ^ t ≤ 2 ^ (padicValNat 2 (b ^ q - 1) + padicValNat 2 n) :=
      Nat.pow_le_pow_right (by norm_num) (ht.trans hval)
    _ = 2 ^ padicValNat 2 (b ^ q - 1) * 2 ^ padicValNat 2 n := by rw [pow_add]
    _ ≤ 2 ^ padicValNat 2 (b ^ q - 1) * n :=
      Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd)

/-- Divisibility form of the exceptional `2`-adic local bound. -/
lemma two_pow_excess_dvd_exponent
    {b q n t : ℕ} (hb : 1 < b) (hq : q ≠ 0) (hqeven : Even q)
    (hn : n ≠ 0) (hbod : ¬ 2 ∣ b) (hpt : 2 ^ t ∣ b ^ n - 1) :
    2 ^ (t - padicValNat 2 (b ^ q - 1)) ∣ n := by
  have hbn : b ^ n - 1 ≠ 0 := by
    have : 1 < b ^ n := Nat.one_lt_pow hn hb
    omega
  have ht : t ≤ padicValNat 2 (b ^ n - 1) :=
    (padicValNat_dvd_iff_le hbn).mp hpt
  have hval := padicValNat_two_pow_sub_one_le_add hb hq hqeven hn hbod
  apply (padicValNat_dvd_iff_le hn).mpr
  omega

private lemma prod_dvd_of_pairwise_coprime_nat {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (hcop : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (hdvd : ∀ i ∈ s, f i ∣ z) :
    (∏ i ∈ s, f i) ∣ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      rw [Finset.prod_insert has]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (fun hai => has (hai ▸ hi))
      · exact hdvd a (Finset.mem_insert_self a s)
      · exact ih (hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)))
          (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))

/-- **Vandehey, Lemma 2.1, multiplicative form (equation (5)).**  If every prime factor of `m`
belongs to `P`, then `m ≤ M(P) * ord(b,m)`.

For `q = 2 * ord(b, ∏ P)` and `n = ord(b, m)`, the local LTE bounds show that
`p^(v_p(m) - v_p(b^q - 1))` divides `n` for every `p ∣ m`.  These excess prime powers
are pairwise coprime, so their product divides `n`; the complementary fixed powers form
a subproduct of `M(P)`. -/
theorem le_bigM_mul_orderOf
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (hbm : Nat.Coprime b m) :
    m ≤ bigM b P * orderOf (b : ZMod m) := by
  classical
  let Q := primeProd P
  let L := orderOf (b : ZMod Q)
  let q := 2 * L
  let n := orderOf (b : ZMod m)
  have hbQ : Nat.Coprime b Q := by
    dsimp [Q, primeProd]
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    exact (hP p hp).2.symm
  have hLpos : 0 < L := by
    dsimp [L]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b Q).mpr hbQ).isOfFinOrder
  have hq0 : q ≠ 0 := by
    dsimp [q]
    omega
  have hqeven : Even q := even_two_mul L
  have hnpos : 0 < n := by
    dsimp [n]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b m).mpr hbm).isOfFinOrder
  have hn0 : n ≠ 0 := hnpos.ne'
  have hpowQ : (b : ZMod Q) ^ L = 1 := by
    dsimp [L]
    exact pow_orderOf_eq_one _
  have hpowm : (b : ZMod m) ^ n = 1 := by
    dsimp [n]
    exact pow_orderOf_eq_one _
  have hbn : m ∣ b ^ n - 1 := by
    have hbn_gt : 1 < b ^ n := Nat.one_lt_pow hn0 (by omega)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hbn_gt.le]
    push_cast
    rw [hpowm]
    simp
  have hprimeFactors : m.primeFactors ⊆ P := by
    intro p hp
    exact hsupp p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  let fixed := b ^ q - 1
  let excess (p : ℕ) := p ^ (m.factorization p - padicValNat p fixed)
  have hexcess_dvd : ∀ p ∈ m.primeFactors, excess p ∣ n := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpP : p ∈ P := hprimeFactors hp
    have hpQ : p ∣ Q := by
      dsimp [Q, primeProd]
      exact Finset.dvd_prod_of_mem _ hpP
    have hpowpL : (b : ZMod p) ^ L = 1 := by
      have h := congrArg (ZMod.castHom hpQ (ZMod p)) hpowQ
      rwa [map_pow, map_one, map_natCast] at h
    have hpowpq : (b : ZMod p) ^ q = 1 := by
      dsimp [q]
      rw [mul_comm, pow_mul, hpowpL, one_pow]
    have hbq_gt : 1 < b ^ q := Nat.one_lt_pow hq0 (by omega)
    have hpq : p ∣ fixed := by
      dsimp [fixed]
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hbq_gt.le]
      push_cast
      rw [hpowpq]
      simp
    have hptm : p ^ m.factorization p ∣ m :=
      (hpprime.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
    have hpt : p ^ m.factorization p ∣ b ^ n - 1 := hptm.trans hbn
    have hpb : ¬ p ∣ b := hpprime.coprime_iff_not_dvd.mp (hP p hpP).2
    dsimp [excess, fixed]
    by_cases hp2 : p = 2
    · subst p
      exact two_pow_excess_dvd_exponent (by omega) hq0 hqeven hn0 hpb hpt
    · exact prime_pow_excess_dvd_exponent_of_odd hpprime hp2 (by omega)
        hq0 hn0 hpq hpb hpt
  have hexcess_pairwise :
      (m.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime excess) := by
    intro p hp r hr hpr
    dsimp [excess]
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hr)).mpr hpr).pow _ _
  have hprodExcess_dvd : (∏ p ∈ m.primeFactors, excess p) ∣ n :=
    prod_dvd_of_pairwise_coprime_nat m.primeFactors excess n hexcess_pairwise hexcess_dvd
  have hprodExcess_le : (∏ p ∈ m.primeFactors, excess p) ≤ n :=
    Nat.le_of_dvd hnpos hprodExcess_dvd
  have hfixed_le :
      (∏ p ∈ m.primeFactors, p ^ padicValNat p fixed) ≤ bigM b P := by
    dsimp [fixed, q, L]
    unfold bigM
    exact Finset.prod_le_prod_of_subset_of_one_le hprimeFactors
      (fun _ _ => by positivity)
      (fun p hp _ => Nat.one_le_pow _ _ (hP p hp).1.pos)
  have hm_le : m ≤ bigM b P * n := by
    calc
      m = ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
        Nat.prod_primeFactors_pow_factorization (by omega)
      _ ≤ ∏ p ∈ m.primeFactors,
          p ^ (padicValNat p fixed + (m.factorization p - padicValNat p fixed)) := by
        apply Finset.prod_le_prod'
        intro p hp
        apply Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors hp)
        omega
      _ = (∏ p ∈ m.primeFactors, p ^ padicValNat p fixed) *
          (∏ p ∈ m.primeFactors, excess p) := by
        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
      _ ≤ bigM b P * (∏ p ∈ m.primeFactors, excess p) :=
        Nat.mul_le_mul_right _ hfixed_le
      _ ≤ bigM b P * n := Nat.mul_le_mul_left _ hprodExcess_le
  exact hm_le

/-- **Vandehey, Lemma 2.1, quotient form (equation (5)).**  This is the convenient
natural-number rendering of `m / M(P) ≤ ord(b,m)`. -/
theorem div_bigM_le_orderOf
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (hbm : Nat.Coprime b m) :
    m / bigM b P ≤ orderOf (b : ZMod m) := by
  apply Nat.div_le_of_le_mul
  simpa [mul_comm] using le_bigM_mul_orderOf b hb P hP m hm hsupp hbm

/-! ## Rung 2: the Parseval--orbit mechanism -/

/-- **The sparse Parseval--orbit square-root bound.**  Let a length-`K` vector have total
squared mass `H`, and suppose `H` distinct frequencies have the same Fourier norm as frequency
`a`.  Then that norm is at most `sqrt T`.

This is the form needed for a multiplicative subgroup of `ZMod T`: take `K = T` and extend
the subgroup character by zero away from the subgroup.  Its squared mass is the subgroup
cardinality `H`, even though its support is not the initial interval `0, ..., H - 1`. -/
theorem norm_blockFourier_le_sqrt_of_orbit_l2 {K H T : ℕ} [NeZero H] [NeZero T]
    (b : Fin K → ℂ) (hbmass : (∑ j : Fin K, ‖b j‖ ^ 2 : ℝ) = H) (hKT : K ≤ T)
    (a : ℤ) (orbit : Fin H → ℕ) (horbit_lt : ∀ j, orbit j < T)
    (horbit_inj : Function.Injective orbit)
    (horbit_norm : ∀ j, ‖blockFourier T b (orbit j : ℤ)‖ = ‖blockFourier T b a‖) :
    ‖blockFourier T b a‖ ≤ Real.sqrt T := by
  classical
  let O : Finset ℕ := Finset.univ.image orbit
  have hOsub : O ⊆ Finset.range T := by
    intro t ht
    rcases Finset.mem_image.1 ht with ⟨j, -, rfl⟩
    exact Finset.mem_range.2 (horbit_lt j)
  have hOrbitSum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) = H * ‖blockFourier T b a‖ ^ 2 := by
    rw [show O = Finset.univ.image orbit from rfl,
      Finset.sum_image (fun x _ y _ hxy ↦ horbit_inj hxy)]
    simp_rw [horbit_norm]
    simp
  have hParseval :
      (∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 : ℝ) = T * H := by
    rw [sum_blockFourier_norm_sq b hKT, hbmass]
  have hsubsum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) ≤
        ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hOsub (fun _ _ _ ↦ sq_nonneg _)
  rw [hOrbitSum, hParseval] at hsubsum
  have hH : (0 : ℝ) < H := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  have hsq : ‖blockFourier T b a‖ ^ 2 ≤ T := by
    nlinarith
  have hsqrt : (Real.sqrt T) ^ 2 = T := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [norm_nonneg (blockFourier T b a), Real.sqrt_nonneg T]

/-- The explicit finite Fourier phase is the standard additive character after reduction
modulo its period. -/
lemma phase_eq_stdAddChar_zmod (T : ℕ) [NeZero T] (t x : ℤ) :
    phase T t x = ZMod.stdAddChar ((t * x : ℤ) : ZMod T) := by
  rw [ZMod.stdAddChar_coe]
  unfold phase
  congr 1
  push_cast
  ring

/-- The integer finite-Fourier phase is the repository's real exponential phase at the
corresponding rational argument. -/
lemma phase_eq_ePhase (T : ℕ) (t x : ℤ) :
    phase T t x = ePhase ((t : ℝ) * (x : ℝ) / T) := by
  unfold phase ePhase
  congr 1
  push_cast
  ring

/-- Multiplying two canonical residues inside the explicit Fourier phase agrees with
multiplication in `ZMod`. -/
lemma phase_val_mul {T : ℕ} [NeZero T] (t x : ZMod T) :
    phase T (t.val : ℤ) (x.val : ℤ) = ZMod.stdAddChar (t * x) := by
  rw [phase_eq_stdAddChar_zmod]
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- **Vandehey's twisted subgroup bound (the Parseval--orbit trick).**

Let `τ` be the multiplicative order of `b` modulo `m`.  For every additive character
`ψ` of the cyclic exponent group `ZMod τ` and every unit frequency `a`, the character-twisted
sum over the subgroup generated by `b` has norm at most `√m`.

The proof extends `ψ` by zero from the actual subgroup residues to all residues modulo `m`.
Its squared mass is exactly `τ`.  Multiplication of the frequency by `b^h` cyclically reindexes
the subgroup sum and changes it only by the unit scalar `ψ(-h)`.  The `τ` resulting frequencies
are distinct, so `norm_blockFourier_le_sqrt_of_orbit_l2` applies. -/
theorem norm_twisted_powers_sum_le_sqrt
    {b m : ℕ} [NeZero m] [NeZero (orderOf (b : ZMod m))]
    (hbm : Nat.Coprime b m) (a : ZMod m) (ha : IsUnit a)
    (ψ : AddChar (ZMod (orderOf (b : ZMod m))) ℂ) :
    ‖∑ j : ZMod (orderOf (b : ZMod m)),
        ψ j * phase m (a.val : ℤ) (((b : ZMod m) ^ j.val).val : ℤ)‖ ≤ Real.sqrt m := by
  let g : ZMod m := b
  let τ := orderOf g
  let pos : ZMod τ → Fin m := fun j ↦ ⟨(g ^ j.val).val, ZMod.val_lt _⟩
  have hgunit : IsUnit g := by
    exact (ZMod.isUnit_iff_coprime b m).mpr hbm
  have hpos_inj : Function.Injective pos := by
    intro j k hjk
    have hpows : g ^ j.val = g ^ k.val := by
      apply ZMod.val_injective m
      exact congrArg Fin.val hjk
    have hmods := hgunit.isOfFinOrder.pow_inj_mod.mp hpows
    have hvals : j.val = k.val := by
      simpa only [τ, Nat.mod_eq_of_lt j.val_lt, Nat.mod_eq_of_lt k.val_lt] using hmods
    exact ZMod.val_injective τ hvals
  let v : Fin m → ℂ := Function.extend pos ψ (fun _ ↦ 0)
  let S : Finset (Fin m) := Finset.univ.image pos
  have hv_zero (x : Fin m) (hx : x ∉ S) : v x = 0 := by
    have hnot : ¬ ∃ j, pos j = x := by
      simpa only [S, Finset.mem_image, Finset.mem_univ, true_and] using hx
    exact Function.extend_apply' ψ (fun _ ↦ 0) x hnot
  have hmass : (∑ x : Fin m, ‖v x‖ ^ 2 : ℝ) = τ := by
    calc
      ((∑ x : Fin m, ‖v x‖ ^ 2) : ℝ) = (∑ x ∈ S, ‖v x‖ ^ 2) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro x _ hx
        rw [hv_zero x hx]
        simp
      _ = ∑ j : ZMod τ, ‖v (pos j)‖ ^ 2 := by
        simp only [S]
        rw [Finset.sum_image hpos_inj.injOn]
      _ = ∑ j : ZMod τ, ‖ψ j‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show v (pos j) = ψ j from hpos_inj.extend_apply ψ (fun _ ↦ 0) j]
      _ = τ := by
        simp [AddChar.norm_apply, ZMod.card]
  have hfourier (t : ZMod m) :
      blockFourier m v (t.val : ℤ) =
        ∑ j : ZMod τ, ψ j * phase m (t.val : ℤ) ((g ^ j.val).val : ℤ) := by
    unfold blockFourier
    calc
      (∑ x : Fin m, v x * phase m (t.val : ℤ) (x.val : ℤ)) =
          ∑ x ∈ S, v x * phase m (t.val : ℤ) (x.val : ℤ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro x _ hx
        rw [hv_zero x hx, zero_mul]
      _ = ∑ j : ZMod τ, v (pos j) * phase m (t.val : ℤ) ((pos j).val : ℤ) := by
        simp only [S]
        rw [Finset.sum_image hpos_inj.injOn]
      _ = ∑ j : ZMod τ, ψ j * phase m (t.val : ℤ) ((g ^ j.val).val : ℤ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show v (pos j) = ψ j from hpos_inj.extend_apply ψ (fun _ ↦ 0) j]
  let orbit : Fin τ → ℕ := fun h ↦ (a * g ^ h.val).val
  have horbit_lt (h : Fin τ) : orbit h < m := ZMod.val_lt _
  have horbit_inj : Function.Injective orbit := by
    intro h k hhk
    apply Fin.ext
    apply pow_injOn_Iio_orderOf h.isLt k.isLt
    apply ha.mul_left_cancel
    apply ZMod.val_injective m
    exact hhk
  have hpow_shift (k : ZMod τ) (h : Fin τ) :
      g ^ h.val * g ^ (k - (h.val : ZMod τ)).val = g ^ k.val := by
    have hmod : (h.val + (k - (h.val : ZMod τ)).val) % τ = k.val := by
      have hz :
          (((h.val + (k - (h.val : ZMod τ)).val : ℕ) : ZMod τ)).val = k.val := by
        apply congrArg ZMod.val
        push_cast
        rw [ZMod.natCast_zmod_val]
        abel
      simpa only [ZMod.val_natCast] using hz
    calc
      g ^ h.val * g ^ (k - (h.val : ZMod τ)).val =
          g ^ (h.val + (k - (h.val : ZMod τ)).val) := (pow_add _ _ _).symm
      _ = g ^ ((h.val + (k - (h.val : ZMod τ)).val) % τ) :=
        (pow_mod_orderOf g _).symm
      _ = g ^ k.val := by rw [hmod]
  have hphase_shift (k : ZMod τ) (h : Fin τ) :
      phase m ((a * g ^ h.val).val : ℤ)
          ((g ^ (k - (h.val : ZMod τ)).val).val : ℤ) =
        phase m (a.val : ℤ) ((g ^ k.val).val : ℤ) := by
    rw [phase_val_mul, phase_val_mul]
    congr 1
    rw [mul_assoc, hpow_shift]
  have hsum_shift (h : Fin τ) :
      (∑ j : ZMod τ, ψ j *
          phase m ((a * g ^ h.val).val : ℤ) ((g ^ j.val).val : ℤ)) =
        ψ (-(h.val : ZMod τ)) *
          ∑ k : ZMod τ, ψ k * phase m (a.val : ℤ) ((g ^ k.val).val : ℤ) := by
    let F : ZMod τ → ℂ := fun j ↦
      ψ j * phase m ((a * g ^ h.val).val : ℤ) ((g ^ j.val).val : ℤ)
    calc
      (∑ j : ZMod τ, ψ j *
          phase m ((a * g ^ h.val).val : ℤ) ((g ^ j.val).val : ℤ)) =
          ∑ k : ZMod τ, ψ (k - (h.val : ZMod τ)) *
            phase m ((a * g ^ h.val).val : ℤ)
              ((g ^ (k - (h.val : ZMod τ)).val).val : ℤ) := by
        simpa only [F, Equiv.subRight_apply] using
          ((Equiv.subRight (h.val : ZMod τ)).sum_comp F).symm
      _ = ∑ k : ZMod τ, ψ (-(h.val : ZMod τ)) *
            (ψ k * phase m (a.val : ℤ) ((g ^ k.val).val : ℤ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hphase_shift, ψ.map_sub_eq_div, ψ.map_neg_eq_inv]
        ring
      _ = ψ (-(h.val : ZMod τ)) *
          ∑ k : ZMod τ, ψ k * phase m (a.val : ℤ) ((g ^ k.val).val : ℤ) := by
        rw [Finset.mul_sum]
  have horbit_norm (h : Fin τ) :
      ‖blockFourier m v (orbit h : ℤ)‖ = ‖blockFourier m v (a.val : ℤ)‖ := by
    change ‖blockFourier m v ((a * g ^ h.val).val : ℤ)‖ =
      ‖blockFourier m v (a.val : ℤ)‖
    rw [hfourier, hfourier, hsum_shift, norm_mul, ψ.norm_apply, one_mul]
  rw [← hfourier a]
  exact norm_blockFourier_le_sqrt_of_orbit_l2
    (K := m) (H := τ) (T := m) v hmass le_rfl (a.val : ℤ) orbit
      horbit_lt horbit_inj horbit_norm

/-- Every completed additive twist of the power orbit is bounded by `√m`.  This is the
specialization of `norm_twisted_powers_sum_le_sqrt` used in the completion proof of
Vandehey's Lemma 2.2. -/
theorem norm_completed_power_sum_le_sqrt
    {b m : ℕ} [NeZero m] [NeZero (orderOf (b : ZMod m))]
    (hbm : Nat.Coprime b m) (a : ZMod m) (ha : IsUnit a)
    (h : ZMod (orderOf (b : ZMod m))) :
    ‖∑ j : ZMod (orderOf (b : ZMod m)),
        phase (orderOf (b : ZMod m)) (h.val : ℤ) (j.val : ℤ) *
          phase m (a.val : ℤ) (((b : ZMod m) ^ j.val).val : ℤ)‖ ≤ Real.sqrt m := by
  simpa only [phase_val_mul, AddChar.mulShift_apply] using
    norm_twisted_powers_sum_le_sqrt hbm a ha (ZMod.stdAddChar.mulShift h)

/-- **Dense Parseval--orbit square-root bound.**  Let `b` be a length-`H` sequence of unit-modulus
coefficients and take its unnormalised Fourier transform modulo `T`.  If `H` distinct frequencies
all have the same Fourier norm as the frequency `a`, then that norm is at most `sqrt T`.

For Vandehey's twisted subgroup sum the subgroup residues need not form the initial interval, so
the direct instantiation uses the sparse `norm_blockFourier_le_sqrt_of_orbit_l2` above. -/
theorem norm_blockFourier_le_sqrt_of_orbit {H T : ℕ} [NeZero H] [NeZero T]
    (b : Fin H → ℂ) (hb : ∀ j, ‖b j‖ = 1) (a : ℤ)
    (orbit : Fin H → ℕ) (horbit_lt : ∀ j, orbit j < T)
    (horbit_inj : Function.Injective orbit)
    (horbit_norm : ∀ j, ‖blockFourier T b (orbit j : ℤ)‖ = ‖blockFourier T b a‖) :
    ‖blockFourier T b a‖ ≤ Real.sqrt T := by
  classical
  let O : Finset ℕ := Finset.univ.image orbit
  have hOsub : O ⊆ Finset.range T := by
    intro t ht
    rcases Finset.mem_image.1 ht with ⟨j, -, rfl⟩
    exact Finset.mem_range.2 (horbit_lt j)
  have hOcard : O.card = H := by
    simp only [O, Finset.card_image_of_injective _ horbit_inj, Finset.card_univ, Fintype.card_fin]
  have hOrbitSum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) = H * ‖blockFourier T b a‖ ^ 2 := by
    rw [show O = Finset.univ.image orbit from rfl,
      Finset.sum_image (fun x _ y _ hxy ↦ horbit_inj hxy)]
    simp_rw [horbit_norm]
    simp
  have hParseval :
      (∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 : ℝ) = T * H := by
    have hHT : H ≤ T := by
      calc
        H = O.card := hOcard.symm
        _ ≤ (Finset.range T).card := Finset.card_le_card hOsub
        _ = T := Finset.card_range T
    rw [sum_blockFourier_norm_sq b hHT]
    simp_rw [hb]
    simp
  have hsubsum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) ≤
        ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hOsub (fun _ _ _ ↦ sq_nonneg _)
  rw [hOrbitSum, hParseval] at hsubsum
  have hH : (0 : ℝ) < H := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  have hsq : ‖blockFourier T b a‖ ^ 2 ≤ T := by
    nlinarith
  have hsqrt : (Real.sqrt T) ^ 2 = T := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [norm_nonneg (blockFourier T b a), Real.sqrt_nonneg T]

end

end NormalNumbers.VandeheyKorobov
