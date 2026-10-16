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

/-- **Vandehey, Lemma 2.1, consumed form (equation (5)).**  If every prime factor of `m`
belongs to `P`, then the multiplicative order of `b` modulo `m` is at least `m / M(P)`.

The remaining proof debt is the simultaneous prime-power lifting argument, including the
exceptional 2-adic case.  The statement is frozen here before that arithmetic is developed. -/
theorem div_bigM_le_orderOf
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (hbm : Nat.Coprime b m) :
    m / bigM b P ≤ orderOf (b : ZMod m) := by
  sorry

/-! ## Rung 2: the Parseval--orbit mechanism -/

/-- **The Parseval--orbit square-root bound.**  Let `b` be a length-`H` sequence of unit-modulus
coefficients and take its unnormalised Fourier transform modulo `T`.  If `H` distinct frequencies
all have the same Fourier norm as the frequency `a`, then that norm is at most `sqrt T`.

For the twisted subgroup sum in Vandehey's Lemma 2.2, the coefficients are the values of the
subgroup character, and the `H` frequencies are the orbit `aH`. -/
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
