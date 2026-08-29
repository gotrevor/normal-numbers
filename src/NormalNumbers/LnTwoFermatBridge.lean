/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoPrimeWindow

/-!
# The Fermat-quotient bridge (R3): Glaisher / Z.-H. Sun congruence

Lane-2 target 3 (2026-08-29 operator brief).  Turns the provenance note in
`LnTwoPrimeWindow.lean`'s node docstring into a theorem:

  `lnTwoNum (p−1) ≡ lcmRange (p−1) · q_p(2)  (mod p)`  for odd primes `p`,

where `q_p(2) = (2^{p−1} − 1)/p mod p` is the Fermat quotient.  The
statement SHAPE is settled — probe-verified exactly for all 2261 primes
`3 ≤ p < 20000` with zero failures (`experiments/lntwo_fermat_bridge.py`),
unit pinned as `L_{p−1} mod p`.  Formalize exactly this form.

Route (all sums `k = 0, …, p−2`, working in the field `ZMod p`):

1. `C(p−1, k) ≡ (−1)^k (mod p)` by induction from
   `C(n, k+1)·(k+1) = C(n, k)·(n−k)`.
2. `C(p, k+1)/p` is an integer (`p` prime) and
   `C(p, k+1)/p ≡ (−1)^k·(k+1)⁻¹ (mod p)` from
   `p·C(p−1, k) = C(p, k+1)·(k+1)`.
3. Binomial theorem at `x = −2`: `Σ_k C(p, k+1)·(−2)^{k+1} = 2^p − 2`
   (over `ℤ`; the `k = 0` and `k = p` terms of `(−2+1)^p` cancel `−1−(−2)^p`).
4. Divide the exact identity by `p` and cast to `ZMod p`, substituting
   step 2 and Fermat `p ∣ 2^{p−1} − 1`:
   `Σ_k (k+1)⁻¹·2^{k+1} ≡ −2·q_p(2)` — Z.-H. Sun's congruence in the
   equivalent form `Σ_{j=1}^{p−1} 2^j/j ≡ −2 q_p(2)`.
5. Reflect the surrogate sum (`Finset.sum_range_reflect`):
   `A_{p−1} = Σ_k (L/(k+1))·2^{p−2−k} ≡ L·Σ_k (p−1−k)⁻¹·2^k
   = −L·2⁻¹·Σ_k (k+1)⁻¹·2^{k+1} ≡ L·q_p(2)`.
-/

namespace NormalNumbers

open Finset

/-- The Fermat quotient `q_p(2) = ((2^{p−1} − 1)/p) mod p`.  For an odd
prime `p` the division is exact (Fermat's little theorem). -/
def fermatQuotient2 (p : ℕ) : ℕ := (2 ^ (p - 1) - 1) / p % p

section OddPrime

variable {p : ℕ} [hpf : Fact p.Prime]

private lemma cast_ne_zero_of_lt {k : ℕ} (h0 : 0 < k) (hk : k < p) :
    (k : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hdvd => absurd (Nat.le_of_dvd h0 hdvd) (not_le.mpr hk)

private lemma cast_p_sub_one : ((p - 1 : ℕ) : ZMod p) = -1 := by
  have hp1 : 1 ≤ p := hpf.out.one_lt.le
  rw [Nat.cast_sub hp1, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- Step 1: `C(p−1, k) ≡ (−1)^k (mod p)` for `k ≤ p−1`. -/
private lemma choose_p_sub_one_cast :
    ∀ k, k ≤ p - 1 → ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk1
    have hk : k ≤ p - 1 := (Nat.le_succ k).trans hk1
    have hkp : k + 1 < p := by
      have := hpf.out.one_lt
      omega
    have hrec := Nat.choose_succ_right_eq (p - 1) k
    have hcast : ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * (k + 1) =
        ((Nat.choose (p - 1) k : ℕ) : ZMod p) * ((p - 1 - k : ℕ) : ZMod p) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hrec
    rw [ih hk, Nat.cast_sub hk, cast_p_sub_one] at hcast
    have hne : ((k : ZMod p) + 1) ≠ 0 := by
      have := cast_ne_zero_of_lt (Nat.succ_pos k) hkp
      push_cast at this
      exact this
    have : ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k : ZMod p) + 1) =
        (-1) ^ (k + 1) * ((k : ZMod p) + 1) := by
      push_cast at hcast
      rw [hcast]; ring
    exact mul_right_cancel₀ hne this

/-- Step 2: the exact binomial quotient `C(p, k+1)/p` reduces to
`(−1)^k·(k+1)⁻¹` mod `p`, for `k < p−1`. -/
private lemma choose_div_p_cast {k : ℕ} (hk : k < p - 1) :
    ((Nat.choose p (k + 1) / p : ℕ) : ZMod p) = (-1) ^ k * ((k : ZMod p) + 1)⁻¹ := by
  have hp := hpf.out
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hkp : k + 1 < p := by omega
  have hdvd : p ∣ Nat.choose p (k + 1) :=
    hp.dvd_choose_self (Nat.succ_ne_zero k) hkp
  -- p · C(p−1, k) = C(p, k+1) · (k+1)
  have hkey := Nat.add_one_mul_choose_eq (p - 1) k
  rw [Nat.sub_add_cancel hp1] at hkey
  -- substitute C(p, k+1) = p · (C(p, k+1)/p) and cancel p
  obtain ⟨c, hc⟩ := hdvd
  have hcdiv : Nat.choose p (k + 1) / p = c := by
    rw [hc, Nat.mul_div_cancel_left _ hp.pos]
  rw [hc, mul_assoc] at hkey
  have hcancel : Nat.choose (p - 1) k = c * (k + 1) :=
    Nat.eq_of_mul_eq_mul_left hp.pos hkey
  have hcast : ((Nat.choose (p - 1) k : ℕ) : ZMod p) =
      (c : ZMod p) * ((k : ZMod p) + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hcancel
  rw [choose_p_sub_one_cast k (by omega)] at hcast
  have hne : ((k : ZMod p) + 1) ≠ 0 := by
    have := cast_ne_zero_of_lt (Nat.succ_pos k) hkp
    push_cast at this
    exact this
  rw [hcdiv, eq_mul_inv_iff_mul_eq₀ hne, ← hcast]

/-- Step 3: the binomial theorem for `(−2+1)^p` over `ℤ`, boundary terms
removed: `Σ_{k<p−1} C(p, k+1)·(−2)^{k+1} = 2^p − 2` (odd `p`). -/
private lemma sum_choose_neg_two (hodd : Odd p) :
    ∑ k ∈ range (p - 1), (Nat.choose p (k + 1) : ℤ) * (-2) ^ (k + 1) =
      2 ^ p - 2 := by
  have hp1 : 1 ≤ p := hpf.out.one_lt.le
  have hbin := add_pow (-2 : ℤ) 1 p
  rw [show (-2 : ℤ) + 1 = -1 by ring, hodd.neg_one_pow] at hbin
  simp only [one_pow, mul_one] at hbin
  rw [Finset.sum_range_succ] at hbin
  rw [show p = p - 1 + 1 by omega, Finset.sum_range_succ'] at hbin
  rw [show p - 1 + 1 = p by omega] at hbin
  simp only [Nat.choose_self, Nat.cast_one, mul_one, pow_zero,
    Nat.choose_zero_right] at hbin
  have hneg : (-2 : ℤ) ^ p = -(2 ^ p) := hodd.neg_pow 2
  have := hbin
  rw [hneg] at this
  have hcomm : ∀ k, (-2 : ℤ) ^ (k + 1) * (Nat.choose p (k + 1) : ℤ) =
      (Nat.choose p (k + 1) : ℤ) * (-2) ^ (k + 1) := fun k => mul_comm _ _
  calc ∑ k ∈ range (p - 1), (Nat.choose p (k + 1) : ℤ) * (-2) ^ (k + 1)
      = ∑ k ∈ range (p - 1), (-2 : ℤ) ^ (k + 1) * (Nat.choose p (k + 1) : ℤ) := by
        exact Finset.sum_congr rfl fun k _ => (hcomm k).symm
    _ = 2 ^ p - 2 := by linarith [this]

/-- Fermat's little theorem as exact divisibility: `p ∣ 2^{p−1} − 1`. -/
private lemma p_dvd_two_pow_sub_one (hodd : Odd p) : p ∣ 2 ^ (p - 1) - 1 := by
  have hp := hpf.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num [Nat.odd_iff] at hodd
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    exact_mod_cast this
  have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [← ZMod.natCast_eq_zero_iff]
  have h1le : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub h1le]
  push_cast
  rw [hfermat, sub_self]

/-- Step 4 (Z.-H. Sun's congruence, geometric form):
`Σ_{k<p−1} (k+1)⁻¹·2^{k+1} = −2·q_p(2)` in `ZMod p`. -/
private lemma sum_inv_two_pow (hodd : Odd p) :
    ∑ k ∈ range (p - 1), ((k : ZMod p) + 1)⁻¹ * 2 ^ (k + 1) =
      -2 * ((2 ^ (p - 1) - 1) / p : ℕ) := by
  have hp := hpf.out
  have hp1 : 1 ≤ p := hp.one_lt.le
  -- exact integer identity: Σ (C(p,k+1)/p)·(−2)^{k+1} = 2·q′ over ℤ
  have hq : ((2 ^ (p - 1) - 1) / p : ℕ) * p = 2 ^ (p - 1) - 1 :=
    Nat.div_mul_cancel (p_dvd_two_pow_sub_one hodd)
  have hqZ : (((2 ^ (p - 1) - 1) / p : ℕ) : ℤ) * p = 2 ^ (p - 1) - 1 := by
    have h1le : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
    have := congrArg (Nat.cast : ℕ → ℤ) hq
    rw [Nat.cast_mul, Nat.cast_sub h1le] at this
    push_cast at this
    exact this
  have hchoose : ∀ k ∈ range (p - 1),
      (Nat.choose p (k + 1) : ℤ) = p * (Nat.choose p (k + 1) / p : ℕ) := by
    intro k hk
    have hkp : k + 1 < p := by
      have := Finset.mem_range.mp hk; omega
    have hdvd : p ∣ Nat.choose p (k + 1) :=
      hp.dvd_choose_self (Nat.succ_ne_zero k) hkp
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hdvd).symm
  have hsum := sum_choose_neg_two (p := p) hodd
  rw [Finset.sum_congr rfl fun k hk => by rw [hchoose k hk]] at hsum
  simp only [mul_assoc] at hsum
  rw [← Finset.mul_sum] at hsum
  have hrhs : (2 : ℤ) ^ p - 2 = (p : ℤ) * (2 * ((2 ^ (p - 1) - 1) / p : ℕ)) := by
    have : (2 : ℤ) ^ p = 2 ^ (p - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    linarith [hqZ]
  rw [hrhs] at hsum
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hint : ∑ k ∈ range (p - 1), ((Nat.choose p (k + 1) / p : ℕ) : ℤ) * (-2) ^ (k + 1) =
      2 * ((2 ^ (p - 1) - 1) / p : ℕ) := mul_left_cancel₀ hpZ hsum
  -- cast the ℤ identity into ZMod p and substitute step 2
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hint
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat,
    Int.cast_natCast] at hcast
  rw [Finset.sum_congr rfl fun k hk =>
    show ((Nat.choose p (k + 1) / p : ℕ) : ZMod p) * (-2) ^ (k + 1) =
        -(((k : ZMod p) + 1)⁻¹ * 2 ^ (k + 1)) by
      rw [choose_div_p_cast (Finset.mem_range.mp hk)]
      have hneg : (-2 : ZMod p) ^ (k + 1) = (-1) ^ (k + 1) * 2 ^ (k + 1) := by
        rw [neg_pow]
      have hone : ((-1 : ZMod p)) ^ k * (-1) ^ k = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      rw [hneg]
      linear_combination (-(((k : ZMod p) + 1)⁻¹ * 2 ^ (k + 1))) * hone] at hcast
  rw [Finset.sum_neg_distrib] at hcast
  linear_combination -hcast

end OddPrime

/-- **The Fermat-quotient bridge (Glaisher / Z.-H. Sun)**: at a
prime-adjacent index the surrogate numerator carries the Fermat quotient,
`A_{p−1} ≡ L_{p−1} · q_p(2) (mod p)`.  Probe-verified for all primes
`3 ≤ p < 20000`; statement shape frozen — formalize exactly this form. -/
theorem lnTwoNum_modEq_fermatQuotient {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    lnTwoNum (p - 1) ≡ lcmRange (p - 1) * fermatQuotient2 p [MOD p] := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  rw [← ZMod.natCast_eq_natCast_iff]
  -- RHS: the mod-p reduction in the definition is invisible in ZMod p
  have hRHS : ((lcmRange (p - 1) * fermatQuotient2 p : ℕ) : ZMod p) =
      (lcmRange (p - 1) : ZMod p) * ((2 ^ (p - 1) - 1) / p : ℕ) := by
    rw [fermatQuotient2]
    push_cast [ZMod.natCast_mod]
    ring
  rw [hRHS, lnTwoNum]
  push_cast
  -- each division by k+1 is exact; convert to field inverses
  have hterm : ∀ k ∈ range (p - 1),
      ((lcmRange (p - 1) / (k + 1) : ℕ) : ZMod p) * 2 ^ (p - 1 - k - 1) =
        (lcmRange (p - 1) : ZMod p) * ((k : ZMod p) + 1)⁻¹ * 2 ^ (p - 1 - k - 1) := by
    intro k hk
    have hkp : k + 1 < p := by
      have := Finset.mem_range.mp hk; omega
    have hne : ((k : ZMod p) + 1) ≠ 0 := by
      have := cast_ne_zero_of_lt (Nat.succ_pos k) hkp
      push_cast at this
      exact this
    have hdvd := succ_dvd_lcmRange (Finset.mem_range.mp hk)
    have hdiv : ((lcmRange (p - 1) / (k + 1) : ℕ) : ZMod p) =
        (lcmRange (p - 1) : ZMod p) * ((k : ZMod p) + 1)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hne]
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) (Nat.div_mul_cancel hdvd)
    rw [hdiv]
  rw [Finset.sum_congr rfl hterm]
  -- reflect the sum: k ↦ p−2−k
  rw [← Finset.sum_range_reflect
    (fun k => (lcmRange (p - 1) : ZMod p) * ((k : ZMod p) + 1)⁻¹ * 2 ^ (p - 1 - k - 1))
    (p - 1)]
  -- rewrite the reflected terms
  have hrefl : ∀ j ∈ range (p - 1),
      (lcmRange (p - 1) : ZMod p) * (((p - 1 - 1 - j : ℕ) : ZMod p) + 1)⁻¹ *
          2 ^ (p - 1 - (p - 1 - 1 - j) - 1) =
        -((lcmRange (p - 1) : ZMod p) * ((j : ZMod p) + 1)⁻¹ * 2 ^ j) := by
    intro j hj
    have hjlt : j < p - 1 := Finset.mem_range.mp hj
    have hexp : p - 1 - (p - 1 - 1 - j) - 1 = j := by omega
    have hidx : ((p - 1 - 1 - j : ℕ) : ZMod p) + 1 = -((j : ZMod p) + 1) := by
      have hcast : ((p - 1 - 1 - j : ℕ) : ZMod p) =
          ((p - 1 : ℕ) : ZMod p) - ((1 + j : ℕ) : ZMod p) := by
        rw [← Nat.cast_sub (by omega)]
        congr 1
        omega
      rw [hcast, cast_p_sub_one]
      push_cast
      ring
    rw [hexp, hidx, inv_neg]
    ring
  rw [Finset.sum_congr rfl hrefl, Finset.sum_neg_distrib]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  -- Sun's congruence, shifted down by one factor of 2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by
      rintro rfl
      norm_num [Nat.odd_iff] at hodd
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    exact_mod_cast this
  have hsum2 : ∑ j ∈ range (p - 1), ((j : ZMod p) + 1)⁻¹ * 2 ^ j =
      -((2 ^ (p - 1) - 1) / p : ℕ) := by
    refine mul_left_cancel₀ h2ne ?_
    have hlhs : (2 : ZMod p) * ∑ j ∈ range (p - 1), ((j : ZMod p) + 1)⁻¹ * 2 ^ j =
        ∑ j ∈ range (p - 1), ((j : ZMod p) + 1)⁻¹ * 2 ^ (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    rw [hlhs, sum_inv_two_pow hodd]
    ring
  rw [hsum2]
  ring

end NormalNumbers
