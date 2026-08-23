/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Arithmetic core for Stoneham's theorem: 2 is a primitive root mod `3 ^ m`

The number-theoretic engine behind the normality of the Stoneham constant
`α₂,₃`: the multiplicative order of `2` modulo `3 ^ m` is exactly
`2 * 3 ^ (m - 1) = φ (3 ^ m)`, so the doubling map cycles through *all*
units mod `3 ^ m` — the equidistribution ingredient of Bailey–Crandall.

## Main results

* `exists_two_pow_eq_one_add` — the explicit lifting-the-exponent shape:
  `2 ^ (2 * 3 ^ k) = 1 + t * 3 ^ (k + 1)` with `3 ∤ t`, i.e. the 3-adic
  valuation of `2 ^ (2 * 3 ^ k) - 1` is exactly `k + 1`.  Corollaries
  `two_pow_modEq_one` / `two_pow_not_modEq_one` state it in `Nat.ModEq` form.
* `orderOf_two_zmod_three_pow` — `orderOf (2 : ZMod (3 ^ m)) = 2 * 3 ^ (m - 1)`
  for `1 ≤ m`.  The proof factors `2 = (-1) * (-2)` and rides mathlib's
  `ZMod.orderOf_one_add_mul_prime` (LTE for units of `ZMod (p ^ n)`, odd `p`)
  applied to `-2 = 1 + 3 * (-1)`, gluing with `orderOf (-1) = 2` via
  coprimality of the orders.
* `mem_zpowers_unitOfCoprime_two` — `2` generates the full unit group
  `(ZMod (3 ^ m))ˣ` (cardinality: `φ (3 ^ m) = 2 * 3 ^ (m - 1)`).
* `exists_pow_mul_eq_unit` — uniformity form: every doubling orbit
  `k ↦ a * 2 ^ k` on the units visits every unit within one period.
-/

namespace NormalNumbers

/-! ### Lifting the exponent, explicitly, over `ℕ` -/

/-- Explicit 3-adic valuation of `2 ^ (2 * 3 ^ k) - 1`: it is *exactly*
`k + 1`, witnessed by `2 ^ (2 * 3 ^ k) = 1 + t * 3 ^ (k + 1)` with `3 ∤ t`.
Induction on `k`; the cube of `1 + t * 3 ^ (k + 1)` picks up exactly one more
factor of `3`. -/
theorem exists_two_pow_eq_one_add (k : ℕ) :
    ∃ t : ℕ, ¬ 3 ∣ t ∧ 2 ^ (2 * 3 ^ k) = 1 + t * 3 ^ (k + 1) := by
  induction k with
  | zero => exact ⟨1, by decide, by norm_num⟩
  | succ n ih =>
    obtain ⟨t, ht3, ht⟩ := ih
    refine ⟨t + t ^ 2 * 3 ^ (n + 1) + t ^ 3 * 3 ^ (2 * n + 1), ?_, ?_⟩
    · intro h
      apply ht3
      have h1 : (3 : ℕ) ∣ t ^ 2 * 3 ^ (n + 1) := ⟨t ^ 2 * 3 ^ n, by ring⟩
      have h2 : (3 : ℕ) ∣ t ^ 3 * 3 ^ (2 * n + 1) := ⟨t ^ 3 * 3 ^ (2 * n), by ring⟩
      omega
    · have e : 2 * 3 ^ (n + 1) = 2 * 3 ^ n * 3 := by ring
      rw [e, pow_mul, ht]
      ring

/-- `2 ^ (2 * 3 ^ k) ≡ 1 [MOD 3 ^ (k + 1)]` — the "order divides" half. -/
theorem two_pow_modEq_one (k : ℕ) : 2 ^ (2 * 3 ^ k) ≡ 1 [MOD 3 ^ (k + 1)] := by
  obtain ⟨t, -, ht⟩ := exists_two_pow_eq_one_add k
  rw [ht]
  show (1 + t * 3 ^ (k + 1)) % 3 ^ (k + 1) = 1 % 3 ^ (k + 1)
  rw [Nat.add_mul_mod_self_right]

/-- `2 ^ (2 * 3 ^ k) ≢ 1 [MOD 3 ^ (k + 2)]` — the valuation is *exactly*
`k + 1`, so the order does not collapse at the next level. -/
theorem two_pow_not_modEq_one (k : ℕ) :
    ¬ 2 ^ (2 * 3 ^ k) ≡ 1 [MOD 3 ^ (k + 2)] := by
  obtain ⟨t, ht3, ht⟩ := exists_two_pow_eq_one_add k
  rw [ht]
  intro h
  have hd : 3 ^ (k + 2) ∣ t * 3 ^ (k + 1) := by
    have h' := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).mp h.symm
    simpa using h'
  apply ht3
  have e : (3 : ℕ) ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
  rw [e] at hd
  exact (mul_dvd_mul_iff_right (pow_ne_zero (k + 1) (by norm_num))).mp hd

/-- Bridge between the `ZMod` and `Nat.ModEq` worlds for powers of `2`. -/
theorem two_pow_zmod_eq_one_iff (n k : ℕ) :
    (2 : ZMod n) ^ k = 1 ↔ 2 ^ k ≡ 1 [MOD n] := by
  have h := ZMod.natCast_eq_natCast_iff (2 ^ k) 1 n
  simpa using h

/-! ### The main theorem: `2` is a primitive root modulo `3 ^ m` -/

/-- **`2` is a primitive root modulo every power of `3`**: its multiplicative
order in `ZMod (3 ^ m)` is `2 * 3 ^ (m - 1) = φ (3 ^ m)`. -/
theorem orderOf_two_zmod_three_pow (m : ℕ) (hm : 1 ≤ m) :
    orderOf (2 : ZMod (3 ^ m)) = 2 * 3 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- `-2 = 1 + 3 * (-1)` has order `3 ^ n` (lifting the exponent).
  have hkey : orderOf (-2 : ZMod (3 ^ (n + 1))) = 3 ^ n := by
    have h := ZMod.orderOf_one_add_mul_prime Nat.prime_three (by norm_num) (-1)
      (by norm_num) n
    convert h using 2
    push_cast
    ring
  -- `-1` has order `2`.
  have hne : (-1 : ZMod (3 ^ (n + 1))) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod (3 ^ (n + 1))) = 0 := by push_cast; linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    have h3 : (3 : ℕ) ≤ 3 ^ (n + 1) := by
      calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hneg1 : orderOf (-1 : ZMod (3 ^ (n + 1))) = 2 :=
    orderOf_eq_prime neg_one_sq hne
  -- The two orders are coprime, so the order of the product is the product.
  have hco : Nat.Coprime (orderOf (-1 : ZMod (3 ^ (n + 1))))
      (orderOf (-2 : ZMod (3 ^ (n + 1)))) := by
    rw [hneg1, hkey]
    exact Nat.Coprime.pow_right n (by decide)
  have hprod : ((-1) * (-2) : ZMod (3 ^ (n + 1))) = 2 := by norm_num
  rw [← hprod, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hco, hneg1, hkey]

/-- Coprimality of `2` with `3 ^ m`, for building the unit. -/
theorem coprime_two_three_pow (m : ℕ) : Nat.Coprime 2 (3 ^ m) :=
  Nat.Coprime.pow_right m (by decide)

/-- `2` as a unit of `ZMod (3 ^ m)`. -/
def twoUnit (m : ℕ) : (ZMod (3 ^ m))ˣ :=
  ZMod.unitOfCoprime 2 (coprime_two_three_pow m)

/-- The order of `2` as a *unit* of `ZMod (3 ^ m)` is `2 * 3 ^ (m - 1)`. -/
theorem orderOf_twoUnit (m : ℕ) (hm : 1 ≤ m) :
    orderOf (twoUnit m) = 2 * 3 ^ (m - 1) := by
  rw [twoUnit, ← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  exact orderOf_two_zmod_three_pow m hm

/-! ### `2` generates the full unit group -/

/-- **`2` generates `(ZMod (3 ^ m))ˣ`**: the cyclic subgroup it generates has
cardinality `orderOf 2 = 2 * 3 ^ (m - 1) = φ (3 ^ m)`, the order of the whole
group, hence is everything. -/
theorem mem_zpowers_twoUnit (m : ℕ) (hm : 1 ≤ m) (u : (ZMod (3 ^ m))ˣ) :
    u ∈ Subgroup.zpowers (twoUnit m) := by
  have : NeZero ((3 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have htop : Subgroup.zpowers (twoUnit m) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, orderOf_twoUnit m hm, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_three hm]
    omega
  rw [htop]
  exact Subgroup.mem_top u

/-- Uniformity ingredient: every doubling orbit `k ↦ a * 2 ^ k` on the units
of `ZMod (3 ^ m)` visits every unit (once per period `2 * 3 ^ (m - 1)`). -/
theorem exists_pow_mul_eq_unit (m : ℕ) (hm : 1 ≤ m) (a u : (ZMod (3 ^ m))ˣ) :
    ∃ k < 2 * 3 ^ (m - 1), a * twoUnit m ^ k = u := by
  have horder : orderOf (twoUnit m) = 2 * 3 ^ (m - 1) := orderOf_twoUnit m hm
  have hmem : a⁻¹ * u ∈ Subgroup.zpowers (twoUnit m) :=
    mem_zpowers_twoUnit m hm _
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k % (2 * 3 ^ (m - 1)), Nat.mod_lt _ (by positivity), ?_⟩
  rw [← horder, pow_mod_orderOf, hk]
  exact mul_inv_cancel_left a u

end NormalNumbers
