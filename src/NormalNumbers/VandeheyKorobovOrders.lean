/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovRounded

/-!
# Order lifting for Vandehey's Korobov estimate

This file begins the order-theoretic part of Proposition 4.1.  It proves Claim 4.4,
identifying the largest divisor on which the order stays fixed, and packages the exact
local lifting-the-exponent identity needed for Claims 4.5 and 4.6.  The latter includes
the exceptional prime `2` under the paper's `4`-divisibility condition.
-/

namespace NormalNumbers.VandeheyKorobov

/-- Uniform LTE for `x^n - 1`, including `p = 2` when `x ≡ 1 (mod 4)`.

The odd-prime branch is mathlib's standard LTE theorem.  The `p = 2` branch uses the
strong all-exponents form of LTE; the additional congruence modulo `4` is precisely the
exceptional condition preserved by `roundedDivisor` in equation (12). -/
lemma padicValNat_pow_sub_one_eq_add
    {p x n : ℕ} (hp : p.Prime) (hx : 1 < x) (hn : n ≠ 0)
    (hpx : p ∣ x - 1) (hpnx : ¬ p ∣ x) (hfour : p = 2 → 4 ∣ x - 1) :
    padicValNat p (x ^ n - 1) =
      padicValNat p (x - 1) + padicValNat p n := by
  by_cases hp2 : p = 2
  · subst p
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpow0 : x ^ n - 1 ≠ 0 := by
      have : 1 < x ^ n := Nat.one_lt_pow hn hx
      omega
    have hsub0 : x - 1 ≠ 0 := by omega
    have hfourZ : (4 : ℤ) ∣ (x : ℤ) - 1 := by
      rcases hfour rfl with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← Int.natCast_one, ← Int.natCast_sub hx.le]
      exact_mod_cast hc
    have hpnxZ : ¬ (2 : ℤ) ∣ (x : ℤ) := by
      exact_mod_cast hpnx
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
    rw [padicValNat_eq_emultiplicity hpow0,
      padicValNat_eq_emultiplicity hsub0, padicValNat_eq_emultiplicity hn]
    iterate 3 rw [← Int.natCast_emultiplicity]
    simpa [Int.ofNat_sub hx.le,
      Int.ofNat_sub (Nat.one_le_pow n x (by omega))] using
      (Int.two_pow_sub_pow' (x := (x : ℤ)) (y := 1) n hfourZ hpnxZ)
  · let _ : Fact p.Prime := ⟨hp⟩
    simpa only [one_pow] using
      (padicValNat.pow_sub_pow (p := p) (y := 1) (hp.odd_of_ne_two hp2)
        hx hpx hpnx hn)

/-- **Vandehey, Claim 4.4.**  If `τ` is the order of `b` modulo `m'`, then
`gcd(b^τ - 1, m)` also has order `τ`, and is the largest divisor of `m` with that order.

The maximality conclusion is stated as divisibility, which is the exact form consumed by
the local order-growth argument in Claim 4.5. -/
theorem orderOf_gcd_pow_sub_one_eq_and_maximal
    (b m m' : ℕ) (hb : 2 ≤ b) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    orderOf (b : ZMod mbar) = τ ∧
      ∀ D : ℕ, D ∣ m → orderOf (b : ZMod D) = τ → D ∣ mbar := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    simp only [Nat.coprime_zero_right] at hbm
    omega
  have hm'cop : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr ((ZMod.isUnit_iff_coprime b m').mpr hm'cop).isOfFinOrder
  have hpowgt : 1 < b ^ τ := Nat.one_lt_pow hτpos.ne' (by omega)
  have hm'pow : m' ∣ b ^ τ - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpowgt.le]
    push_cast
    dsimp [τ]
    rw [pow_orderOf_eq_one]
    simp
  have hm'mbar : m' ∣ mbar := by
    dsimp [mbar]
    exact Nat.dvd_gcd hm'pow hm'dvd
  have hmbarpow : mbar ∣ b ^ τ - 1 := Nat.gcd_dvd_left _ _
  have hτmbar : τ ∣ orderOf (b : ZMod mbar) := by
    dsimp [τ]
    have hmap := orderOf_map_dvd
      (ZMod.castHom hm'mbar (ZMod m')).toMonoidHom (b : ZMod mbar)
    simpa using hmap
  have hmbarτ : orderOf (b : ZMod mbar) ∣ τ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hz : ((b ^ τ - 1 : ℕ) : ZMod mbar) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hmbarpow
    rw [Nat.cast_sub hpowgt.le] at hz
    push_cast at hz ⊢
    exact sub_eq_zero.mp hz
  have horder : orderOf (b : ZMod mbar) = τ := Nat.dvd_antisymm hmbarτ hτmbar
  refine ⟨horder, ?_⟩
  intro D hDm hDorder
  have hDpow : D ∣ b ^ τ - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpowgt.le]
    push_cast
    exact sub_eq_zero.mpr (by
      simpa [hDorder] using (pow_orderOf_eq_one (b : ZMod D)))
  exact Nat.dvd_gcd hDpow hDm

end NormalNumbers.VandeheyKorobov
