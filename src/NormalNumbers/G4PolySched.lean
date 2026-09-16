/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedSched

/-!
# Campaign B: a `k₄` for an arbitrary polynomial coefficient bound

`exists_good_k₄_poly` hard-codes the quartic `⌈A⌉₊ + 368k₄² + 88320k₄⁴` coming from
`c_p ≤ log₂log₂ p`.  Widening the growth class to `c_p ≤ A₀(1 + log₂log₂ p)^s` multiplies the
degree by `s`, so the schedule needs the statement for an arbitrary degree.  Nothing changes:
the junk budget is *exponential* in `k₄`, so any polynomial is absorbed by `k₄ = 2^t`, which
turns `M·k₄^D ≤ 2^{k₄}` into the linear-versus-exponential `log₂M + tD ≤ 2^t`.
-/

open Finset

namespace NormalNumbers.G4

namespace SchedB

/-- **Linear versus exponential, with an explicit threshold.** -/
theorem exists_lin_le_two_pow (m D : ℕ) : ∃ T, ∀ t, T ≤ t → m + D * t ≤ 2 ^ t := by
  set a : ℕ := max (m + D) 2 with ha
  have ha2 : 2 ≤ a := le_max_right _ _
  have ham : m ≤ a := le_trans (Nat.le_add_right _ _) (le_max_left _ _)
  have haD : D ≤ a := le_trans (Nat.le_add_left _ _) (le_max_left _ _)
  refine ⟨8 * a, ?_⟩
  -- base case at `t = 8a`, then induction
  have hbase : m + D * (8 * a) ≤ 2 ^ (8 * a) := by
    have h1 : (a + 1) ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    have h2 : (a + 1) ^ 8 ≤ (2 ^ a) ^ 8 := Nat.pow_le_pow_left h1 8
    have h3 : ((2 : ℕ) ^ a) ^ 8 = 2 ^ (8 * a) := by rw [← pow_mul]; ring_nf
    have h4 : m + D * (8 * a) ≤ 9 * a ^ 2 := by nlinarith
    have h5 : 9 * a ^ 2 ≤ a ^ 8 := by
      have : a ^ 2 * 9 ≤ a ^ 2 * a ^ 6 := by
        refine Nat.mul_le_mul_left _ ?_
        calc (9 : ℕ) ≤ 2 ^ 6 := by norm_num
          _ ≤ a ^ 6 := Nat.pow_le_pow_left ha2 6
      calc 9 * a ^ 2 = a ^ 2 * 9 := by ring
        _ ≤ a ^ 2 * a ^ 6 := this
        _ = a ^ 8 := by ring
    have h6 : a ^ 8 ≤ (a + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    omega
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
      have hD : D ≤ 2 ^ n := by
        calc D ≤ a := haD
          _ ≤ 2 ^ a := (Nat.lt_two_pow_self).le
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      have : m + D * (n + 1) = (m + D * n) + D := by ring
      omega

/-- **A `k₄` for an arbitrary polynomial coefficient bound.**  `exists_good_k₄_poly` is the
case `a + γ·k₄^d` with `d = 4`. -/
theorem exists_good_k₄_polyGen (b ℓ a γ : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ∃ k₄, k₄bℓ b ℓ ≤ k₄ ∧ 40 ≤ k₄ ∧ a ≤ k₄ ∧
      100000 * (a + γ * k₄ ^ d) * k₄ ^ 3 ≤ 2 ^ k₄ := by
  obtain ⟨T, hT⟩ := exists_lin_le_two_pow (18 + γ) (d + 3)
  obtain ⟨t, ht, hts⟩ : ∃ t, T ≤ t ∧ max (max 40 a) (k₄bℓ b ℓ) ≤ 2 ^ t := by
    refine ⟨max T (max (max 40 a) (k₄bℓ b ℓ)), le_max_left _ _, ?_⟩
    exact le_trans (Nat.lt_two_pow_self).le
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  set k := 2 ^ t with hk
  have h40 : 40 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hts
  have ha : a ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hts
  have hbℓ : k₄bℓ b ℓ ≤ k := le_trans (le_max_right _ _) hts
  refine ⟨k, hbℓ, h40, ha, ?_⟩
  have hk1 : 1 ≤ k := by omega
  -- `a + γ k^d ≤ (1 + γ) k^d`
  have hkd : k ≤ k ^ d := Nat.le_self_pow (by omega) k
  have hpoly : a + γ * k ^ d ≤ (1 + γ) * k ^ d := by
    have : a ≤ k ^ d := le_trans ha hkd
    nlinarith
  have hγ : (1 + γ) ≤ 2 ^ (1 + γ) := (Nat.lt_two_pow_self).le
  have hstep : 100000 * (a + γ * k ^ d) * k ^ 3 ≤ 2 ^ 17 * (2 ^ (1 + γ) * k ^ (d + 3)) := by
    have h1 : 100000 * (a + γ * k ^ d) * k ^ 3 ≤ 100000 * ((1 + γ) * k ^ d) * k ^ 3 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpoly)
    have h2 : 100000 * ((1 + γ) * k ^ d) * k ^ 3 = 100000 * (1 + γ) * k ^ (d + 3) := by
      rw [pow_add]; ring
    have h3 : 100000 * (1 + γ) ≤ 2 ^ 17 * 2 ^ (1 + γ) := by
      have : (100000 : ℕ) ≤ 2 ^ 17 := by norm_num
      exact Nat.mul_le_mul this hγ
    calc 100000 * (a + γ * k ^ d) * k ^ 3 ≤ 100000 * (1 + γ) * k ^ (d + 3) := by
          rw [← h2]; exact h1
      _ ≤ (2 ^ 17 * 2 ^ (1 + γ)) * k ^ (d + 3) := Nat.mul_le_mul_right _ h3
      _ = 2 ^ 17 * (2 ^ (1 + γ) * k ^ (d + 3)) := by ring
  refine hstep.trans ?_
  have hrw : (2 : ℕ) ^ 17 * (2 ^ (1 + γ) * k ^ (d + 3)) = 2 ^ (18 + γ + (d + 3) * t) := by
    rw [hk, ← pow_mul, ← pow_add, ← pow_add]
    ring_nf
  rw [hrw, hk]
  exact Nat.pow_le_pow_right (by norm_num) (hT t ht)

end SchedB

end NormalNumbers.G4
