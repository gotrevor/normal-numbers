/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Transport

/-!
# The arithmetic formula for the digits of `G_b = ∑ ω(n)/bⁿ`

The `ConjC3` campaign needs the base-`b` digits of `G_b` *as an arithmetic object*, not just as
`digitOf`.  This file supplies the bridge:

    digitOf b (fract G_b) n  =  (ω(n+1) + omegaCarry b (n+1)) % b,

where `omegaCarry b k = ⌊T_b(k)⌋` is the carry coming in from the infinite tail
`T_b(k) = ∑_{j ≥ 1} ω(k+j) b^{-j}` (`G4Transport.tailB`).  So the digit sequence of `G_b` is
`ω` read modulo `b`, perturbed by a carry which is itself a tail functional of `ω`.

This is the input for the Erdős–Kac attack on `ConjC3`: `ω(n)` is asymptotically
`N(log log n, log log n)`, so `ω(n) mod b` equidistributes with discrepancy
`≍ (log n)^{−2π²/b²}`, and a word `w` of length `ℓ` occurs at `n` exactly when
`ω(n+1+j) + omegaCarry b (n+1+j) ≡ w_j (mod b)` for every `j < ℓ`.
-/

open Finset

namespace NormalNumbers

open PrimeLambert G4

/-- The carry into digit position `k`: the integer part of the tail `T_b(k)`. -/
noncomputable def omegaCarry (b k : ℕ) : ℕ := ⌊G4.tailB b k⌋₊

lemma tailB_nonneg {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : 0 ≤ G4.tailB b k :=
  tsum_nonneg fun i => by
    have := omegaR_nonneg (k + i + 1)
    have hb0 : (0 : ℝ) < (b : ℝ) ^ (i + 1) := by positivity
    positivity

/-- `⌊T_b(k)⌋` as an integer. -/
lemma intFloor_tailB {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    ⌊G4.tailB b k⌋ = (omegaCarry b k : ℤ) := by
  rw [omegaCarry, Int.natCast_floor_eq_floor (tailB_nonneg hb k)]

/-- `∑_{m ≤ k} b^{k−m} ω(m) ≡ ω(k) (mod b)`: every term but the last carries a factor `b`. -/
lemma tailIntB_mod {b : ℕ} (k : ℕ) :
    G4.tailIntB b k % b = ArithmeticFunction.cardDistinctFactors k % b := by
  unfold G4.tailIntB
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have hdvd : b ∣ ∑ m ∈ Finset.range k, b ^ (k - m) * ArithmeticFunction.cardDistinctFactors m :=
    Finset.dvd_sum fun m hm => by
      have : 1 ≤ k - m := by have := Finset.mem_range.1 hm; omega
      exact Dvd.dvd.mul_right (dvd_pow_self b (by omega)) _
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_add_mod]

/-- **The digit formula.**  Digit `n` of `G_b = ∑ ω(m)/bᵐ` is `ω(n+1)` plus the tail carry,
read modulo `b`. -/
theorem digitOf_primeLambertAtBase {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    digitOf b (Int.fract (primeLambertAtBase b)) n
      = (ArithmeticFunction.cardDistinctFactors (n + 1) + omegaCarry b (n + 1)) % b := by
  set x := primeLambertAtBase b with hx
  set A : ℕ := G4.tailIntB b (n + 1) + omegaCarry b (n + 1) with hA
  -- `x · b^{n+1} = tailIntB + T_b(n+1)`
  have hxb : x * (b : ℝ) ^ (n + 1) = (G4.tailIntB b (n + 1) : ℝ) + G4.tailB b (n + 1) := by
    have := G4.tailB_eq (b := b) hb (n + 1)
    rw [hx]; linarith [this]
  have hfl : ⌊x * (b : ℝ) ^ (n + 1)⌋ = (A : ℤ) := by
    rw [hxb, add_comm ((G4.tailIntB b (n + 1) : ℝ)) _, Int.floor_add_natCast,
      intFloor_tailB hb, hA]
    push_cast; ring
  -- pass to the fractional part: the correction is a multiple of `b^{n+1}`
  have hfr : Int.fract x * (b : ℝ) ^ (n + 1) = x * (b : ℝ) ^ (n + 1) - (⌊x⌋ * (b : ℕ) ^ (n + 1) : ℤ) := by
    rw [Int.fract]
    push_cast; ring
  have hfl2 : ⌊Int.fract x * (b : ℝ) ^ (n + 1)⌋ = (A : ℤ) - (⌊x⌋ * (b : ℕ) ^ (n + 1) : ℤ) := by
    rw [hfr, Int.floor_sub_intCast, hfl]
  have hnn : (0 : ℤ) ≤ ⌊Int.fract x * (b : ℝ) ^ (n + 1)⌋ :=
    Int.floor_nonneg.2 (by positivity)
  -- now reduce mod `b`
  unfold digitOf
  have hcast : ((⌊Int.fract x * (b : ℝ) ^ (n + 1)⌋.toNat : ℕ) : ℤ)
      = (A : ℤ) - (⌊x⌋ * (b : ℕ) ^ (n + 1) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn, hfl2]
  have hmod : (⌊Int.fract x * (b : ℝ) ^ (n + 1)⌋.toNat) % b = A % b := by
    have h1 : ((⌊Int.fract x * (b : ℝ) ^ (n + 1)⌋.toNat % b : ℕ) : ℤ)
        = ((A % b : ℕ) : ℤ) := by
      rw [Int.natCast_mod, Int.natCast_mod, hcast,
        show (⌊x⌋ * (b : ℕ) ^ (n + 1) : ℤ) = (b : ℤ) * (⌊x⌋ * (b : ℤ) ^ n) by push_cast; ring,
        Int.sub_mul_emod_self_left]
    exact_mod_cast h1
  rw [hmod, hA, Nat.add_mod, tailIntB_mod, ← Nat.add_mod]

end NormalNumbers
