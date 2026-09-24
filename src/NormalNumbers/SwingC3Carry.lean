/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Digits

/-!
# The carry of `G_b` is a SHORT-window functional of `ω`

`omegaCarry b k = ⌊T_b(k)⌋` looks like a functional of the whole future `ω(k+1), ω(k+2), …`.
It is not: the tail splits exactly,

    T_b(k) = ∑_{j=1}^{J} ω(k+j) b^{−j}  +  b^{−J} · T_b(k+J)        (`tailB_split`)

and `T_b(m) ≤ (m + 2)` crudely (`tailB_le`), so the remainder is `≤ (k+J+2)/b^J`, which is
below `1` as soon as `J ≳ log_b k`.  Hence `omegaCarry b k` is pinned to within one unit by the
window `ω(k+1), …, ω(k+J)` alone (`omegaCarry_sandwich`), and the whole length-`ℓ` digit window
of `G_b` at `n` is a function of `ω` on `[n+1, n+ℓ+J]` with `J = O(log_b n)`.

This is the structural fact `OmegaCarryJoint` (`SwingC3.lean`) has to exploit: the carry is not
"far-future measurable", it lives in a window that is *shorter than any power of `n`*, which is
exactly the regime where the Kubilius model gives joint Erdős–Kac for the shifts.
-/

open Finset

namespace NormalNumbers

open PrimeLambert G4

/-- The visible head of the carry: `∑_{j=1}^{J} ω(k+j) b^{−j}`. -/
noncomputable def carryHead (b k J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range J, omegaR (k + i + 1) / (b : ℝ) ^ (i + 1)

/-- **Exact tail splitting**: the carry tail after `J` steps is the tail at `k + J`, scaled. -/
theorem tailB_split {b : ℕ} (hb : 2 ≤ b) (k J : ℕ) :
    G4.tailB b k = carryHead b k J + G4.tailB b (k + J) / (b : ℝ) ^ J := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by positivity
  have hsum := (G4.summable_tailB hb k).sum_add_tsum_nat_add J
  rw [G4.tailB, ← hsum, carryHead]
  congr 1
  rw [eq_div_iff (by positivity), G4.tailB, ← tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [show i + J = J + i by ring, show k + (J + i) + 1 = (k + J) + i + 1 by ring]
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  ring_nf

/-- A crude but explicit bound on the tail: `T_b(m) ≤ m + 2`. -/
theorem tailB_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) : G4.tailB b m ≤ (m : ℝ) + 2 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set r : ℝ := 1 / (b : ℝ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrdef]; exact one_div_le_one_div_of_le (by norm_num) hbR
  have hr1 : r < 1 := by linarith
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hgeom : ∑' i : ℕ, r ^ i = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hmul : ∑' i : ℕ, (i : ℝ) * r ^ i = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsg : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_lt_one hr0 hr1
  have hsm : Summable (fun i : ℕ => (i : ℝ) * r ^ i) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa using this
  set M : ℕ → ℝ := fun i => r * (((m : ℝ) + 1) * r ^ i + (i : ℝ) * r ^ i) with hM
  have hsM : Summable M := ((hsg.mul_left _).add hsm).mul_left r
  have hterm : ∀ i : ℕ, omegaR (m + i + 1) / (b : ℝ) ^ (i + 1) ≤ M i := by
    intro i
    have hpow : (1 : ℝ) / (b : ℝ) ^ (i + 1) = r ^ (i + 1) := by
      rw [hrdef, div_pow, one_pow]
    have hle : omegaR (m + i + 1) ≤ (m : ℝ) + 1 + i := by
      have := omegaR_le (m + i + 1); push_cast at this ⊢; linarith
    have hrp : (0 : ℝ) ≤ r ^ (i + 1) := by positivity
    calc omegaR (m + i + 1) / (b : ℝ) ^ (i + 1)
        = omegaR (m + i + 1) * r ^ (i + 1) := by rw [div_eq_mul_one_div, hpow]
      _ ≤ ((m : ℝ) + 1 + i) * r ^ (i + 1) := by gcongr
      _ = M i := by rw [hM]; ring
  have hsum_le : G4.tailB b m ≤ ∑' i : ℕ, M i :=
    (G4.summable_tailB hb m).tsum_le_tsum hterm hsM
  refine hsum_le.trans ?_
  have htM : ∑' i : ℕ, M i = r * (((m : ℝ) + 1) * (1 - r)⁻¹ + r / (1 - r) ^ 2) := by
    rw [hM, tsum_mul_left, Summable.tsum_add (hsg.mul_left _) hsm, tsum_mul_left, hgeom, hmul]
  rw [htM]
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have h1 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith
  have h2 : r / (1 - r) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  calc r * (((m : ℝ) + 1) * (1 - r)⁻¹ + r / (1 - r) ^ 2)
      ≤ r * (((m : ℝ) + 1) * 2 + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hr0
        have := mul_le_mul_of_nonneg_left h1 hmnn
        linarith
    _ ≤ (m : ℝ) + 2 := by nlinarith

/-- **The carry is pinned by a window of length `J`.**  `carryHead b k J` uses only
`ω(k+1), …, ω(k+J)`, and the unseen remainder is `b^{−J} T_b(k+J) ≤ (k+J+2)/b^J`. -/
theorem omegaCarry_sandwich {b : ℕ} (hb : 2 ≤ b) (k J : ℕ) :
    ⌊carryHead b k J⌋₊ ≤ omegaCarry b k ∧
      (omegaCarry b k : ℝ) ≤ carryHead b k J + ((k : ℝ) + J + 2) / (b : ℝ) ^ J := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by positivity
  have hsplit := tailB_split hb k J
  have hrem0 : 0 ≤ G4.tailB b (k + J) / (b : ℝ) ^ J :=
    div_nonneg (tailB_nonneg hb _) (by positivity)
  have hrem : G4.tailB b (k + J) / (b : ℝ) ^ J ≤ ((k : ℝ) + J + 2) / (b : ℝ) ^ J := by
    have := tailB_le hb (k + J)
    push_cast at this
    gcongr
  constructor
  · exact Nat.floor_le_floor (by rw [hsplit]; linarith)
  · have : (omegaCarry b k : ℝ) ≤ G4.tailB b (k + 0) := by
      rw [Nat.add_zero, omegaCarry]
      exact Nat.floor_le (tailB_nonneg hb k)
    rw [Nat.add_zero] at this
    rw [hsplit] at this
    linarith

end NormalNumbers
