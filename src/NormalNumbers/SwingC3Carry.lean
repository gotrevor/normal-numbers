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

and `T_b(m) ≤ log₂ m + 2` (`tailB_le_log`, from `ω(n) ≤ log₂ n`), so the remainder is
`≤ (log₂(k+J) + 2)/b^J`, which is below `1` as soon as `J ≳ log_b log₂ k`.  Hence
`omegaCarry b k` is pinned to within one unit by the window `ω(k+1), …, ω(k+J)` alone
(`omegaCarry_sandwich_log`), and the whole length-`ℓ` digit window of `G_b` at `n` is a function
of `ω` on `[n+1, n+ℓ+J]` with `J = O(log_b log n)` — an *iterated-logarithmically* short window.

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

/-- Generic tail bound: if `ω(m+i+1) ≤ A + 1 + i` for every `i`, then `T_b(m) ≤ A + 2`. -/
theorem tailB_le_of_bound {b : ℕ} (hb : 2 ≤ b) (m : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hbd : ∀ i : ℕ, omegaR (m + i + 1) ≤ A + 1 + i) : G4.tailB b m ≤ A + 2 := by
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
  set M : ℕ → ℝ := fun i => r * ((A + 1) * r ^ i + (i : ℝ) * r ^ i) with hM
  have hsM : Summable M := ((hsg.mul_left _).add hsm).mul_left r
  have hterm : ∀ i : ℕ, omegaR (m + i + 1) / (b : ℝ) ^ (i + 1) ≤ M i := by
    intro i
    have hpow : (1 : ℝ) / (b : ℝ) ^ (i + 1) = r ^ (i + 1) := by
      rw [hrdef, div_pow, one_pow]
    have hle : omegaR (m + i + 1) ≤ A + 1 + i := hbd i
    have hrp : (0 : ℝ) ≤ r ^ (i + 1) := by positivity
    calc omegaR (m + i + 1) / (b : ℝ) ^ (i + 1)
        = omegaR (m + i + 1) * r ^ (i + 1) := by rw [div_eq_mul_one_div, hpow]
      _ ≤ (A + 1 + i) * r ^ (i + 1) := by gcongr
      _ = M i := by rw [hM]; ring
  have hsum_le : G4.tailB b m ≤ ∑' i : ℕ, M i :=
    (G4.summable_tailB hb m).tsum_le_tsum hterm hsM
  refine hsum_le.trans ?_
  have htM : ∑' i : ℕ, M i = r * ((A + 1) * (1 - r)⁻¹ + r / (1 - r) ^ 2) := by
    rw [hM, tsum_mul_left, Summable.tsum_add (hsg.mul_left _) hsm, tsum_mul_left, hgeom, hmul]
  rw [htM]
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have h1 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith
  have h2 : r / (1 - r) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hmnn : (0 : ℝ) ≤ A + 1 := by linarith
  calc r * ((A + 1) * (1 - r)⁻¹ + r / (1 - r) ^ 2)
      ≤ r * ((A + 1) * 2 + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hr0
        have := mul_le_mul_of_nonneg_left h1 hmnn
        linarith
    _ ≤ A + 2 := by nlinarith

/-- `ω(n) ≤ log₂ n`: the `ω(n)` distinct prime factors are all `≥ 2` and their product divides
`n`. -/
theorem cardDistinctFactors_le_log_two {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.cardDistinctFactors n ≤ Nat.log 2 n := by
  rw [cardDistinctFactors_eq_card_primeFactors]
  refine (Nat.le_log_iff_pow_le (by norm_num) hn).2 ?_
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- `log₂(m+j) ≤ log₂ m + j` for `m ≥ 1`. -/
theorem log_two_add_le {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    Nat.log 2 (m + j) ≤ Nat.log 2 m + j := by
  have hmj : ∀ i : ℕ, m + i ≤ m * 2 ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        have h1 : 1 ≤ m * 2 ^ i := Nat.one_le_iff_ne_zero.2 (by positivity)
        calc m + (i + 1) ≤ m * 2 ^ i + 1 := by omega
          _ ≤ m * 2 ^ i + m * 2 ^ i := by omega
          _ = m * 2 ^ (i + 1) := by ring
  by_cases hj : Nat.log 2 (m + j) ≤ j
  · omega
  · have hmj := hmj j
    have hp : 2 ^ (Nat.log 2 (m + j) - j) ≤ m := by
      have h2 : 2 ^ Nat.log 2 (m + j) ≤ m + j := Nat.pow_log_le_self 2 (by omega)
      have h3 : 2 ^ (Nat.log 2 (m + j) - j) * 2 ^ j = 2 ^ Nat.log 2 (m + j) := by
        rw [← pow_add]; congr 1; omega
      have h4 : 2 ^ (Nat.log 2 (m + j) - j) * 2 ^ j ≤ m * 2 ^ j := by
        rw [h3]; omega
      exact Nat.le_of_mul_le_mul_right h4 (by positivity)
    have := (Nat.le_log_iff_pow_le (by norm_num) (show m ≠ 0 by omega)).2 hp
    omega

/-- The crude bound `T_b(m) ≤ m + 2`. -/
theorem tailB_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) : G4.tailB b m ≤ (m : ℝ) + 2 :=
  tailB_le_of_bound hb m (m : ℝ) (by positivity) fun i => by
    have := omegaR_le (m + i + 1); push_cast at this ⊢; linarith

/-- **The sharp tail bound**: `T_b(m) ≤ log₂ m + 2`.  This is what makes the carry window
`J = O(log_b log m)` rather than `O(log_b m)`. -/
theorem tailB_le_log {b : ℕ} (hb : 2 ≤ b) (m : ℕ) (hm : 1 ≤ m) :
    G4.tailB b m ≤ (Nat.log 2 m : ℝ) + 2 :=
  tailB_le_of_bound hb m (Nat.log 2 m : ℝ) (by positivity) fun i => by
    have h1 : ArithmeticFunction.cardDistinctFactors (m + i + 1) ≤ Nat.log 2 (m + (i + 1)) := by
      have := cardDistinctFactors_le_log_two (n := m + i + 1) (by omega)
      rwa [show m + i + 1 = m + (i + 1) by ring] at this
    have h2 : Nat.log 2 (m + (i + 1)) ≤ Nat.log 2 m + (i + 1) := log_two_add_le hm (i + 1)
    have : (ArithmeticFunction.cardDistinctFactors (m + i + 1) : ℝ) ≤ (Nat.log 2 m : ℝ) + (i + 1) := by
      have : ArithmeticFunction.cardDistinctFactors (m + i + 1) ≤ Nat.log 2 m + (i + 1) := by omega
      exact_mod_cast this
    rw [omegaR]; linarith

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

/-- **The sharp window bound.**  With `J` chosen so that `b^J > log₂(k+J) + 2` — that is,
`J ≈ log_b log₂ k` — the unseen remainder is `< 1`, so `omegaCarry b k` is determined by
`ω(k+1), …, ω(k+J)` up to one unit. -/
theorem omegaCarry_sandwich_log {b : ℕ} (hb : 2 ≤ b) (k J : ℕ) (hk : 1 ≤ k) :
    ⌊carryHead b k J⌋₊ ≤ omegaCarry b k ∧
      (omegaCarry b k : ℝ) ≤ carryHead b k J
        + ((Nat.log 2 (k + J) : ℝ) + 2) / (b : ℝ) ^ J := by
  have hsplit := tailB_split hb k J
  have hrem0 : 0 ≤ G4.tailB b (k + J) / (b : ℝ) ^ J :=
    div_nonneg (tailB_nonneg hb _) (by positivity)
  have hrem : G4.tailB b (k + J) / (b : ℝ) ^ J
      ≤ ((Nat.log 2 (k + J) : ℝ) + 2) / (b : ℝ) ^ J := by
    have := tailB_le_log hb (k + J) (by omega)
    gcongr
  refine ⟨Nat.floor_le_floor (by rw [hsplit]; linarith), ?_⟩
  have hle : (omegaCarry b k : ℝ) ≤ G4.tailB b k := by
    rw [omegaCarry]; exact Nat.floor_le (tailB_nonneg hb k)
  rw [hsplit] at hle
  linarith

/-! ### The carry recursion: `G_b`'s digits are a base-`b` adder automaton driven by `ω` -/

/-- `carryHead b k 1 = ω(k+1)/b`. -/
@[simp] lemma carryHead_one (b k : ℕ) : carryHead b k 1 = omegaR (k + 1) / (b : ℝ) := by
  simp [carryHead]

/-- **The carry recursion.**  Together with `digitOf_primeLambertAtBase` this says: the digit
stream of `G_b` is exactly the output of the base-`b` addition automaton run right-to-left on
the input stream `ω(1), ω(2), …`, with `omegaCarry b k` the carry state at position `k`. -/
theorem omegaCarry_succ {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    omegaCarry b k = (ArithmeticFunction.cardDistinctFactors (k + 1) + omegaCarry b (k + 1)) / b := by
  have hsplit := tailB_split hb k 1
  rw [carryHead_one, pow_one] at hsplit
  have hT : G4.tailB b k = ((ArithmeticFunction.cardDistinctFactors (k + 1) : ℝ)
      + G4.tailB b (k + 1)) / (b : ℝ) := by
    rw [hsplit, omegaR]; ring
  rw [omegaCarry, hT, Nat.floor_div_natCast, omegaCarry]
  congr 1
  rw [add_comm, Nat.floor_add_natCast (tailB_nonneg hb _), add_comm]

end NormalNumbers
