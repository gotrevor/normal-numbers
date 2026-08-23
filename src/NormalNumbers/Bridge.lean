/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# The sequence ↔ real bridge

A digit sequence that does not eventually stick at `b − 1` is recovered
exactly by the digit map of the real number it sums to.  This is the lemma
that upgrades any *sequence*-normality theorem (e.g. Champernowne's) to a
statement about the corresponding *real number*.

The proof is the classical positional-expansion computation: writing
`F i = s i / b^(i+1)`, the series `∑ F` splits at every index into a finite
head (a natural number after scaling by `b^(i+1)`) plus a tail lying in
`[0, 1/b^(i+1))` — the *strict* upper bound is exactly where properness of
the digit sequence enters, via a termwise-strict comparison with the
geometric tail `∑ (b−1)/b^(n+k+1) = 1/b^n`.
-/

namespace NormalNumbers

/-- A digit sequence is **proper** if it does not eventually stick at
`b − 1`: past every index there is a digit `≠ b - 1`.  (The improper
expansion `0.d₁…dₖ(b−1)(b−1)…` denotes the same real as a terminating one,
and the digit map recovers the terminating form instead.) -/
def ProperDigits (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1

/-- The digit series `∑ s i / b^(i+1)` is summable (comparison with the
geometric series `∑ (1/b)^i`). -/
private theorem summable_digitTerm (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) :
    Summable (fun i : ℕ => (s i : ℝ) / (b : ℝ) ^ (i + 1)) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hb1))
  rw [inv_pow, div_le_iff₀ (pow_pos hb0 (i + 1)), pow_succ,
    inv_mul_cancel_left₀ (pow_pos hb0 i).ne']
  exact_mod_cast (hs i).le

/-- Each term of the dominating tail series is the corresponding term of a
geometric series, factored. -/
private theorem tail_term_eq (b : ℕ) (n k : ℕ) :
    ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1)
      = (((b : ℝ) - 1) / (b : ℝ) ^ (n + 1)) * ((b : ℝ)⁻¹) ^ k := by
  rw [(by omega : k + n + 1 = n + 1 + k), pow_add, ← div_div, div_eq_mul_inv,
    inv_pow]

/-- Geometric tail evaluation: `∑ₖ (b−1)/b^(n+k+1) = 1/b^n`. -/
private theorem tsum_tail_geom (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∑' k : ℕ, ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) = 1 / (b : ℝ) ^ n := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hbne : (b : ℝ) ≠ 0 := hb0.ne'
  have hbsubne : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hb1.ne'
  have h1 : (1 : ℝ) - (b : ℝ)⁻¹ = ((b : ℝ) - 1) / (b : ℝ) := by
    rw [sub_div, div_self hbne, one_div]
  rw [tsum_congr (tail_term_eq b n), tsum_mul_left,
    tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1),
    h1, inv_div, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hbne) hbsubne)
      (pow_ne_zero n hbne)]
  ring

/-- **Strict** tail bound: past index `n` the digit series contributes
strictly less than `1/b^n`.  Properness supplies an index `j ≥ n` whose
digit is `< b − 1`, making the comparison with the geometric tail strict. -/
private theorem tsum_tail_lt (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) (n : ℕ) :
    ∑' k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1) < 1 / (b : ℝ) ^ n := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hb1n : 1 ≤ b := by omega
  have hbsub : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub hb1n, Nat.cast_one]
  obtain ⟨j, hjn, hj⟩ := hp n
  have hgsum : Summable (fun k : ℕ => ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1)) := by
    refine Summable.congr ((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹)
      (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left
        (((b : ℝ) - 1) / (b : ℝ) ^ (n + 1))) fun k => ?_
    exact (tail_term_eq b n k).symm
  have hle : ∀ k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1)
      ≤ ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) := by
    intro k
    have h1 : s (k + n) ≤ b - 1 := by have := hs (k + n); omega
    have h2 : (s (k + n) : ℝ) ≤ (b : ℝ) - 1 := by
      rw [← hbsub]; exact_mod_cast h1
    exact div_le_div_of_nonneg_right h2 (pow_pos hb0 _).le
  have hstrict : (s ((j - n) + n) : ℝ) / (b : ℝ) ^ ((j - n) + n + 1)
      < ((b : ℝ) - 1) / (b : ℝ) ^ ((j - n) + n + 1) := by
    have hjeq : (j - n) + n = j := by omega
    have h1 : s j < b - 1 := by have := hs j; omega
    have h2 : (s ((j - n) + n) : ℝ) < (b : ℝ) - 1 := by
      rw [hjeq, ← hbsub]; exact_mod_cast h1
    exact div_lt_div_of_pos_right h2 (pow_pos hb0 _)
  calc ∑' k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1)
      < ∑' k : ℕ, ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) :=
        Summable.tsum_lt_tsum_of_nonneg (fun k => by positivity) hle hstrict hgsum
    _ = 1 / (b : ℝ) ^ n := tsum_tail_geom b hb n

theorem realOfDigits_mem_Ico (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) :
    realOfDigits b s ∈ Set.Ico (0 : ℝ) 1 := by
  rw [Set.mem_Ico]
  constructor
  · exact tsum_nonneg fun i => by positivity
  · have h := tsum_tail_lt b hb s hs hp 0
    simp only [Nat.add_zero, pow_zero, div_one] at h
    exact h

/-- Scaling by `b^(i+1)` turns the length-`(i+1)` head of the digit series
into the natural number `∑ₖ s k · b^(i−k)`. -/
private theorem head_mul_pow (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ) (i : ℕ) :
    (∑ k ∈ Finset.range (i + 1), (s k : ℝ) / (b : ℝ) ^ (k + 1)) * (b : ℝ) ^ (i + 1)
      = ((∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) : ℝ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  rw [Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [div_mul_eq_mul_div, div_eq_iff (pow_pos hb0 (k + 1)).ne', mul_assoc,
    ← pow_add, (by omega : i - k + (k + 1) = i + 1)]

/-- The floor of `realOfDigits b s · b^(i+1)` is the integer whose base-`b`
digits are `s 0 … s i`: the head contributes exactly that natural number and
the (proper) tail contributes an amount in `[0, 1)`. -/
private theorem floor_realOfDigits_mul_pow (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) (i : ℕ) :
    ⌊realOfDigits b s * (b : ℝ) ^ (i + 1)⌋
      = (∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hpowpos : (0 : ℝ) < (b : ℝ) ^ (i + 1) := pow_pos hb0 (i + 1)
  have hsum := summable_digitTerm b hb s hs
  have hx : realOfDigits b s
      = (∑ k ∈ Finset.range (i + 1), (s k : ℝ) / (b : ℝ) ^ (k + 1))
        + ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1) :=
    (hsum.sum_add_tsum_nat_add (i + 1)).symm
  have htail0 : (0 : ℝ) ≤ ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1) :=
    tsum_nonneg fun k => by positivity
  have htail1 : ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1)
      < 1 / (b : ℝ) ^ (i + 1) := tsum_tail_lt b hb s hs hp (i + 1)
  have key : realOfDigits b s * (b : ℝ) ^ (i + 1)
      = ((∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) : ℝ)
        + (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
            * (b : ℝ) ^ (i + 1) := by
    rw [hx, add_mul, head_mul_pow b hb s i]
  have htail1' : (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
      * (b : ℝ) ^ (i + 1) < 1 := by
    have := mul_lt_mul_of_pos_right htail1 hpowpos
    rwa [one_div, inv_mul_cancel₀ hpowpos.ne'] at this
  have htail0' : (0 : ℝ) ≤ (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
      * (b : ℝ) ^ (i + 1) := mul_nonneg htail0 hpowpos.le
  rw [Int.floor_eq_iff]
  constructor
  · rw [key]; push_cast; linarith
  · rw [key]; push_cast; linarith

/-- **The bridge**: the digit map inverts `realOfDigits` on proper digit
sequences. -/
theorem digitOf_realOfDigits (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s) :
    digitOf b (realOfDigits b s) = s := by
  funext i
  show (⌊realOfDigits b s * (b : ℝ) ^ (i + 1)⌋).toNat % b = s i
  rw [floor_realOfDigits_mul_pow b hb s hs hp i, Int.toNat_natCast,
    Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  have hdvd : b ∣ ∑ k ∈ Finset.range i, s k * b ^ (i - k) := by
    refine Finset.dvd_sum fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [(by omega : i - k = (i - k - 1) + 1), pow_succ, ← mul_assoc]
    exact dvd_mul_left b _
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (hs i)

/-- Sequence normality upgrades to real-number normality along the bridge. -/
theorem isNormal_realOfDigits (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ProperDigits b s)
    (hn : IsNormalSequence b s) : IsNormal b (realOfDigits b s) := by
  have hmem := realOfDigits_mem_Ico b hb s hs hp
  rw [Set.mem_Ico] at hmem
  show IsNormalSequence b (digitOf b (Int.fract (realOfDigits b s)))
  rw [Int.fract_eq_self.mpr hmem, digitOf_realOfDigits b hb s hs hp]
  exact hn

end NormalNumbers
