/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDisjunctivityDefs
import NormalNumbers.JointLambertDisjunctivity

/-!
# Reading a word from general integer coefficients

The existing Lambert digit calculation only needs nonnegative integer
coefficients bounded by their index, divisibility in the other slots, one
prescribed coefficient, and a small positive tail.  The arithmetic supply is
proved separately; this module is its generic consumer.
-/

namespace NormalNumbers.ArithmeticDisjunctivity
open Finset JointLambert

/-- The digit bridge for arbitrary bounded natural coefficients. -/
theorem floor_digit_of_coefficient_offset
    (f : ℕ → ℕ) (hf : ∀ m : ℕ, f m ≤ m)
    (b ℓ v c a r k N : ℕ) (hb : 2 ≤ b) (hbc : b ∣ c)
    (hv : v < b ^ ℓ) (hrk : r < k)
    (hkill : ∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ f (N + 1 + j))
    (hsurv : f (N + 1 + r) = 2 * a)
    (hlo : (v : ℝ) / (b : ℝ) ^ ℓ < Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)))
    (hhi : Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)) < ((v : ℝ) + 1 / 2) / (b : ℝ) ^ ℓ)
    (hT0 : 0 ≤ ∑' t : ℕ,
      (f (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1))
    (hT : ∑' t : ℕ, (f (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1)
            < (1 / 2) / (b : ℝ) ^ ℓ) :
    ⌊(b : ℝ) ^ ℓ * orbit b (coefficientValue f b) N⌋ = (v : ℤ) := by
  have hbpos : 0 < b := by omega
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbl0 : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  set τ := f with hτdef
  set T : ℝ := ∑' t : ℕ, (τ (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) with hTdef
  set y : ℝ := Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)) with hydef
  -- the full shifted tail, split at `k`
  have hsum := summable_shift_tail b hb τ hf N
  have hkspl := Summable.sum_add_tsum_nat_add k hsum
  have hfar : ∑' t : ℕ, (τ (N + 1 + (t + k)) : ℝ) / (b : ℝ) ^ (t + k + 1) = T := by
    rw [hTdef]
    exact tsum_congr fun t => by
      rw [show N + 1 + (t + k) = N + 1 + k + t from by omega,
        show t + k + 1 = k + t + 1 from by omega]
  -- every killed slot is an integer
  have hG : ∀ j ∈ (range k).erase r, (τ (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
      = ((τ (N + 1 + j) / b ^ (j + 1) : ℕ) : ℝ) := by
    intro j hj
    obtain ⟨hjr, hjk⟩ := Finset.mem_erase.mp hj
    have hdvd : b ^ (j + 1) ∣ τ (N + 1 + j) :=
      dvd_trans (pow_dvd_pow_of_dvd hbc (j + 1)) (hkill j (mem_range.mp hjk) hjr)
    have hne : ((b ^ (j + 1) : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℕ) < b ^ (j + 1) := Nat.pow_pos hbpos
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div hdvd hne]
    push_cast
    ring
  have hrmem : r ∈ range k := mem_range.2 hrk
  have hnear : ∑ j ∈ range k, (τ (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
      = ((∑ j ∈ (range k).erase r, (τ (N + 1 + j) / b ^ (j + 1)) : ℕ) : ℝ)
        + 2 * (a : ℝ) / (b : ℝ) ^ (r + 1) := by
    rw [← Finset.add_sum_erase _ _ hrmem, Finset.sum_congr rfl hG, ← Nat.cast_sum, hsurv]
    push_cast
    ring
  -- the master identity
  set Head : ℕ := ∑ m ∈ range (N + 1), τ m * b ^ (N - m) with hHead
  set Kill : ℕ := ∑ j ∈ (range k).erase r, (τ (N + 1 + j) / b ^ (j + 1)) with hKill
  have hmaster : coefficientValue f b * (b : ℝ) ^ N
      = ((Head + Kill : ℕ) : ℝ) + (2 * (a : ℝ) / (b : ℝ) ^ (r + 1) + T) := by
    change CastingOut.lambertVal b τ * (b : ℝ) ^ N = _
    rw [lambertVal_mul_pow_eq b hb τ hf N,
      ← hkspl, hfar, hnear, hHead]
    push_cast
    ring
  -- read the orbit
  have hylt : y + T < ((v : ℝ) + 1) / (b : ℝ) ^ ℓ := by
    have hne : ((b : ℝ) ^ ℓ) ≠ 0 := ne_of_gt hbl0
    have : ((v : ℝ) + 1 / 2) / (b : ℝ) ^ ℓ + (1 / 2) / (b : ℝ) ^ ℓ
        = ((v : ℝ) + 1) / (b : ℝ) ^ ℓ := by
      field_simp
      ring
    linarith [hhi, hT, this]
  have hvle : (v : ℝ) + 1 ≤ (b : ℝ) ^ ℓ := by
    have : (v : ℝ) + 1 ≤ ((b ^ ℓ : ℕ) : ℝ) := by
      have : (v : ℕ) + 1 ≤ b ^ ℓ := by omega
      exact_mod_cast this
    simpa using this
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hylt1 : y + T < 1 := by
    have h1 : ((v : ℝ) + 1) / (b : ℝ) ^ ℓ ≤ 1 := by
      rw [div_le_one hbl0]; exact hvle
    linarith
  have horb : orbit b (coefficientValue f b) N = y + T := by
    unfold orbit
    rw [hmaster, show ((Head + Kill : ℕ) : ℝ) = (((Head + Kill : ℕ) : ℤ) : ℝ) from by push_cast; ring,
      Int.fract_intCast_add]
    rw [show 2 * (a : ℝ) / (b : ℝ) ^ (r + 1)
        = ((⌊2 * (a : ℝ) / (b : ℝ) ^ (r + 1)⌋ : ℤ) : ℝ) + y from (Int.floor_add_fract _).symm,
      add_assoc, Int.fract_intCast_add]
    exact Int.fract_eq_self.2 ⟨by linarith, hylt1⟩
  rw [horb, Int.floor_eq_iff]
  have hlo' : (v : ℝ) < y * (b : ℝ) ^ ℓ := (div_lt_iff₀ hbl0).mp hlo
  have hTnn : 0 ≤ T * (b : ℝ) ^ ℓ := mul_nonneg hT0 hbl0.le
  have hup : (y + T) * (b : ℝ) ^ ℓ < (v : ℝ) + 1 := (lt_div_iff₀ hbl0).mp hylt
  constructor
  · push_cast
    nlinarith [hlo', hTnn]
  · push_cast
    nlinarith [hup]


end NormalNumbers.ArithmeticDisjunctivity
