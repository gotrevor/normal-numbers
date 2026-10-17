/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal

/-!
# Mahler shifts for prime-class Stoneham series

The identity `alpha_(B^c,c) = c * alpha_(B,c) - B^(-c)` moves a factor of `c` from the
base exponent into the coefficient.  Iterating it is the algebraic normalization used in the
dependent half of the one-prime-class theorem: prime-power factors of the exponents can be
removed at the cost of a finite base-`B` rational correction.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset

/-- The one-step Mahler identity for a Stoneham series. -/
theorem stonehamAlpha_pow_base (B c : ℕ) (hB : 1 ≤ B) (hc : 2 ≤ c) :
    stonehamAlpha (B ^ c) c =
      (c : ℝ) * stonehamAlpha B c - 1 / (B : ℝ) ^ c := by
  let f : ℕ → ℝ := fun n =>
    1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))
  have hf : Summable f := by
    simpa only [f] using
      StonehamSumsNormal.summable_stonehamAlpha_term B c hB hc
  have hshift : stonehamAlpha (B ^ c) c = ∑' n, (c : ℝ) * f (n + 1) := by
    unfold stonehamAlpha
    apply tsum_congr
    intro n
    simp only [f]
    have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
    push_cast
    rw [← pow_mul]
    rw [show c * c ^ (n + 1) = c ^ (n + 1 + 1) by simp only [pow_succ]; ring]
    field_simp
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  have hsplit : stonehamAlpha B c = f 0 + ∑' n, f (n + 1) := by
    simpa only [stonehamAlpha, f, sum_range_one, Nat.zero_add] using
      (hf.sum_add_tsum_nat_add 1).symm
  rw [hshift, tsum_mul_left]
  rw [hsplit]
  simp only [f, zero_add, pow_one]
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  field_simp
  ring

/-- Iterating the Mahler identity removes an arbitrary power of the series parameter from the
base.  The displayed finite sum is the complete terminating correction. -/
theorem stonehamAlpha_pow_base_iterate (B c a : ℕ) (hB : 1 ≤ B) (hc : 2 ≤ c) :
    stonehamAlpha (B ^ (c ^ a)) c =
      (c : ℝ) ^ a * stonehamAlpha B c -
        ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / (B : ℝ) ^ (c ^ t) := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hBc : 1 ≤ B ^ (c ^ a) := one_le_pow₀ hB
      rw [show B ^ (c ^ (a + 1)) = (B ^ (c ^ a)) ^ c by
        rw [pow_succ, pow_mul]]
      rw [stonehamAlpha_pow_base (B ^ (c ^ a)) c hBc hc, ih]
      have hIcc : Icc 1 (a + 1) = insert (a + 1) (Icc 1 a) := by
        ext t
        simp only [mem_Icc, mem_insert]
        omega
      rw [hIcc, sum_insert (by simp)]
      simp only [Nat.sub_self, pow_zero]
      rw [mul_sub, pow_succ]
      have hsum :
          (c : ℝ) * ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / (B : ℝ) ^ (c ^ t) =
            ∑ t ∈ Icc 1 a,
              (c : ℝ) ^ (a + 1 - t) / (B : ℝ) ^ (c ^ t) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t ht
        have ht_le : t ≤ a := (mem_Icc.mp ht).2
        rw [show a + 1 - t = (a - t) + 1 by omega, pow_succ]
        ring
      rw [hsum]
      simp only [Nat.cast_pow]
      rw [show ((B : ℝ) ^ (c ^ a)) ^ c = (B : ℝ) ^ (c ^ (a + 1)) by
        rw [pow_succ, pow_mul]]
      ring

/-- Exponent form of the iterated shift, matching the parameters of `primeClassFamily`.
Thus a factor `(p^s)^a` in an exponent contributes the nonzero coefficient `p^(s*a)` and a
finite terminating correction. -/
theorem stonehamAlpha_exponent_mul_pow (b c u a : ℕ) (hb : 1 ≤ b) (hc : 2 ≤ c) :
    stonehamAlpha (b ^ (u * c ^ a)) c =
      (c : ℝ) ^ a * stonehamAlpha (b ^ u) c -
        ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / ((b : ℝ) ^ u) ^ (c ^ t) := by
  simpa only [pow_mul, Nat.cast_pow] using
    stonehamAlpha_pow_base_iterate (b ^ u) c a (one_le_pow₀ hb) hc

end NormalNumbers.StonehamPrimeClass
