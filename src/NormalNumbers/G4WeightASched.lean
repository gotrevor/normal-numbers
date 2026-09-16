/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightAWitness
import NormalNumbers.G4SchedBEAssembly

/-!
# The schedule's `D`-side at a general bounded multiplier

A general bounded `a` multiplies the large-prime average by `Ca` (`bigAvgA_le'`) and the far
tail by `Ca` (`farAvgW_le_effC_smul`).  Against the *same* budget fields `δbig = 1/8`,
`δfar = 11/64`, both are paid by the schedule's own slack:

* the large-prime estimate is `2K·a⁴ + 51·a²` with `a = 2^{−k₄}` (`hbig_two_termsE`), while the
  target is `(1/8)·(1/K)·a` — a full factor `a⁻¹/K` of room, so `Ca ≤ 2^{k₄}/(10⁵k₄³)` suffices;
* the far tail already runs at a free constant `κ` with `κ ≤ 2^{k₄}` (`hfarC_holdsE`), so
  `Ca · effC ≤ Ca · C` is the same statement at `C ↦ Ca·C`.

Together with `hN_holdsA` (`G4WeightAWitness`) this is the whole quantitative cost of the
`a`-side: one condition `10⁵ · (Ca·C) · k₄³ ≤ 2^{k₄}` on the schedule's free parameter `k₄`,
which `exists_good_k₄_poly` supplies.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J)

/-- **`hbig` with the multiplier `Ca`.**  The large-prime average of the `a`-weighted count is
`Ca` copies of the subset one, and the schedule pays for them out of the gap between `a²` and
`(1/K)·a`. -/
theorem hbigA_holdsE {b K k₄ e Ca : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e)
    (hCa1 : 1 ≤ Ca) (hCa : 100000 * Ca * k₄ ^ 3 ≤ 2 ^ k₄) :
    (Ca : ℝ) * (Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e))
            - Real.log (Nat.log 2 (RE e))) * rowL2 b K
          + 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2
            / ((apSample (XE K e) (gridOf K (Sched.N K) h.hK1).P₀
                (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ))
      + (Real.log ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (YE K e))
          * rowL1 b K)
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  have hk25 : (25 : ℝ) ≤ (k₄ : ℝ) := by exact_mod_cast hk
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hA1 : (1 : ℝ) ≤ (Ca : ℝ) := by exact_mod_cast hCa1
  have hinv : (2 : ℝ) ^ k₄ * a = 1 := by
    rw [ha, one_div_pow]
    field_simp
  have hCaR : 100000 * (Ca : ℝ) * (k₄ : ℝ) ^ 3 ≤ (2 : ℝ) ^ k₄ := by exact_mod_cast hCa
  have hkey : 100000 * (Ca : ℝ) * (k₄ : ℝ) ^ 3 * a ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hCaR ha0.le
    rwa [hinv] at hm
  have ha3 : a ^ 3 ≤ a := by
    calc a ^ 3 ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
      _ = a := pow_one a
  have ha2 : a ^ 2 ≤ a := by
    calc a ^ 2 ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
      _ = a := pow_one a
  have hc1 : (Ca : ℝ) * (2 * (K : ℝ) * a ^ 4) ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have h32 : 32 * (Ca : ℝ) * (K : ℝ) ^ 2 * a ^ 3 ≤ 1 := by
      have h1 : (K : ℝ) ^ 2 = 16 * (k₄ : ℝ) ^ 2 := by rw [hKk]; ring
      calc 32 * (Ca : ℝ) * (K : ℝ) ^ 2 * a ^ 3
          = 512 * (Ca : ℝ) * (k₄ : ℝ) ^ 2 * a ^ 3 := by rw [h1]; ring
        _ ≤ 512 * (Ca : ℝ) * (k₄ : ℝ) ^ 2 * a :=
            mul_le_mul_of_nonneg_left ha3 (by positivity)
        _ ≤ 100000 * (Ca : ℝ) * (k₄ : ℝ) ^ 3 * a := by
            have hx : (0 : ℝ) ≤ (Ca : ℝ) * (k₄ : ℝ) ^ 2 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left
              (show (512 : ℝ) ≤ 100000 * (k₄ : ℝ) by linarith) hx, ha0.le]
        _ ≤ 1 := hkey
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h32 ha0.le]
  have hc2 : (Ca : ℝ) * (51 * a ^ 2) ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have h816 : 816 * (Ca : ℝ) * (K : ℝ) * a ≤ 1 := by
      calc 816 * (Ca : ℝ) * (K : ℝ) * a = 3264 * (Ca : ℝ) * (k₄ : ℝ) * a := by rw [hKk]; ring
        _ ≤ 100000 * (Ca : ℝ) * (k₄ : ℝ) ^ 3 * a := by
            have hx : (0 : ℝ) ≤ (Ca : ℝ) * (k₄ : ℝ) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left
              (show (3264 : ℝ) ≤ 100000 * (k₄ : ℝ) ^ 2 by nlinarith [hk25]) hx, ha0.le]
        _ ≤ 1 := hkey
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h816 ha0.le]
  have hterm := hbig_two_termsE hK4 h
  have hCa0 : (0 : ℝ) ≤ (Ca : ℝ) := by positivity
  calc (Ca : ℝ) * _
      ≤ (Ca : ℝ) * (2 * (K : ℝ) * a ^ 4 + 51 * a ^ 2) :=
        mul_le_mul_of_nonneg_left hterm hCa0
    _ = (Ca : ℝ) * (2 * (K : ℝ) * a ^ 4) + (Ca : ℝ) * (51 * a ^ 2) := by ring
    _ ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) + (1 / 16 : ℝ) * ((1 / K : ℝ) * a) :=
        add_le_add hc1 hc2
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

end SchedB

end NormalNumbers.G4
