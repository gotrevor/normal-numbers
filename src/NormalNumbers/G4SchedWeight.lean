/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedOmega
import NormalNumbers.G4WeightWitness

/-!
# Size arithmetic for the `w_c` schedule

The two §4D fields of `ScheduleWitnessC` are the `Ω` ones times `C` (junk) and `max C 1` (far).
Both are paid for by a single hypothesis on the coefficient bound,

  `100000 · C · k₄³ ≤ 2^{k₄}`,

i.e. `C` may grow almost like `2^{k₄}` — and at `C = 1` this is exactly the `Ω` demand
`cube_le_two_pow` (`40 ≤ k₄`).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

namespace SchedB

open Sched (N J logP₀Nat)

variable {b K e : ℕ}

/-- **`hjunk` for `w_c`**: the `Ω` junk field with its factor `C`. -/
theorem hjunk_holdsCE {k₄ C : ℕ} (hK4 : K = 4 * k₄) (hk : 40 ≤ k₄)
    (hCk : 100000 * C * k₄ ^ 3 ≤ 2 ^ k₄) (h : HypE b K e) :
    ((C : ℝ) * junkShiftBound (gridOf K (N K) h.hK1).P₀ (XE K e) (J K * gridDm K (N K))
        / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀
              (gridOf K (N K) h.hK1).b₀).card : ℝ)) * rowL1 b K
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set G := gridOf K (N K) h.hK1 with hG
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    exact_mod_cast (sample_nonemptyE h).card_pos
  have hcard := Sched.card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_XE h)
  have hXpos : 0 < XE K e := by unfold XE; positivity
  have hV := junkShiftBound_div_le' (P₀ := G.P₀) (X := XE K e)
    (ρmax := J K * gridDm K (N K)) G.P₀_pos hXpos (J_mul_gridDm_le_XE h) hcard0 hcard
    (junk_size_holdsE h)
  have hlogω := log_card_primeFactors_P₀_leE h
  have hV' : junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) ≤ 5 + 30 * (K : ℝ) ^ 2 := by linarith
  have hV0 : (0 : ℝ) ≤ junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) :=
    div_nonneg (junkShiftBound_nonneg _ _ _) hcard0.le
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  have hVC : (C : ℝ) * junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) ≤ (C : ℝ) * (5 + 30 * (K : ℝ) ^ 2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hV' hC0
  have hVC0 : (0 : ℝ) ≤ (C : ℝ) * junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) := by
    rw [mul_div_assoc]; positivity
  have hL1 : rowL1 b K ≤ a ^ 2 / 2 := by
    have := rowL1_le_three hb K; have := two_thirds_pow_le (k₄ := k₄) hK4; linarith
  have hL10 : (0 : ℝ) ≤ rowL1 b K :=
    rowL1_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  have hk₄r : (40 : ℝ) ≤ k₄ := by exact_mod_cast hk
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  have hpow : (C : ℝ) * (20 * (K : ℝ) + 120 * (K : ℝ) ^ 3) * a ≤ 1 := by
    have hcr : (100000 : ℝ) * (C : ℝ) * (k₄ : ℝ) ^ 3 ≤ (2 : ℝ) ^ k₄ := by exact_mod_cast hCk
    have hae : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
    rw [hae, mul_one_div, div_le_one (by positivity), hKk]
    have hsq : (1600 : ℝ) ≤ (k₄ : ℝ) ^ 2 := by nlinarith [hk₄r]
    have hk3 : (k₄ : ℝ) ≤ (k₄ : ℝ) ^ 3 := by nlinarith [hk₄r, hsq]
    nlinarith [hcr, hk3, hk₄r, hC0]
  calc ((C : ℝ) * junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
        / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ)) * rowL1 b K
      ≤ ((C : ℝ) * (5 + 30 * (K : ℝ) ^ 2)) * (a ^ 2 / 2) :=
        mul_le_mul hVC hL1 hL10 (by positivity)
    _ = ((C : ℝ) * (20 * (K : ℝ) + 120 * (K : ℝ) ^ 3) * a) * (a / (8 * K)) := by
        have hKpos : (0 : ℝ) < K := by linarith
        field_simp
        ring
    _ ≤ 1 * (a / (8 * K)) := by
        have hKpos : (0 : ℝ) < K := by linarith
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
        have hKpos : (0 : ℝ) < K := by linarith
        field_simp

end SchedB

end NormalNumbers.G4
