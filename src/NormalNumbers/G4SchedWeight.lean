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

/-! ### The far field for `w_c`: the `Ω` far pieces with one spare factor `2^{-k₄}`

Each piece is the `Ω` one proved against a target smaller by `(1/2)^{k₄}`; the exponent slack
(the far tail decays like `2^{-50K²}`) pays for it with room to spare.  That spare factor is
what absorbs `κ = max C 1 ≤ 2^{k₄}`. -/

lemma half_pow_le_target'' {K k₄ D : ℕ} (hK : 100 ≤ K) (hD : 2 * k₄ + 2 * K ≤ D) :
    ((1 : ℝ) / 2) ^ D
      ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := by
  have hsplit : ((1 : ℝ) / 2) ^ D = (1 / 2 : ℝ) ^ k₄ * ((1 : ℝ) / 2) ^ (D - k₄) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_comm ((1 / 64 : ℝ) * _)]
  exact mul_le_mul_of_nonneg_left (half_pow_le_target' hK (by omega)) (by positivity)

theorem hfar_frozen_leSE {k₄ : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K * (((Ω (gridOf K (N K) h.hK1).P₀ : ℕ) : ℝ)
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  set G := gridOf K (N K) h.hK1 with hG
  have hΩ := cardFactors_P₀_leE h
  have hΩ0 : (0 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ) := by positivity
  -- the geometric factor
  have hg1 : (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
      ≤ (1 / 3 : ℝ) ^ (K + N K) := by
    have h1 : (1 / (b : ℝ)) ^ (K + N K + 1) ≤ (1 / 3 : ℝ) ^ (K + N K + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2 : (b : ℝ) / ((b : ℝ) - 1) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 : (0 : ℝ) < (1 / 3 : ℝ) ^ (K + N K + 1) := by positivity
    calc (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
        ≤ (1 / 3 : ℝ) ^ (K + N K + 1) * (3 / 2) := by
          have hb0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
            have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
            positivity
          exact mul_le_mul h1 h2 hb0 h3.le
      _ = (1 / 3 : ℝ) ^ (K + N K) * (1 / 2) := by rw [pow_succ]; ring
      _ ≤ (1 / 3 : ℝ) ^ (K + N K) := by nlinarith [(by positivity : (0:ℝ) < (1/3:ℝ) ^ (K + N K))]
  -- `2^K (1/3)^{K+N} ≤ (1/2)^{2k₄} (1/2)^{100K²}`
  have hNK : N K = 100 * K ^ 2 := rfl
  have hsplit : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
      ≤ ((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
    have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by
      rw [← mul_pow]; norm_num
    have hth : (2 / 3 : ℝ) ^ K ≤ ((1 / 2 : ℝ) ^ k₄) ^ 2 := two_thirds_pow_le hK4
    have hth' : (2 / 3 : ℝ) ^ K ≤ ((1 : ℝ) / 2) ^ (2 * k₄) := by
      rw [mul_comm, pow_mul]
      exact hth
    have hN3 : (1 / 3 : ℝ) ^ (N K) ≤ ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
      rw [hNK]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
        = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K) * (1 / 3 : ℝ) ^ (N K) := by rw [pow_add]; ring
      _ = (2 / 3 : ℝ) ^ K * (1 / 3 : ℝ) ^ (N K) := by rw [h23]
      _ ≤ ((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
          exact mul_le_mul hth' hN3 (by positivity) (by positivity)
  -- assemble
  have hfinal : ((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (21 * K ^ 2 + 1)
      = ((1 : ℝ) / 2) ^ (100 * K ^ 2 - (21 * K ^ 2 + 1)) :=
    half_pow_mul_two_pow (by nlinarith [hK, sq_nonneg K])
  have hD : 2 * k₄ + 2 * K ≤ 2 * k₄ + (100 * K ^ 2 - (21 * K ^ 2 + 1)) := by
    have hKsq : K * 100 ≤ K ^ 2 := by nlinarith [hK]
    have hKk : K = 4 * k₄ := hK4
    omega
  calc (2 : ℝ) ^ K * (((Ω G.P₀ : ℕ) : ℝ)
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ (2 : ℝ) ^ K * (((Ω G.P₀ : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (K + N K)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hΩ0) (by positivity)
    _ = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)) * ((Ω G.P₀ : ℕ) : ℝ) := by ring
    _ ≤ (((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2)) * (2 : ℝ) ^ (21 * K ^ 2 + 1) := by
        exact mul_le_mul hsplit hΩ hΩ0 (by positivity)
    _ = ((1 : ℝ) / 2) ^ (2 * k₄) * (((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (21 * K ^ 2 + 1)) := by
        ring
    _ = ((1 : ℝ) / 2) ^ (2 * k₄ + (100 * K ^ 2 - (21 * K ^ 2 + 1))) := by
        rw [hfinal, pow_add]
    _ ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := half_pow_le_target'' (by omega) hD


/-- The `junkA` far piece. -/
theorem hfar_junkA_leSE {k₄ : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K * ((junkA (gridOf K (N K) h.hK1).P₀ (XE K e)
          / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀
              (gridOf K (N K) h.hK1).b₀).card : ℝ))
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  set G := gridOf K (N K) h.hK1 with hG
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    exact_mod_cast (sample_nonemptyE h).card_pos
  have hcard := Sched.card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_XE h)
  have hXpos : 0 < XE K e := by unfold XE; positivity
  have hA := junkA_div_le (P₀ := G.P₀) (X := XE K e) G.P₀_pos hXpos hcard0 hcard
  have hlogω := log_card_primeFactors_P₀_leE h
  have hA' : junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ)
      ≤ (2 : ℝ) ^ (2 * K + 6) := by
    have h1 : junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ)
        ≤ 4 + 30 * (K : ℝ) ^ 2 := by linarith
    have hK2 : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      have : (K : ℕ) < 2 ^ K := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hpow : ((2 : ℝ) ^ K) ^ 2 = (2 : ℝ) ^ (2 * K) := by rw [← pow_mul, mul_comm]
    have h2 : (4 : ℝ) + 30 * (K : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * K + 6) := by
      have hsq : (K : ℝ) ^ 2 ≤ ((2 : ℝ) ^ K) ^ 2 := by nlinarith [hK2, hK0]
      rw [pow_add, ← hpow]
      nlinarith [hsq, (by positivity : (0:ℝ) < ((2:ℝ) ^ K) ^ 2)]
    linarith
  have hA0 : (0 : ℝ) ≤ junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) :=
    div_nonneg (junkA_nonneg _ _) hcard0.le
  have hg1 : (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
      ≤ (1 / 3 : ℝ) ^ (K + N K) := by
    have h1 : (1 / (b : ℝ)) ^ (K + N K + 1) ≤ (1 / 3 : ℝ) ^ (K + N K + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2 : (b : ℝ) / ((b : ℝ) - 1) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hb0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
      have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      positivity
    calc (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
        ≤ (1 / 3 : ℝ) ^ (K + N K + 1) * (3 / 2) :=
          mul_le_mul h1 h2 hb0 (by positivity)
      _ = (1 / 3 : ℝ) ^ (K + N K) * (1 / 2) := by rw [pow_succ]; ring
      _ ≤ (1 / 3 : ℝ) ^ (K + N K) := by nlinarith [(by positivity : (0:ℝ) < (1/3:ℝ) ^ (K + N K))]
  have hNK : N K = 100 * K ^ 2 := rfl
  have hsplit : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
      ≤ ((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
    have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by rw [← mul_pow]; norm_num
    have hth : (2 / 3 : ℝ) ^ K ≤ ((1 / 2 : ℝ) ^ k₄) ^ 2 := two_thirds_pow_le hK4
    have hth' : (2 / 3 : ℝ) ^ K ≤ ((1 : ℝ) / 2) ^ (2 * k₄) := by rw [mul_comm, pow_mul]; exact hth
    have hN3 : (1 / 3 : ℝ) ^ (N K) ≤ ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
      rw [hNK]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
        = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K) * (1 / 3 : ℝ) ^ (N K) := by rw [pow_add]; ring
      _ = (2 / 3 : ℝ) ^ K * (1 / 3 : ℝ) ^ (N K) := by rw [h23]
      _ ≤ _ := mul_le_mul hth' hN3 (by positivity) (by positivity)
  have hfinal : ((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (2 * K + 6)
      = ((1 : ℝ) / 2) ^ (100 * K ^ 2 - (2 * K + 6)) :=
    half_pow_mul_two_pow (by nlinarith [hK, sq_nonneg K])
  have hD : 2 * k₄ + 2 * K ≤ 2 * k₄ + (100 * K ^ 2 - (2 * K + 6)) := by
    have hKsq : K * 100 ≤ K ^ 2 := by nlinarith [hK]
    have hKk : K = 4 * k₄ := hK4
    omega
  calc (2 : ℝ) ^ K * ((junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ))
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ (2 : ℝ) ^ K * ((junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ))
          * (1 / 3 : ℝ) ^ (K + N K)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hA0) (by positivity)
    _ = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K))
          * (junkA G.P₀ (XE K e) / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ)) := by ring
    _ ≤ (((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2)) * (2 : ℝ) ^ (2 * K + 6) :=
        mul_le_mul hsplit hA' hA0 (by positivity)
    _ = ((1 : ℝ) / 2) ^ (2 * k₄) * (((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (2 * K + 6)) := by
        ring
    _ = ((1 : ℝ) / 2) ^ (2 * k₄ + (100 * K ^ 2 - (2 * K + 6))) := by rw [hfinal, pow_add]
    _ ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := half_pow_le_target'' (by omega) hD


/-- The `junkB` far piece — the one that needs base `≥ 3` (its ratio is `2/b`). -/
theorem hfar_junkB_leSE {k₄ : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K * ((junkB (XE K e) (gridDm K (N K))
          / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀
              (gridOf K (N K) h.hK1).b₀).card : ℝ))
        * ((2 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 2))))
      ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  set G := gridOf K (N K) h.hK1 with hG
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    exact_mod_cast (sample_nonemptyE h).card_pos
  have hcard := Sched.card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_XE h)
  have hXpos : 1 ≤ XE K e := Nat.one_le_two_pow
  have hB := junkB_div_le (P₀ := G.P₀) (X := XE K e) (Dm := gridDm K (N K)) G.P₀_pos hXpos
    (gridDm_le_XE h) hcard0 hcard (junk_size_holdsE' h)
  have hB0 : (0 : ℝ) ≤ junkB (XE K e) (gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) :=
    div_nonneg (junkB_nonneg _ _) hcard0.le
  -- the geometric factor at ratio `2/b ≤ 2/3`
  have hg2 : (2 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 2))
      ≤ (2 / 3 : ℝ) ^ (N K) * 3 := by
    have h1 : (2 / (b : ℝ)) ^ (K + N K + 1) ≤ (2 / 3 : ℝ) ^ (K + N K + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2 : (b : ℝ) / ((b : ℝ) - 2) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hb0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 2) := by
      have : (0 : ℝ) < (b : ℝ) - 2 := by linarith
      positivity
    have h3 : (2 / 3 : ℝ) ^ (K + N K + 1) ≤ (2 / 3 : ℝ) ^ (N K) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (2 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 2))
        ≤ (2 / 3 : ℝ) ^ (K + N K + 1) * 3 := mul_le_mul h1 h2 hb0 (by positivity)
      _ ≤ (2 / 3 : ℝ) ^ (N K) * 3 := by gcongr
  have hNK : N K = 100 * K ^ 2 := rfl
  have hN23 : (2 / 3 : ℝ) ^ (N K) ≤ ((1 : ℝ) / 2) ^ (50 * K ^ 2) := by
    rw [hNK, show 100 * K ^ 2 = 2 * (50 * K ^ 2) by ring, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) _
  have hK2 : (K : ℝ) ≤ (2 : ℝ) ^ K := by
    have : (K : ℕ) < 2 ^ K := Nat.lt_two_pow_self
    exact_mod_cast this.le
  have hfinal : ((1 : ℝ) / 2) ^ (50 * K ^ 2) * (2 : ℝ) ^ (K + 2)
      = ((1 : ℝ) / 2) ^ (50 * K ^ 2 - (K + 2)) :=
    half_pow_mul_two_pow (by nlinarith [hK, sq_nonneg K])
  have hD : 2 * k₄ + 2 * K ≤ 50 * K ^ 2 - (K + 2) := by
    have hKsq : K * 100 ≤ K ^ 2 := by nlinarith [hK]
    have hKk : K = 4 * k₄ := hK4
    omega
  calc (2 : ℝ) ^ K * ((junkB (XE K e) (gridDm K (N K))
        / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ))
        * ((2 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 2))))
      ≤ (2 : ℝ) ^ K * (1 * ((2 / 3 : ℝ) ^ (N K) * 3)) := by
        have hg20 : (0 : ℝ) ≤ (2 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 2)) := by
          have h2 : (0 : ℝ) < (b : ℝ) - 2 := by linarith
          positivity
        refine mul_le_mul_of_nonneg_left (mul_le_mul hB hg2 hg20 (by norm_num)) (by positivity)
    _ = ((2 : ℝ) ^ K * 3) * (2 / 3 : ℝ) ^ (N K) := by ring
    _ ≤ (2 : ℝ) ^ (K + 2) * ((1 : ℝ) / 2) ^ (50 * K ^ 2) := by
        refine mul_le_mul ?_ hN23 (by positivity) (by positivity)
        rw [pow_add]
        nlinarith [(by positivity : (0:ℝ) < (2:ℝ) ^ K)]
    _ = ((1 : ℝ) / 2) ^ (50 * K ^ 2 - (K + 2)) := by rw [mul_comm]; exact hfinal
    _ ≤ ((1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := half_pow_le_target'' (by omega) hD


/-! ### The `ω` far piece with the same spare factor -/

theorem hfar_holdsSE {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K / Real.log 2 * farBound b (K + N K) (farC (gridOf K (N K) h.hK1) (XE K e) (gridDm K (N K)))
      ≤ ((1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄)) * (1 / 2 : ℝ) ^ k₄ := by
  have hb := h.base.hb; have hK := h.base.hK
  have hfarC := farC_leE h
  have hfar0 := farC_nonneg (gridOf K (N K) h.hK1) (XE K e) (sample_nonemptyE h) (gridDm K (N K))
  set C := farC (gridOf K (N K) h.hK1) (XE K e) (gridDm K (N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha]
    calc (1 / 2 : ℝ) ^ k₄ ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  -- reduce to `b = 3`
  have hfb := farBound_le_three hb (K + N K) hfar0
  -- the bracket at `b = 3` is at most `A/2`
  set A : ℕ := logP₀Nat K + mE K e + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2 ≤ (A : ℝ) / 2 := by
    have hJ : (J K : ℝ) = K + N K := by unfold J; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hN := four_mul_le_two_pow_NE h
  have hNr : (4 : ℝ) * K * A ≤ (2 : ℝ) ^ N K := by exact_mod_cast hN
  have h3N : (2 : ℝ) ^ N K ≤ (3 : ℝ) ^ N K := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq : (1 / 3 : ℝ) ^ N K * (A : ℝ) ≤ (1 / (4 * K)) * a := by
    have hA' : (A : ℝ) ≤ (2 : ℝ) ^ N K / (4 * K) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hNr]
    have h23N : (2 / 3 : ℝ) ^ N K ≤ a := by
      have hNk : 2 * k₄ ≤ N K := by
        have : N K = 100 * K ^ 2 := rfl
        rw [this, hK4]
        nlinarith [Nat.zero_le k₄]
      calc (2 / 3 : ℝ) ^ N K ≤ (2 / 3 : ℝ) ^ (2 * k₄) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hNk
        _ = ((2 / 3 : ℝ) ^ 2) ^ k₄ := by rw [pow_mul]
        _ ≤ ((1 : ℝ) / 2) ^ k₄ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ = a := by rw [ha]
    calc (1 / 3 : ℝ) ^ N K * (A : ℝ)
        ≤ (1 / 3 : ℝ) ^ N K * ((2 : ℝ) ^ N K / (4 * K)) := by
          exact mul_le_mul_of_nonneg_left hA' (by positivity)
      _ = (2 / 3 : ℝ) ^ N K / (4 * K) := by
          rw [div_pow, div_pow, one_pow]
          ring
      _ ≤ a / (4 * K) := by gcongr
      _ = (1 / (4 * K)) * a := by ring
  have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by rw [← mul_pow]; norm_num
  have h23a := two_thirds_pow_le (k₄ := k₄) hK4
  have hA0 : (0 : ℝ) ≤ A := by positivity
  calc (2 : ℝ) ^ K / Real.log 2 * farBound b (K + N K) C
      ≤ (2 : ℝ) ^ K / Real.log 2 * farBound 3 (K + N K) C := by gcongr
    _ = (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + N K)
          * ((C + 2 * (K + N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2)) := by
        unfold farBound; push_cast; ring_nf
    _ ≤ (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + N K) * ((A : ℝ) / 2)) := by gcongr
    _ = (2 / 3 : ℝ) ^ K * ((1 / 3 : ℝ) ^ N K * A) / (2 * Real.log 2) := by
        rw [pow_add, ← h23]; field_simp
    _ ≤ a ^ 2 * ((1 / (4 * K)) * a) / (2 * (2 / 3)) := by
        gcongr
    _ = a ^ 3 * (3 / (16 * K)) := by field_simp; norm_num
    _ ≤ ((1 / 8 : ℝ) * ((1 / K : ℝ) * a)) * a := by
        have hKpos' : (0 : ℝ) < K := hKpos
        rw [show ((1 / 8 : ℝ) * ((1 / K : ℝ) * a)) * a = a ^ 2 * (1 / (8 * K)) by
          field_simp]
        have h3 : a ^ 3 * (3 / (16 * K)) = a ^ 2 * (3 * a / (16 * K)) := by ring
        rw [h3]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [ha1, ha0]



end SchedB

end NormalNumbers.G4
