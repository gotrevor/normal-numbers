/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMTowerBudget

/-!
# The marched ladder, step 4: `hbig` and `hfar` **downward** inside the marched window

`G4EntropyMTowerBig` proved the `hbig`/`hfar` fields at the *top* of a marched window
(`X' = Xm K j`); `entropy_E1_march` needs them at every `X'` in the window
`[Xlom K j, Xm K j]`.  This module runs the same downward port that `G4EntropyE0Down` /
`G4EntropyE1Down` ran for the implemented schedule, at the marched parameters:

* `sample_term_le_down_m` — the finite-sample term, off the floor `Xlom K j = 2^{50·2^{mm}}`
  (the exponent count `96 → 46` of the `X`-version, at `mm` in place of `m`);
* `log_Mx_div_le_down_m` — monotone from `log_Mx_div_le_m` (`X' ≤ Xm K j`); the A0 obstruction
  term *improves* downward and stays the constant `≤ 101`;
* `farC_le_down_m`, `hfar_holds_down_m` — `farC G X' Dm ≤ logP₀Nat K + mm K j + 10`, closed by
  `four_mul_le_four_pow_N_m`;
* `hbig_small_down_m`, `hfar_small_down_m` — the E1 allowances `(1/2)^{k₄}·(1/K)·(1/2)^{k₄}`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

variable {K j : ℕ}

/-! ### The finite-sample term, downward -/

lemma sample_term_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hlo : Xlom K j ≤ X') :
    2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
        / ((apSample X' (gridOf K (N K) (by omega)).P₀
            (gridOf K (N K) (by omega)).b₀).card : ℝ)
      ≤ (1 / 8 : ℝ) ^ K := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hX'pos : 0 < X' := by have := Xlom_pos K j; omega
  have hXr : (0 : ℝ) < X' := by exact_mod_cast hX'pos
  have hXlo' : (2 : ℝ) ^ (50 * 2 ^ mm K j) ≤ (X' : ℝ) := by
    rw [← Xlom_cast K j]; exact_mod_cast hlo
  have hcard := card_apSample_ge_half X' G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (le_trans (two_mul_P₀_le_Xlom hK j) hlo)
  have hcard0 : (0 : ℝ) < (apSample X' G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X' : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hP₀2 := P₀_le_two_pow_m hK j
  have hY : (Ym K j : ℝ) ^ 2 = (2 : ℝ) ^ (2 * 2 ^ mm K j) := by
    rw [Ym_cast, ← pow_mul]; ring_nf
  have hkey : (Ym K j : ℝ) ^ 2 * G.P₀ * 4 ≤ (X' : ℝ) * (1 / 2 : ℝ) ^ K := by
    have hpow : (2 : ℝ) ^ (2 * 2 ^ mm K j) * (2 : ℝ) ^ (2 * 2 ^ mm K j) * 4 * (2 : ℝ) ^ K
        ≤ (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : K ≤ 2 ^ mm K j := K_le_two_pow_mm hK j
      have h2 : 2 ≤ 2 ^ mm K j := by
        calc 2 ≤ K := by omega
          _ ≤ 2 ^ mm K j := h1
      omega
    have hη : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
    rw [hY, hη, mul_one_div, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (2 * 2 ^ mm K j) * G.P₀ * 4 * 2 ^ K
        ≤ (2 : ℝ) ^ (2 * 2 ^ mm K j) * (2 : ℝ) ^ (2 * 2 ^ mm K j) * 4 * 2 ^ K := by gcongr
      _ ≤ (2 : ℝ) ^ (50 * 2 ^ mm K j) := hpow
      _ ≤ (X' : ℝ) := hXlo'
  have h8 : (1 / 8 : ℝ) ^ K = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 := by
    rw [show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]
    ring
  rw [div_le_iff₀ hcard0, h8]
  have hη2 : (0 : ℝ) ≤ ((1 / 2 : ℝ) ^ K) ^ 2 := by positivity
  calc 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
      = ((1 / 2 : ℝ) ^ K) ^ 2 * (2 / 9 * (Ym K j : ℝ) ^ 2) := by ring
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * ((X' : ℝ) / (2 * G.P₀))) := by
        apply mul_le_mul_of_nonneg_left _ hη2
        have hY2 : (Ym K j : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ K * ((X' : ℝ) / (2 * G.P₀)) / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [hkey]
        nlinarith [sq_nonneg (Ym K j : ℝ), hY2]
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * (apSample X' G.P₀ G.b₀).card) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 * (apSample X' G.P₀ G.b₀).card := by ring

/-- `log Mx' / log Ym ≤ 101` for `Mx' = X' + J·Dm`, `X' ≤ Xm K j`. -/
lemma log_Mx_div_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hlo : Xlom K j ≤ X')
    (hhi : X' ≤ Xm K j) :
    Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j) ≤ 101 := by
  refine le_trans ?_ (log_Mx_div_le_m hK j)
  have hY0 : 0 < Real.log (Ym K j) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (Ym K j : ℝ) := by
      rw [Ym_cast]
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 ^ mm K j) := pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow
    linarith
  have hX'pos : 0 < X' := by have := Xlom_pos K j; omega
  refine div_le_div_of_nonneg_right ?_ hY0.le
  refine Real.log_le_log ?_ ?_
  · have : (0 : ℝ) < (X' : ℝ) := by exact_mod_cast hX'pos
    push_cast
    positivity
  · exact_mod_cast Nat.add_le_add_right hhi _

/-! ### `hbig` at the E1 allowance, downward and marched -/

theorem hbig_small_down_m {K k₄ j X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlom K j ≤ X') (hhi : X' ≤ Xm K j) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample X' (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j))
          * (1 / 2 : ℝ) ^ K / 3
      ≤ (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h8K : (1 / 8 : ℝ) ^ K = a ^ 12 := by
    rw [ha, ← pow_mul, hK4, show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]; ring_nf
  have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
  have hs2 := sample_term_le_down_m hK hlo
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample X' (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      ≤ 2 * K * a ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15) ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by
      have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
      have hd := dyadic_factor_le_m K j
      have : 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          ≤ 30 * (K : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample X' (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ)
        ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K + (1 / 8 : ℝ) ^ K := add_le_add hfac hs2
      _ ≤ 4 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by nlinarith
      _ = (2 * K * a ^ 6) ^ 2 := by rw [h8K]; ring
  have ht3 : (Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j))
        * (1 / 2 : ℝ) ^ K / 3 ≤ 34 * a ^ 4 := by
    have := log_Mx_div_le_down_m hK hlo hhi
    have hl : 0 ≤ Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hXp : 0 < X' := by have := Xlom_pos K j; omega
        have hX1 : (1 : ℝ) ≤ X' := by exact_mod_cast hXp
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (N K)) : (0 : ℝ) ≤ _)
        nlinarith
      · apply Real.log_nonneg; rw [Ym_cast]; exact one_le_pow₀ (by norm_num)
    rw [h2K]
    have ha4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  have hc1 : 2 * K * a ^ 6 ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) := by
    have hnat : (64 : ℝ) * (k₄ : ℝ) ^ 2 ≤ (2 : ℝ) ^ (4 * k₄) := by exact_mod_cast big_aux1 hk
    have he : a ^ 4 = 1 / (2 : ℝ) ^ (4 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
    have hkey : (4 : ℝ) * K ^ 2 * a ^ 4 ≤ 1 := by
      rw [he, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) = a ^ 2 / (2 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0, pow_pos ha0 2]
  have hc2 : 34 * a ^ 4 ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) := by
    have hnat : (272 : ℝ) * (k₄ : ℝ) ≤ (2 : ℝ) ^ (2 * k₄) := by exact_mod_cast big_aux2 hk
    have he : a ^ 2 = 1 / (2 : ℝ) ^ (2 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
    have hkey : (68 : ℝ) * K * a ^ 2 ≤ 1 := by
      rw [he, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) = a ^ 2 / (2 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0, pow_pos ha0 2]
  calc _ ≤ 2 * K * a ^ 6 + 34 * a ^ 4 := add_le_add hsq ht3
    _ ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) + (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) :=
        add_le_add hc1 hc2
    _ = (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

/-! ### `hfar`, downward and marched -/

theorem farC_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hlo : Xlom K j ≤ X') (hhi : X' ≤ Xm K j) :
    farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) ≤ logP₀Nat K + mm K j + 10 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXlo := Xlom_pos K j
  have hX'pos : 0 < X' := by omega
  have hXr : (0 : ℝ) < X' := by exact_mod_cast hX'pos
  have hhiR : ((X' : ℕ) : ℝ) ≤ ((Xm K j : ℕ) : ℝ) := by exact_mod_cast hhi
  have hcard := card_apSample_ge_half X' G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (le_trans (two_mul_P₀_le_Xlom hK j) hlo)
  have hcard0 : (0 : ℝ) < (apSample X' G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X' : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ X' := by
    exact_mod_cast le_trans (le_trans (gridDm_le_Xlo hK) (Xlo_le_Xlom K j)) hlo
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  unfold farC
  have h1 : (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card) ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (X' : ℝ) + gridDm K (N K) ≤ 2 * (X' : ℝ) := by linarith
      _ = 4 * G.P₀ * ((X' : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample X' G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card)
        ≤ Real.log (4 * G.P₀) := Real.log_le_log hpos h1
      _ = Real.log 4 + Real.log G.P₀ := Real.log_mul (by norm_num) hP₀.ne'
      _ ≤ 2 + logP₀Nat K := by
          have ha : Real.log 4 ≤ 2 := by
            have h4 : (4 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (1 : ℝ)
              have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              rw [h2]; nlinarith [Real.exp_pos 1]
            calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h4
              _ = 2 := Real.log_exp 2
          have hb : Real.log G.P₀ ≤ logP₀Nat K := by
            calc Real.log G.P₀ ≤ Real.log (Real.exp (logP₀Nat K)) := Real.log_le_log hP₀ hP₀exp
              _ = logP₀Nat K := Real.log_exp _
          linarith
  have h2 : Real.log (Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ mm K j + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlogX : Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (mm K j + 7) := by
      have hle : ((X' + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mm K j + 1) := by
        push_cast
        have hXK : ((Xm K j : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mm K j) := Xm_cast K j
        have hDmXK : ((gridDm K (N K) : ℕ) : ℝ) ≤ ((Xm K j : ℕ) : ℝ) := by
          exact_mod_cast gridDm_le_Xm hK j
        rw [pow_succ]
        push_cast at hXK hDmXK hhiR
        linarith
      calc Real.log ((X' + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ mm K j + 1)) :=
            Real.log_le_log (by push_cast; positivity) hle
        _ = (100 * 2 ^ mm K j + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (100 * 2 ^ mm K j + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (100 * 2 ^ mm K j + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (mm K j + 7) := by
            have hN : 100 * 2 ^ mm K j + 1 ≤ 2 ^ (mm K j + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ mm K j := Nat.one_le_two_pow
              omega
            exact_mod_cast hN
    have hpos : (0 : ℝ) < Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) :=
        Real.log_nonneg (by
          push_cast
          have h1 : (1 : ℝ) ≤ (X' : ℝ) := by exact_mod_cast hX'pos
          linarith [(Nat.cast_nonneg (gridDm K (N K)) : (0:ℝ) ≤ ((gridDm K (N K) : ℕ) : ℝ))])
      linarith
    calc Real.log (Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (mm K j + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (mm K j + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (mm K j + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (mm K j + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (mm K j + 8 : ℕ) := by positivity
          nlinarith
      _ = mm K j + 8 := by push_cast; ring
  linarith

theorem hfar_holds_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K)
    (hlo : Xlom K j ≤ X') (hhi : X' ≤ Xm K j) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by
  have hfarC := farC_le_down_m hK hlo hhi
  have hne' : (apSample X' (gridOf K (N K) (by omega)).P₀
      (gridOf K (N K) (by omega)).b₀).Nonempty :=
    apSample_nonempty_of_le _ _ _ (gridOf K (N K) (by omega)).P₀_pos
      (gridOf K (N K) (by omega)).b₀_lt_P₀ (le_trans (two_mul_P₀_le_Xlom hK j) hlo)
  have hfar0 := farC_nonneg (gridOf K (N K) (by omega)) X' hne' (gridDm K (N K))
  set C := farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  set A : ℕ := logP₀Nat K + mm K j + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 ≤ (A : ℝ) / 3 := by
    have hJ : (J K : ℝ) = K + N K := by show ((K + N K : ℕ) : ℝ) = _; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hbr0 : 0 ≤ (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 := by positivity
  have hN := four_mul_le_four_pow_N_m hK hj
  have hNr : (4 : ℝ) * K * A ≤ (4 : ℝ) ^ N K := by exact_mod_cast hN
  have e1 : (1 / 4 : ℝ) ^ (K + N K) = (1 / 4 : ℝ) ^ K * (1 / 4 : ℝ) ^ N K := pow_add _ _ _
  have e2 : (2 : ℝ) ^ K * (1 / 4 : ℝ) ^ K = (1 / 2 : ℝ) ^ K := by rw [← mul_pow]; norm_num
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ N K := by positivity
  have hq : (1 / 4 : ℝ) ^ N K * (A : ℝ) ≤ 1 / (4 * K) := by
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h4pos (by positivity)]
    linarith
  have hη : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  calc (2 : ℝ) ^ K / Real.log 2
        * ((1 / 4 : ℝ) ^ (K + N K) * ((C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9))
      ≤ (2 : ℝ) ^ K / Real.log 2 * ((1 / 4 : ℝ) ^ (K + N K) * ((A : ℝ) / 3)) := by gcongr
    _ = (1 / 2 : ℝ) ^ K * ((1 / 4 : ℝ) ^ N K * A) / (3 * Real.log 2) := by
        rw [e1, ← e2]; field_simp
    _ ≤ (1 / 2 : ℝ) ^ K * (1 / (4 * K)) / 2 := by
        gcongr
        linarith
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by field_simp; ring

theorem hfar_small_down_m {K k₄ j X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hj : j ≤ jstar K) (hlo : Xlom K j ≤ X') (hhi : X' ≤ Xm K j) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have h := hfar_holds_down_m hK hj hlo hhi
  have hKpos : (0 : ℝ) < K := by
    have : (100 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
  rw [h2K] at h
  refine h.trans ?_
  have hrw : (1 / 8 : ℝ) * (1 / (K : ℝ) * a ^ 4) = a ^ 4 / (8 * K) := by field_simp
  have hrw2 : a * (1 / (K : ℝ) * a) = a ^ 2 / K := by field_simp
  rw [hrw, hrw2, div_le_div_iff₀ (by positivity) hKpos]
  have h42 : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
  nlinarith [pow_pos ha0 2, pow_pos ha0 4, ha0, ha1, hKpos, h42]

end Sched

end NormalNumbers.G4
