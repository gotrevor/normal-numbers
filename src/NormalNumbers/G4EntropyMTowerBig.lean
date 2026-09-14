/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMTower

/-!
# The marched ladder, step 1: **`hbig` and `hfar` at the marched parameters `(K, j)`**

`G4EntropyMTower` proved the arithmetic spine of the `m₁`-march and reduced the scale gap to the
single leaf `entropy_E1_march`.  This module discharges the first two of its three inputs: the
`hbig` and `hfar` fields of the witness, at `R ↦ Rm K j`, `Y ↦ Ym K j`, `X ↦ Xm K j`.

Both ports are exactly what the audit predicted:

* **`dyadic_factor_le_m` is `dyadic_factor_le` verbatim** — the dyadic Chebyshev factor is
  `1 + log(⌊log₂ Ym⌋/⌊log₂ Rm⌋) = 1 + m₂ K · log 2`, and `mm - mm₁ = m₂ K` *by definition of the
  march*.  Marching `m₁` does not move it at all.
* `sample_term_le_m` and `log_Mx_div_le_m` only **improve**: the first needs
  `Ym²·P₀·4·2^K ≤ Xm`, which is `4·2^{mm} + 2 + K ≤ 100·2^{mm}`, and the second is
  `log Mx / log Ym ≤ 101` because `Mx ≤ 2·Xm = 2·Ym^{100}` — a *constant*, which is why the A0
  ceiling (`G4EntropyXCeiling`: `X ≤ Y^{3·2^K δbig ε η}`, i.e. `Y^{2^{3K/4}}` at the implemented
  parameters) is never approached by the march.
* `farC_le_m` and `hfar_holds_m` are the `m ↦ mm K j` substitution, closed by
  `four_mul_le_four_pow_N_m`.

What remains for `entropy_E1_march` after this module is the small-prime side (the five
`smallPrimeBound` terms, which need `Mcm_le_two_pow_m₂` and a marched `R_pow_two_Mc_le`) and the
assembly.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

variable {K j : ℕ}

/-! ### Monotonicity of the marched outer scale -/

lemma m_le_mm (K j : ℕ) : m K ≤ mm K j := by show m K ≤ m K + j; omega

lemma X_le_Xm (K j : ℕ) : X K ≤ Xm K j :=
  Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul (le_refl 100) (Nat.pow_le_pow_right (by norm_num) (m_le_mm K j)))

lemma Xm_cast (K j : ℕ) : ((Xm K j : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mm K j) := by
  show (((2 : ℕ) ^ (100 * 2 ^ mm K j) : ℕ) : ℝ) = _
  push_cast; rfl

lemma Ym_cast (K j : ℕ) : ((Ym K j : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ mm K j) := by
  show (((2 : ℕ) ^ (2 ^ mm K j) : ℕ) : ℝ) = _
  push_cast; rfl

lemma one_le_Xm (K j : ℕ) : 1 ≤ Xm K j := Nat.one_le_two_pow

lemma two_mul_P₀_le_Xm (hK : 100 ≤ K) (j : ℕ) :
    2 * (gridOf K (N K) (by omega)).P₀ ≤ Xm K j :=
  le_trans (two_mul_P₀_le_X hK) (X_le_Xm K j)

lemma gridDm_le_Xm (hK : 100 ≤ K) (j : ℕ) : gridDm K (N K) ≤ Xm K j :=
  le_trans (gridDm_le_X hK) (X_le_Xm K j)

lemma J_mul_gridDm_le_Xm (hK : 100 ≤ K) (j : ℕ) : J K * gridDm K (N K) ≤ Xm K j :=
  le_trans (J_mul_gridDm_le_X hK) (X_le_Xm K j)

lemma sample_nonempty_m (hK : 100 ≤ K) (j : ℕ) :
    (apSample (Xm K j) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).Nonempty :=
  apSample_nonempty_of_le _ _ _ (gridOf K (N K) (by omega)).P₀_pos
    (gridOf K (N K) (by omega)).b₀_lt_P₀ (two_mul_P₀_le_Xm hK j)

/-- `K ≤ 2^{mm K j}`. -/
lemma K_le_two_pow_mm (hK : 100 ≤ K) (j : ℕ) : K ≤ 2 ^ mm K j := by
  calc K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
    _ ≤ m₁ K := m₁_ge_cube (by omega)
    _ ≤ m K := m₁_le_m K
    _ ≤ mm K j := m_le_mm K j
    _ ≤ 2 ^ mm K j := (Nat.lt_two_pow_self).le

lemma P₀_le_two_pow_m (hK : 100 ≤ K) (j : ℕ) :
    ((gridOf K (N K) (by omega)).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ mm K j) := by
  refine le_trans (P₀_le_two_pow hK) (pow_le_pow_right₀ (by norm_num) ?_)
  have : (2 : ℕ) ^ m K ≤ 2 ^ mm K j := Nat.pow_le_pow_right (by norm_num) (m_le_mm K j)
  omega

/-! ### `hbig` at the marched parameters -/

lemma natLog_Ym (K j : ℕ) : Nat.log 2 (Ym K j) = 2 ^ mm K j := Nat.log_pow (by norm_num) _
lemma natLog_Rm (K j : ℕ) : Nat.log 2 (Rm K j) = 2 ^ mm₁ K j := Nat.log_pow (by norm_num) _

/-- **The dyadic factor does not move.**  `1 + log ⌊log₂ Ym⌋ − log ⌊log₂ Rm⌋ ≤ 1 + 6K²`, because
`mm - mm₁ = m₂ K = 8K²` for every `j`. -/
lemma dyadic_factor_le_m (K j : ℕ) :
    1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)) ≤ 1 + 6 * (K : ℝ) ^ 2 := by
  rw [natLog_Ym, natLog_Rm]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  have h1 : ((mm K j : ℝ) - mm₁ K j) = m₂ K := by
    rw [← Nat.cast_sub (mm₁_le_mm K j), mm_sub_mm₁]
  have h2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have h3 : (m₂ K : ℝ) = 8 * (K : ℝ) ^ 2 := by show ((8 * K ^ 2 : ℕ) : ℝ) = _; push_cast; ring
  have h4 : (mm K j : ℝ) * Real.log 2 - mm₁ K j * Real.log 2 = 8 * (K : ℝ) ^ 2 * Real.log 2 := by
    rw [← sub_mul, h1, h3]
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg (K : ℝ)]

/-- The finite-sample term at the marched scale: `2·Ym²·(2^{−K}/3)²/|P| ≤ 8^{−K}`. -/
lemma sample_term_le_m (hK : 100 ≤ K) (j : ℕ) :
    2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
        / ((apSample (Xm K j) (gridOf K (N K) (by omega)).P₀
            (gridOf K (N K) (by omega)).b₀).card : ℝ)
      ≤ (1 / 8 : ℝ) ^ K := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < Xm K j := by rw [Xm_cast]; positivity
  have hcard := card_apSample_ge_half (Xm K j) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_Xm hK j)
  have hcard0 : (0 : ℝ) < (apSample (Xm K j) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (Xm K j : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hP₀2 := P₀_le_two_pow_m hK j
  have hY : (Ym K j : ℝ) ^ 2 = (2 : ℝ) ^ (2 * 2 ^ mm K j) := by
    rw [Ym_cast, ← pow_mul]; ring_nf
  have hX : (Xm K j : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mm K j) := Xm_cast K j
  have hkey : (Ym K j : ℝ) ^ 2 * G.P₀ * 4 ≤ (Xm K j : ℝ) * (1 / 2 : ℝ) ^ K := by
    have hpow : (2 : ℝ) ^ (2 * 2 ^ mm K j) * (2 : ℝ) ^ (2 * 2 ^ mm K j) * 4 * (2 : ℝ) ^ K
        ≤ (2 : ℝ) ^ (100 * 2 ^ mm K j) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : K ≤ 2 ^ mm K j := K_le_two_pow_mm hK j
      have h2 : 2 ≤ 2 ^ mm K j := by
        calc 2 ≤ K := by omega
          _ ≤ 2 ^ mm K j := h1
      omega
    have hη : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
    rw [hY, hX, hη]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (2 * 2 ^ mm K j) * G.P₀ * 4 * 2 ^ K
        ≤ (2 : ℝ) ^ (2 * 2 ^ mm K j) * (2 : ℝ) ^ (2 * 2 ^ mm K j) * 4 * 2 ^ K := by gcongr
      _ ≤ _ := hpow
  have h8 : (1 / 8 : ℝ) ^ K = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 := by
    rw [show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]
    ring
  rw [div_le_iff₀ hcard0, h8]
  have hc : (Xm K j : ℝ) / (2 * G.P₀) ≤ (apSample (Xm K j) G.P₀ G.b₀).card := hcard
  have hη2 : (0 : ℝ) ≤ ((1 / 2 : ℝ) ^ K) ^ 2 := by positivity
  calc 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
      = ((1 / 2 : ℝ) ^ K) ^ 2 * (2 / 9 * (Ym K j : ℝ) ^ 2) := by ring
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * ((Xm K j : ℝ) / (2 * G.P₀))) := by
        apply mul_le_mul_of_nonneg_left _ hη2
        have hY2 : (Ym K j : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ K * ((Xm K j : ℝ) / (2 * G.P₀)) / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [hkey]
        nlinarith [sq_nonneg (Ym K j : ℝ), hY2]
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * (apSample (Xm K j) G.P₀ G.b₀).card) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 * (apSample (Xm K j) G.P₀ G.b₀).card := by ring

/-- `log Mx / log Ym ≤ 101` for `Mx = Xm + J·Dm` — a **constant**, independent of the march.
This is the term that A0 (`G4EntropyXCeiling`) caps; the march never moves it. -/
lemma log_Mx_div_le_m (hK : 100 ≤ K) (j : ℕ) :
    Real.log ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j) ≤ 101 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogY : Real.log (Ym K j) = (2 : ℝ) ^ mm K j * Real.log 2 := by
    rw [Ym_cast, Real.log_pow]; push_cast; ring
  have hY0 : 0 < Real.log (Ym K j) := by rw [hlogY]; positivity
  rw [div_le_iff₀ hY0, hlogY]
  have hMx : ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mm K j + 1) := by
    have h := J_mul_gridDm_le_Xm hK j
    have hX := Xm_cast K j
    push_cast
    rw [pow_succ]
    have : (J K * gridDm K (N K) : ℝ) ≤ Xm K j := by exact_mod_cast h
    push_cast at hX ⊢
    linarith
  have hX0 : (0 : ℝ) < Xm K j := by rw [Xm_cast]; positivity
  calc Real.log ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ)
      ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ mm K j + 1)) :=
        Real.log_le_log (by push_cast; positivity) hMx
    _ = (100 * 2 ^ mm K j + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ 101 * ((2 : ℝ) ^ mm K j * Real.log 2) := by
        push_cast
        have : (1 : ℝ) ≤ 2 ^ mm K j := one_le_pow₀ (by norm_num)
        nlinarith

/-- **The `hbig` field at the marched parameters `(K, j)`.** -/
theorem hbig_holds_m {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) (j : ℕ) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (Xm K j) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j))
          * (1 / 2 : ℝ) ^ K / 3
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  obtain ⟨hb1, hb2⟩ := k₄_bounds hk
  have hb1r : (512 : ℝ) * k₄ ^ 2 ≤ 2 ^ (5 * k₄) := by exact_mod_cast hb1
  have hb2r : (2176 : ℝ) * k₄ ≤ 2 ^ (3 * k₄) := by exact_mod_cast hb2
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h8K : (1 / 8 : ℝ) ^ K = a ^ 12 := by
    rw [ha, ← pow_mul, hK4, show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]; ring_nf
  have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
  have hs1 := dyadic_factor_le_m K j
  have hs2 := sample_term_le_m hK j
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (Xm K j) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      ≤ 2 * K * a ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15) ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by
      have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
      have : 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          ≤ 30 * (K : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc 4 * (1 + Real.log (Nat.log 2 (Ym K j)) - Real.log (Nat.log 2 (Rm K j)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Ym K j : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (Xm K j) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ)
        ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K + (1 / 8 : ℝ) ^ K := add_le_add hfac hs2
      _ ≤ 4 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by nlinarith
      _ = (2 * K * a ^ 6) ^ 2 := by rw [h8K]; ring
  have ht3 : (Real.log ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j))
      * (1 / 2 : ℝ) ^ K / 3 ≤ 34 * a ^ 4 := by
    have hlm := log_Mx_div_le_m hK j
    have hl : 0 ≤ Real.log ((Xm K j + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Ym K j) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hX1 : (1 : ℝ) ≤ Xm K j := by rw [Xm_cast]; exact one_le_pow₀ (by norm_num)
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (N K)) : (0 : ℝ) ≤ _)
        push_cast at hX1
        nlinarith
      · apply Real.log_nonneg
        rw [Ym_cast]
        exact one_le_pow₀ (by norm_num)
    rw [h2K]
    have ha4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  -- close: `2K a⁶ ≤ (1/16)(1/K) a` and `34 a⁴ ≤ (1/16)(1/K) a`
  have hc1 : 2 * K * a ^ 6 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have h32 : (32 : ℝ) * K ^ 2 * a ^ 5 ≤ 1 := by
      have e : a ^ 5 = 1 / (2 : ℝ) ^ (5 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  have hc2 : 34 * a ^ 4 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have h544 : (544 : ℝ) * K * a ^ 3 ≤ 1 := by
      have e : a ^ 3 = 1 / (2 : ℝ) ^ (3 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  calc _ ≤ 2 * K * a ^ 6 + 34 * a ^ 4 := add_le_add hsq ht3
    _ ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) + (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := add_le_add hc1 hc2
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

/-! ### `hfar` at the marched parameters -/

/-- **`farC ≤ logP₀Nat K + mm K j + 10`** at the marched outer scale. -/
theorem farC_le_m (hK : 100 ≤ K) (j : ℕ) :
    farC (gridOf K (N K) (by omega)) (Xm K j) (gridDm K (N K))
      ≤ logP₀Nat K + mm K j + 10 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < Xm K j := by rw [Xm_cast]; positivity
  have hcard := card_apSample_ge_half (Xm K j) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_Xm hK j)
  have hcard0 : (0 : ℝ) < (apSample (Xm K j) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (Xm K j : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ Xm K j := by exact_mod_cast gridDm_le_Xm hK j
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  have hXeq : (Xm K j : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mm K j) := Xm_cast K j
  unfold farC
  have h1 : (((Xm K j + gridDm K (N K) : ℕ) : ℝ) / (apSample (Xm K j) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (Xm K j : ℝ) + gridDm K (N K) ≤ 2 * Xm K j := by linarith
      _ = 4 * G.P₀ * ((Xm K j : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (Xm K j) G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((Xm K j + gridDm K (N K) : ℕ) : ℝ)
      / (apSample (Xm K j) G.P₀ G.b₀).card) ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((Xm K j + gridDm K (N K) : ℕ) : ℝ)
        / (apSample (Xm K j) G.P₀ G.b₀).card := by push_cast; positivity
    calc Real.log (((Xm K j + gridDm K (N K) : ℕ) : ℝ)
            / (apSample (Xm K j) G.P₀ G.b₀).card)
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
  have h2 : Real.log (Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ mm K j + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlogX : Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (mm K j + 7) := by
      have hle : ((Xm K j + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mm K j + 1) := by
        push_cast
        rw [pow_succ]
        push_cast at hXeq
        linarith
      calc Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ)
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
    have hpos : (0 : ℝ) < Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ) := by
        apply Real.log_nonneg
        push_cast
        push_cast at hXeq
        have h1' : (1 : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mm K j) := one_le_pow₀ (by norm_num)
        have := (Nat.cast_nonneg (gridDm K (N K)) : (0 : ℝ) ≤ _)
        linarith
      linarith
    calc Real.log (Real.log ((Xm K j + gridDm K (N K) : ℕ) : ℝ) + 1)
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

/-- **The `hfar` field at the marched parameters**, against `η = 2^{−K}`. -/
theorem hfar_holds_m (hK : 100 ≤ K) (hj : j ≤ jstar K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) (Xm K j) (gridDm K (N K))
              + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by
  have hfarC := farC_le_m hK j
  have hfar0 := farC_nonneg (gridOf K (N K) (by omega)) (Xm K j) (sample_nonempty_m hK j)
    (gridDm K (N K))
  set C := farC (gridOf K (N K) (by omega)) (Xm K j) (gridDm K (N K)) with hC
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
  have e2 : (2 : ℝ) ^ K * (1 / 4 : ℝ) ^ K = (1 / 2 : ℝ) ^ K := by
    rw [← mul_pow]; norm_num
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

end Sched

end NormalNumbers.G4
