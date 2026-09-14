/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleFar

/-!
# G4 §5: **`hbig`**, the medium-prime inequality

With `R = 2^{2^{m₁}}` and `Y = 2^{2^m}`, `⌊log₂ Y⌋/⌊log₂ R⌋ = 2^{m₂}`, so the dyadic Chebyshev
factor is `1 + m₂ log 2 ≤ 1 + 6K²`; the finite-sample term `2Y²(2^{−K}/3)²/|P|` is at most
`8^{−K}` because `|P| ≥ X/(2P₀)` and `Y²P₀/X ≤ 2^{−96·2^m}`; and `log Mx / log Y ≤ 101` since
`Mx = X + J·Dm ≤ 2X = Y^{100}·2`.  Altogether, with `K = 4k₄` and `η = 2^{−k₄}`,

    √(3K²·8^{−K}) + 34·2^{−K} ≤ 2K·2^{−6k₄} + 34·2^{−4k₄} ≤ (1/8)(1/K)2^{−k₄},

the last step being `512k₄² ≤ 2^{5k₄}` and `2176k₄ ≤ 2^{3k₄}`.  This is the lower edge of
the two-sided `K`-window: the medium-prime error is `8^{−K/2}√(log(Mc/5))`-sized and must beat
`εη = 2^{−K/4}/K`, which it does because `log(Mc/5) ≈ m₂ log 2 = O(K²)` — bounded in terms of
`K` alone, precisely because `X` was chosen after `K`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

lemma natLog_Y (K : ℕ) : Nat.log 2 (Y K) = 2 ^ m K := Nat.log_pow (by norm_num) _
lemma natLog_R (K : ℕ) : Nat.log 2 (R K) = 2 ^ m₁ K := Nat.log_pow (by norm_num) _

lemma m_sub_m₁ (K : ℕ) : m K - m₁ K = m₂ K := by unfold m; omega
lemma m₁_le_m (K : ℕ) : m₁ K ≤ m K := by unfold m; omega

/-- The dyadic factor: `1 + log ⌊log₂ Y⌋ − log ⌊log₂ R⌋ ≤ 1 + 6K²`. -/
lemma dyadic_factor_le (K : ℕ) :
    1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)) ≤ 1 + 6 * (K : ℝ) ^ 2 := by
  rw [natLog_Y, natLog_R]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  have h1 : ((m K : ℝ) - m₁ K) = m₂ K := by
    rw [← Nat.cast_sub (m₁_le_m K), m_sub_m₁]
  have h2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have h3 : (m₂ K : ℝ) = 8 * (K : ℝ) ^ 2 := by unfold m₂; push_cast; ring
  have h4 : (m K : ℝ) * Real.log 2 - m₁ K * Real.log 2 = 8 * (K : ℝ) ^ 2 * Real.log 2 := by
    rw [← sub_mul, h1, h3]
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg (K : ℝ)]

/-- `J·Dm ≤ X`. -/
lemma J_mul_gridDm_le_X {K : ℕ} (hK : 100 ≤ K) : J K * gridDm K (N K) ≤ X K := by
  have hJ : J K * gridDm K (N K) ≤ gridP₀Bound K (N K) := by
    unfold gridP₀Bound
    have hDm := gridDm_pos K (N K)
    have hT : 1 ≤ gridT K (N K) ^ 2 := by
      have := T_pos (K := K) (by omega)
      unfold T at this
      exact Nat.one_le_pow _ _ this
    have h1 : 1 ≤ gridDm K (N K) ^ (2 * gridH K) := Nat.one_le_pow _ _ hDm
    have h2 : 1 ≤ (2 * gridT K (N K) + 1) ^ (2 * gridT K (N K) + 1) := Nat.one_le_pow _ _ (by omega)
    have h3 : J K * gridDm K (N K) ≤ ((K + N K) * gridDm K (N K)) ^ (gridT K (N K) ^ 2) := by
      have : J K = K + N K := rfl
      rw [this]
      apply Nat.le_self_pow
      omega
    calc J K * gridDm K (N K) = 1 * 1 * (J K * gridDm K (N K)) := by ring
      _ ≤ _ := by gcongr
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
      have := gridDm_pos K (N K)
      have := gridDm_le_gridP₀Bound K (N K) (by omega)
      exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 := two_mul_exp_le_X hK
  have h4 : (J K * gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by exact_mod_cast hJ
  have : (J K * gridDm K (N K) : ℝ) ≤ X K := by
    have := Real.exp_pos (logP₀Nat K : ℝ)
    linarith
  exact_mod_cast this

/-- `P₀ ≤ 2^{2·2^m}`. -/
lemma P₀_le_two_pow {K : ℕ} (hK : 100 ≤ K) :
    ((gridOf K (N K) (by omega)).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m K) := by
  calc ((gridOf K (N K) (by omega)).P₀ : ℝ) ≤ Real.exp (logP₀Nat K) := P₀_le_exp (by omega)
    _ ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := exp_nat_le_two_pow _
    _ ≤ (2 : ℝ) ^ (2 * 2 ^ m K) :=
        pow_le_pow_right₀ (by norm_num) (by have := logP₀Nat_le_two_pow_m hK; omega)

/-- The finite-sample term: `2Y²(2^{−K}/3)²/|P| ≤ 8^{−K}`. -/
lemma sample_term_le {K : ℕ} (hK : 100 ≤ K) :
    2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
        / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)
      ≤ (1 / 8 : ℝ) ^ K := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X K := by unfold X; positivity
  have hcard := card_apSample_ge_half (X K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X hK)
  have hcard0 : (0 : ℝ) < (apSample (X K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hP₀2 := P₀_le_two_pow hK
  -- `Y² · P₀ / X ≤ 2^{−96·2^m}`
  have hY : (Y K : ℝ) ^ 2 = (2 : ℝ) ^ (2 * 2 ^ m K) := by unfold Y; push_cast; rw [← pow_mul]; ring_nf
  have hX : (X K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
  have hkey : (Y K : ℝ) ^ 2 * G.P₀ * 4 ≤ (X K : ℝ) * (1 / 2 : ℝ) ^ K := by
    have hpow : (2 : ℝ) ^ (2 * 2 ^ m K) * (2 : ℝ) ^ (2 * 2 ^ m K) * 4 * (2 : ℝ) ^ K
        ≤ (2 : ℝ) ^ (100 * 2 ^ m K) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : K ≤ 2 ^ m K := by
        calc K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
          _ ≤ m₁ K := m₁_ge_cube (by omega)
          _ ≤ m K := m₁_le_m K
          _ ≤ 2 ^ m K := (Nat.lt_two_pow_self).le
      have h2 : 2 ≤ 2 ^ m K := by
        calc 2 ≤ K := by omega
          _ ≤ 2 ^ m K := h1
      omega
    have hη : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
    rw [hY, hX, hη]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (2 * 2 ^ m K) * G.P₀ * 4 * 2 ^ K
        ≤ (2 : ℝ) ^ (2 * 2 ^ m K) * (2 : ℝ) ^ (2 * 2 ^ m K) * 4 * 2 ^ K := by gcongr
      _ ≤ _ := hpow
  have h8 : (1 / 8 : ℝ) ^ K = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 := by
    rw [show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]
    ring
  rw [div_le_iff₀ hcard0, h8]
  have hc : (X K : ℝ) / (2 * G.P₀) ≤ (apSample (X K) G.P₀ G.b₀).card := hcard
  have hη2 : (0 : ℝ) ≤ ((1 / 2 : ℝ) ^ K) ^ 2 := by positivity
  calc 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
      = ((1 / 2 : ℝ) ^ K) ^ 2 * (2 / 9 * (Y K : ℝ) ^ 2) := by ring
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * ((X K : ℝ) / (2 * G.P₀))) := by
        apply mul_le_mul_of_nonneg_left _ hη2
        have hY2 : (Y K : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ K * ((X K : ℝ) / (2 * G.P₀)) / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [hkey]
        nlinarith [sq_nonneg (Y K : ℝ), hY2]
    _ ≤ ((1 / 2 : ℝ) ^ K) ^ 2 * ((1 / 2 : ℝ) ^ K * (apSample (X K) G.P₀ G.b₀).card) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ K) ^ 2 * (apSample (X K) G.P₀ G.b₀).card := by ring

/-- `log Mx / log Y ≤ 101` for `Mx = X + J·Dm`. -/
lemma log_Mx_div_le {K : ℕ} (hK : 100 ≤ K) :
    Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K) ≤ 101 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogY : Real.log (Y K) = (2 : ℝ) ^ m K * Real.log 2 := by
    unfold Y; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hY0 : 0 < Real.log (Y K) := by rw [hlogY]; positivity
  rw [div_le_iff₀ hY0, hlogY]
  have hMx : ((X K + J K * gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m K + 1) := by
    have := J_mul_gridDm_le_X hK
    have hX : (X K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
    push_cast
    rw [pow_succ]
    have : (J K * gridDm K (N K) : ℝ) ≤ X K := by exact_mod_cast this
    linarith
  have hX0 : (0 : ℝ) < X K := by unfold X; positivity
  calc Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ)
      ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ m K + 1)) :=
        Real.log_le_log (by push_cast; positivity) hMx
    _ = (100 * 2 ^ m K + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ 101 * ((2 : ℝ) ^ m K * Real.log 2) := by
        push_cast
        have : (1 : ℝ) ≤ 2 ^ m K := one_le_pow₀ (by norm_num)
        nlinarith

/-- The two ℕ inequalities that close `hbig`. -/
lemma k₄_bounds {k₄ : ℕ} (hk : 25 ≤ k₄) : 512 * k₄ ^ 2 ≤ 2 ^ (5 * k₄) ∧ 2176 * k₄ ≤ 2 ^ (3 * k₄) := by
  have h1 : k₄ ≤ 2 ^ k₄ := (Nat.lt_two_pow_self).le
  constructor
  · calc 512 * k₄ ^ 2 ≤ 2 ^ 9 * (2 ^ k₄) ^ 2 := by gcongr <;> norm_num
      _ = 2 ^ (9 + 2 * k₄) := by ring
      _ ≤ 2 ^ (5 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2176 * k₄ ≤ 2 ^ 12 * 2 ^ k₄ := by gcongr; norm_num
      _ = 2 ^ (12 + k₄) := by rw [← pow_add]
      _ ≤ 2 ^ (3 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The `hbig` field of `ScheduleWitness`**, with `K = 4k₄`, `η = 2^{−k₄}`, `ε = 1/K`,
`δbig = 1/8`, `Mx = X + J·Dm`. -/
theorem hbig_holds {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K)) * (1 / 2 : ℝ) ^ K / 3
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
  -- the square root
  have hs1 := dyadic_factor_le K
  have hs2 := sample_term_le hK
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ))
      ≤ 2 * K * a ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15) ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by
      have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
      have : 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K))) ≤ 30 * (K : ℝ) ^ 2 := by
        nlinarith
      nlinarith
    have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)
        ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K + (1 / 8 : ℝ) ^ K := add_le_add hfac hs2
      _ ≤ 4 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by nlinarith
      _ = (2 * K * a ^ 6) ^ 2 := by rw [h8K]; ring
  -- the third term
  have ht3 : (Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K)) * (1 / 2 : ℝ) ^ K / 3
      ≤ 34 * a ^ 4 := by
    have := log_Mx_div_le hK
    have hl : 0 ≤ Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hX1 : (1 : ℝ) ≤ X K := by unfold X; exact_mod_cast Nat.one_le_two_pow
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (N K)) : (0 : ℝ) ≤ _)
        nlinarith
      · apply Real.log_nonneg; unfold Y; push_cast; exact one_le_pow₀ (by norm_num)
    rw [h2K]
    have ha4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  -- close: `2K a⁶ ≤ (1/16)(1/K) a` and `34 a⁴ ≤ (1/16)(1/K) a`
  have hc1 : 2 * K * a ^ 6 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (32 : ℝ) * K ^ 2 * a ^ 5 ≤ 1 := by
      have e : a ^ 5 = 1 / (2 : ℝ) ^ (5 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  have hc2 : 34 * a ^ 4 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (544 : ℝ) * K * a ^ 3 ≤ 1 := by
      have e : a ^ 3 = 1 / (2 : ℝ) ^ (3 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  calc _ ≤ 2 * K * a ^ 6 + 34 * a ^ 4 := add_le_add hsq ht3
    _ ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) + (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := add_le_add hc1 hc2
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

end Sched

end NormalNumbers.G4
