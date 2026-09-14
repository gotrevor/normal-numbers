/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleParams
import NormalNumbers.G4ScheduleWitness

/-!
# G4 §5: the outer scales, the sample size, and **`hfar`**

The scales: `R = 2^{2^{m₁}}`, `Y = 2^{2^m}`, `X = Y^{100} = 2^{100·2^m}`.  With
`P₀ ≤ exp(logP₀Nat K) ≤ 2^{2^m}` the sample `{n < X : n ≡ b₀ (P₀)}` has at least
`X/(2P₀)` points (`card_apSample_ge_half`), and then the far-tail constant is

    farC ≤ logP₀Nat K + m + 10                       (`farC_le`)

(the first term is `log(4P₀)`, the second `log log(2X) ≤ m + 8`).  The `hfar` field of
`ScheduleWitness` then follows from the single ℕ inequality

    4K · (logP₀Nat K + m + 2J + 13) ≤ 4^N,   N = 100K²,        (`four_mul_le_four_pow_N`)

which holds on the ladder because the left side is `≤ K^{20K+20} ≤ 2^{20K²+20K}` while
`4^N = 2^{200K²}`.  The bound is proved against `η = 2^{−K}`, which is weaker than the
witness's `η = 2^{−K/4}`; `hfar_of_le` transports it.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

/-- `R = 2^{2^{m₁}}`. -/
def R (K : ℕ) : ℕ := 2 ^ (2 ^ m₁ K)
/-- `Y = 2^{2^m}`. -/
def Y (K : ℕ) : ℕ := 2 ^ (2 ^ m K)
/-- `X = 2^{100·2^m} = Y^{100}`. -/
def X (K : ℕ) : ℕ := 2 ^ (100 * 2 ^ m K)

lemma m₁_ge_cube {K : ℕ} (hK : 1 ≤ K) : K ^ 3 ≤ m₁ K := by
  refine le_trans ?_ (m₁_ge K)
  have h1 : 1 ≤ 8 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have h2 : K ^ 3 ≤ K ^ (2 * K + 1) := Nat.pow_le_pow_right hK (by omega)
  calc K ^ 3 = 1 * K ^ 3 := (one_mul _).symm
    _ ≤ 8 ^ K * K ^ (2 * K + 1) := Nat.mul_le_mul h1 h2

lemma logP₀Nat_le_two_pow {K : ℕ} (hK : 100 ≤ K) : logP₀Nat K ≤ 2 ^ (21 * K ^ 2) := by
  calc logP₀Nat K ≤ K ^ (20 * K + 17) := logP₀Nat_le hK
    _ ≤ 2 ^ (K * (20 * K + 17)) := pow_le_two_pow_mul _ _
    _ ≤ 2 ^ (21 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

lemma twentyone_sq_le_m {K : ℕ} (hK : 100 ≤ K) : 21 * K ^ 2 ≤ m K := by
  have h1 := m₁_ge_cube (by omega : 1 ≤ K)
  have h2 : 21 * K ^ 2 ≤ K ^ 3 := by
    calc 21 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
  unfold m
  omega

lemma logP₀Nat_le_two_pow_m {K : ℕ} (hK : 100 ≤ K) : logP₀Nat K ≤ 2 ^ m K :=
  (logP₀Nat_le_two_pow hK).trans (Nat.pow_le_pow_right (by norm_num) (twentyone_sq_le_m hK))

/-- `exp n ≤ 2^{2n}` for `n : ℕ`. -/
lemma exp_nat_le_two_pow (n : ℕ) : Real.exp n ≤ (2 : ℝ) ^ (2 * n) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc Real.exp n ≤ Real.exp ((2 * n : ℕ) * Real.log 2) := by
        apply Real.exp_le_exp.2
        push_cast
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ = Real.exp (Real.log 2) ^ (2 * n) := Real.exp_nat_mul _ _
    _ = (2 : ℝ) ^ (2 * n) := by rw [Real.exp_log (by norm_num)]

/-- `2·exp(logP₀Nat K) ≤ X`. -/
lemma two_mul_exp_le_X {K : ℕ} (hK : 100 ≤ K) :
    2 * Real.exp (logP₀Nat K) ≤ (X K : ℝ) := by
  have h1 := exp_nat_le_two_pow (logP₀Nat K)
  have h2 : 2 * logP₀Nat K + 1 ≤ 100 * 2 ^ m K := by
    have := logP₀Nat_le_two_pow_m hK
    have : 1 ≤ 2 ^ m K := Nat.one_le_two_pow
    omega
  have h3 : (2 : ℝ) ^ (2 * logP₀Nat K + 1) ≤ (2 : ℝ) ^ (100 * 2 ^ m K) :=
    pow_le_pow_right₀ (by norm_num) h2
  unfold X
  push_cast
  calc 2 * Real.exp (logP₀Nat K) ≤ 2 * (2 : ℝ) ^ (2 * logP₀Nat K) := by linarith
    _ = (2 : ℝ) ^ (2 * logP₀Nat K + 1) := by ring
    _ ≤ _ := h3

lemma two_mul_P₀_le_X {K : ℕ} (hK : 100 ≤ K) :
    2 * (gridOf K (N K) (by omega)).P₀ ≤ X K := by
  have h1 := P₀_le_exp (K := K) (by omega)
  have h2 := two_mul_exp_le_X hK
  exact_mod_cast (by linarith : (2 * (gridOf K (N K) (by omega)).P₀ : ℝ) ≤ X K)

lemma gridDm_le_gridP₀Bound (K N : ℕ) (hK : 1 ≤ K) : gridDm K N ≤ gridP₀Bound K N := by
  unfold gridP₀Bound
  have hDm := gridDm_pos K N
  have h1 : gridDm K N ≤ gridDm K N ^ (2 * gridH K) := by
    apply Nat.le_self_pow
    unfold gridH; positivity
  have h2 : 1 ≤ (2 * gridT K N + 1) ^ (2 * gridT K N + 1) := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ ((K + N) * gridDm K N) ^ (gridT K N ^ 2) := by
    apply Nat.one_le_pow
    have : 0 < K + N := by omega
    positivity
  calc gridDm K N ≤ gridDm K N ^ (2 * gridH K) * 1 * 1 := by rw [mul_one, mul_one]; exact h1
    _ ≤ _ := by gcongr

lemma gridDm_le_X {K : ℕ} (hK : 100 ≤ K) : gridDm K (N K) ≤ X K := by
  have h1 := gridDm_le_gridP₀Bound K (N K) (by omega)
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
      have := gridDm_pos K (N K)
      exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 := two_mul_exp_le_X hK
  have h4 : (gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by exact_mod_cast h1
  have : (gridDm K (N K) : ℝ) ≤ X K := by
    have := Real.exp_pos (logP₀Nat K : ℝ)
    linarith
  exact_mod_cast this

/-! ### The sample -/

/-- `X/(2P₀) ≤ |P|` as soon as `2P₀ ≤ X`. -/
lemma card_apSample_ge_half (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀) (hX : 2 * P₀ ≤ X) :
    (X : ℝ) / (2 * P₀) ≤ ((apSample X P₀ a).card : ℝ) := by
  have h := card_apSample_ge X P₀ a hP₀ ha
  have hP : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hX' : (2 : ℝ) * P₀ ≤ X := by exact_mod_cast hX
  have : (X : ℝ) / (2 * P₀) ≤ (X : ℝ) / P₀ - 1 := by
    rw [div_sub_one hP.ne', div_le_div_iff₀ (by positivity) hP]
    nlinarith
  linarith

lemma sample_nonempty {K : ℕ} (hK : 100 ≤ K) :
    (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).Nonempty :=
  apSample_nonempty_of_le _ _ _ (gridOf K (N K) (by omega)).P₀_pos
    (gridOf K (N K) (by omega)).b₀_lt_P₀ (two_mul_P₀_le_X hK)

/-! ### `farC` -/

/-- **`farC ≤ logP₀Nat K + m + 10`.** -/
theorem farC_le {K : ℕ} (hK : 100 ≤ K) :
    farC (gridOf K (N K) (by omega)) (X K) (gridDm K (N K)) ≤ logP₀Nat K + m K + 10 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X K := by unfold X; positivity
  have hcard := card_apSample_ge_half (X K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X hK)
  have hcard0 : (0 : ℝ) < (apSample (X K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ X K := by exact_mod_cast gridDm_le_X hK
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  unfold farC
  -- first term: `(X+Dm)/|P| ≤ 4P₀`
  have h1 : (((X K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X K) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (X K : ℝ) + gridDm K (N K) ≤ 2 * X K := by linarith
      _ = 4 * G.P₀ * ((X K : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (X K) G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((X K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X K) G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((X K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X K) G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((X K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X K) G.P₀ G.b₀).card)
        ≤ Real.log (4 * G.P₀) := Real.log_le_log hpos h1
      _ = Real.log 4 + Real.log G.P₀ := Real.log_mul (by norm_num) hP₀.ne'
      _ ≤ 2 + logP₀Nat K := by
          have ha : Real.log 4 ≤ 2 := by
            have : (4 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (1 : ℝ)
              have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              rw [h2]; nlinarith [Real.exp_pos 1]
            calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
              _ = 2 := Real.log_exp 2
          have hb : Real.log G.P₀ ≤ logP₀Nat K := by
            calc Real.log G.P₀ ≤ Real.log (Real.exp (logP₀Nat K)) := Real.log_le_log hP₀ hP₀exp
              _ = logP₀Nat K := Real.log_exp _
          linarith
  -- second term: `log(log(X+Dm)+1) ≤ m + 8`
  have h2 : Real.log (Real.log ((X K + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ m K + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogX : Real.log ((X K + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m K + 7) := by
      have hle : ((X K + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m K + 1) := by
        push_cast
        have : (X K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
        rw [pow_succ]
        linarith
      calc Real.log ((X K + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ m K + 1)) :=
            Real.log_le_log (by push_cast; positivity) hle
        _ = (100 * 2 ^ m K + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (100 * 2 ^ m K + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (100 * 2 ^ m K + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (m K + 7) := by
            have : 100 * 2 ^ m K + 1 ≤ 2 ^ (m K + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ m K := Nat.one_le_two_pow
              omega
            exact_mod_cast this
    have hpos : (0 : ℝ) < Real.log ((X K + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ Real.log ((X K + gridDm K (N K) : ℕ) : ℝ) :=
        Real.log_nonneg (by push_cast; unfold X; have : (1:ℝ) ≤ 2 ^ (100 * 2 ^ m K) := one_le_pow₀ (by norm_num); push_cast; linarith [(Nat.cast_nonneg (gridDm K (N K)) : (0:ℝ) ≤ _)])
      linarith
    calc Real.log (Real.log ((X K + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (m K + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (m K + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (m K + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (m K + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (m K + 8 : ℕ) := by positivity
          nlinarith
      _ = m K + 8 := by push_cast; ring
  linarith

/-! ### The ℕ inequality -/

lemma four_mul_le_four_pow_N {K : ℕ} (hK : 100 ≤ K) :
    4 * K * (logP₀Nat K + m K + 2 * J K + 13) ≤ 4 ^ N K := by
  have h1 := logP₀Nat_le hK
  have h2 := m_le hK
  have h3 := J_le hK
  have hK2 : 2 ≤ K := by omega
  have hA : logP₀Nat K + m K + 2 * J K + 13 ≤ K ^ (20 * K + 18) := by
    have a1 : m K ≤ K ^ (20 * K + 17) := h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have a2 : 2 * J K ≤ K ^ (20 * K + 17) := by
      have : K ^ 4 ≤ K ^ (20 * K + 16) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * K ^ (20 * K + 16) ≤ K ^ (20 * K + 17) := by
        calc 2 * K ^ (20 * K + 16) ≤ K * K ^ (20 * K + 16) := Nat.mul_le_mul_right _ (by omega)
          _ = K ^ (20 * K + 17) := by ring
      omega
    have a3 : 13 ≤ K ^ (20 * K + 17) := by
      calc 13 ≤ K := by omega
        _ ≤ K ^ (20 * K + 17) := Nat.le_self_pow (by omega) K
    have a4 : 4 * K ^ (20 * K + 17) ≤ K ^ (20 * K + 18) := by
      calc 4 * K ^ (20 * K + 17) ≤ K * K ^ (20 * K + 17) := Nat.mul_le_mul_right _ (by omega)
        _ = K ^ (20 * K + 18) := by ring
    omega
  have hB : 4 * K * K ^ (20 * K + 18) ≤ K ^ (20 * K + 20) := by
    calc 4 * K * K ^ (20 * K + 18) ≤ K * K * K ^ (20 * K + 18) := by gcongr; omega
      _ = K ^ (20 * K + 20) := by ring
  have hC : K ^ (20 * K + 20) ≤ 2 ^ (200 * K ^ 2) := by
    calc K ^ (20 * K + 20) ≤ 2 ^ (K * (20 * K + 20)) := pow_le_two_pow_mul _ _
      _ ≤ 2 ^ (200 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hD : (4 : ℕ) ^ N K = 2 ^ (200 * K ^ 2) := by
    unfold N
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  rw [hD]
  calc 4 * K * (logP₀Nat K + m K + 2 * J K + 13) ≤ 4 * K * K ^ (20 * K + 18) := by gcongr
    _ ≤ K ^ (20 * K + 20) := hB
    _ ≤ 2 ^ (200 * K ^ 2) := hC

/-! ### `hfar` -/

/-- **The `hfar` field, against `η = 2^{−K}`** (weaker than the witness's `η = 2^{−K/4}`). -/
theorem hfar_holds {K : ℕ} (hK : 100 ≤ K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) (X K) (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by
  have hfarC := farC_le hK
  have hfar0 := farC_nonneg (gridOf K (N K) (by omega)) (X K) (sample_nonempty hK) (gridDm K (N K))
  set C := farC (gridOf K (N K) (by omega)) (X K) (gridDm K (N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  -- the bracket is at most `A/3` with `A = logP₀Nat + m + 2J + 13`
  set A : ℕ := logP₀Nat K + m K + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 ≤ (A : ℝ) / 3 := by
    have hJ : (J K : ℝ) = K + N K := by unfold J; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hbr0 : 0 ≤ (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 := by positivity
  -- the ℕ inequality
  have hN := four_mul_le_four_pow_N hK
  have hNr : (4 : ℝ) * K * A ≤ (4 : ℝ) ^ N K := by exact_mod_cast hN
  -- assemble
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
