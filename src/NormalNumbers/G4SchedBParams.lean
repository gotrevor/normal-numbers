/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleBudget
import NormalNumbers.G4ScheduleWitness

/-!
# G4B §5: the explicit schedule in `(b, K)` — parameters and sizes

Campaign G4B (`IsDisjunctive b (primeLambertAtBase b)` for `b ≥ 3`).  The base-four schedule
of `G4Schedule*` is reused verbatim wherever it is base-free (`N, J, W, H, T, logP₀Nat, m₂`,
the size ladder, `Dj`, the elementary `exp` bounds, the subset count).  The one quantity that
must change is the small-prime exponent: the base-`b` frequency seed is
`θ₀ = freqSeed b K = b^{−4}(2/b²)^K`, so the main budget term needs
`θ₀ · m₁ log 2 ≳ Kr`, and we take

    m₁ b K = 1000 · b^{2K+4} · K^{2K+1}          (base four: `1000 · 8^K · K^{2K+1}`).

Everything downstream (`m = m₁ + m₂`, `Mc = 10⁵·T·m₁`, `R = 2^{2^{m₁}}`, `Y = 2^{2^m}`,
`X = 2^{100·2^m}`) is then the same text.  The size ladder survives under the standing
hypothesis `2b² ≤ K` (`Hyp b K`), because then `b^{2K+4} ≤ (K/2)^{K+2}` and
`m₁ ≤ K^{3K+3}` exactly as before.  The row masses enter only through `rowL1 b K ≤ (2/3)^K/2`,
`rowL2 b K ≤ (2/9)^K/8` and `farBound b ≤ farBound 3` for `b ≥ 3`, i.e. the worst case is
`b = 3`, which is handled in `G4SchedBAssembly`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J W H T logP₀Nat m₂ Dj pow_le_two_pow_mul N_le J_le gridB_le gridUmax_le W_le H_le
  T_le H_pos T_pos H_le_T r_le_H logP₀Nat_le log_nat_le log_gridP₀Bound_le P₀_le_exp
  logP₀Nat_le_two_pow exp_nat_le_two_pow gridDm_le_gridP₀Bound card_apSample_ge_half
  omega_mul_log_two_le sum_inv_excluded_le card_small_subsets_le card_smallPrimes_le
  exp_one_le two_le_exp_one exp_four_ge exp_neg_four_le exp_thirteen_half_le
  four_e_div_thirteen_le six_sevenths_pow_le prod_one_add_le_exp_sum two_pow_le_exp
  jackson_term_le two_Dj_add_one_le Lambda_le budget_assembly k₄_bounds N_pos T_eq)

/-- The standing hypotheses of the base-`b` schedule: `b ≥ 3`, `2b² ≤ K`, `K ≥ 100`. -/
structure Hyp (b K : ℕ) : Prop where
  hb : 3 ≤ b
  hbK : 2 * b ^ 2 ≤ K
  hK : 100 ≤ K

lemma Hyp.hK1 {b K : ℕ} (h : Hyp b K) : 1 ≤ K := by have := h.hK; omega

/-- `m₁ = 1000 · b^{2K+4} · K^{2K+1}`: `log₂ log₂ R`. -/
def m₁ (b K : ℕ) : ℕ := 1000 * b ^ (2 * K + 4) * K ^ (2 * K + 1)
/-- `m = m₁ + m₂`. -/
def m (b K : ℕ) : ℕ := m₁ b K + m₂ K
/-- The moment order `Mc = 10⁵·T·m₁`. -/
def Mc (b K : ℕ) : ℕ := 100000 * T K * m₁ b K
/-- `R = 2^{2^{m₁}}`. -/
def R (b K : ℕ) : ℕ := 2 ^ (2 ^ m₁ b K)
/-- `Y = 2^{2^m}`. -/
def Y (b K : ℕ) : ℕ := 2 ^ (2 ^ m b K)
/-- `X = 2^{100·2^m} = Y^{100}`. -/
def X (b K : ℕ) : ℕ := 2 ^ (100 * 2 ^ m b K)

variable {b : ℕ}

/-! ### `m₁` in the ladder -/

lemma m₁_le {b K : ℕ} (h : Hyp b K) : m₁ b K ≤ K ^ (3 * K + 3) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  unfold m₁
  have hb2 : b ^ 2 * 2 ≤ K := by omega
  have h1 : b ^ (2 * K + 4) * 2 ^ (K + 2) ≤ K ^ (K + 2) := by
    calc b ^ (2 * K + 4) * 2 ^ (K + 2) = (b ^ 2 * 2) ^ (K + 2) := by
          rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ K ^ (K + 2) := Nat.pow_le_pow_left hb2 _
  have h2 : 1000 ≤ 2 ^ (K + 2) := by
    calc 1000 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 1000 * b ^ (2 * K + 4) * K ^ (2 * K + 1)
      ≤ 2 ^ (K + 2) * b ^ (2 * K + 4) * K ^ (2 * K + 1) := by gcongr
    _ = (b ^ (2 * K + 4) * 2 ^ (K + 2)) * K ^ (2 * K + 1) := by ring
    _ ≤ K ^ (K + 2) * K ^ (2 * K + 1) := by gcongr
    _ = K ^ (3 * K + 3) := by rw [← pow_add]; ring_nf

lemma eight_pow_le {b K : ℕ} (hb : 3 ≤ b) : 8 ^ K ≤ b ^ (2 * K + 4) := by
  calc 8 ^ K ≤ 9 ^ K := Nat.pow_le_pow_left (by norm_num) K
    _ = (3 ^ 2) ^ K := by norm_num
    _ ≤ (b ^ 2) ^ K := Nat.pow_le_pow_left (Nat.pow_le_pow_left hb 2) K
    _ = b ^ (2 * K) := by rw [← pow_mul]
    _ ≤ b ^ (2 * K + 4) := Nat.pow_le_pow_right (by omega) (by omega)

lemma m₁_ge {b K : ℕ} (hb : 3 ≤ b) : 8 ^ K * K ^ (2 * K + 1) ≤ m₁ b K := by
  unfold m₁
  have h1 := eight_pow_le (K := K) hb
  calc 8 ^ K * K ^ (2 * K + 1) ≤ b ^ (2 * K + 4) * K ^ (2 * K + 1) := by gcongr
    _ = 1 * (b ^ (2 * K + 4) * K ^ (2 * K + 1)) := by ring
    _ ≤ 1000 * (b ^ (2 * K + 4) * K ^ (2 * K + 1)) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 1000 * b ^ (2 * K + 4) * K ^ (2 * K + 1) := by ring

lemma m_le {b K : ℕ} (h : Hyp b K) : m b K ≤ K ^ (3 * K + 4) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  unfold m m₂
  have h1 := m₁_le h
  have h2 : 8 * K ^ 2 ≤ K ^ (3 * K + 3) := by
    calc 8 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
      _ ≤ K ^ (3 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * K ^ (3 * K + 3) ≤ K ^ (3 * K + 4) := by
    calc 2 * K ^ (3 * K + 3) ≤ K * K ^ (3 * K + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ (3 * K + 4) := by ring
  omega

lemma Mc_le {b K : ℕ} (h : Hyp b K) : Mc b K ≤ K ^ (6 * K + 9) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  unfold Mc
  have h1 : 100000 ≤ K ^ 3 := by
    calc 100000 ≤ 100 ^ 3 := by norm_num
      _ ≤ K ^ 3 := Nat.pow_le_pow_left hK 3
  calc 100000 * T K * m₁ b K ≤ K ^ 3 * K ^ (3 * K + 3) * K ^ (3 * K + 3) := by
        gcongr
        · exact T_le hK
        · exact m₁_le h
    _ = K ^ (6 * K + 9) := by rw [← pow_add, ← pow_add]; ring_nf

lemma Mc_pos {b K : ℕ} (hb : 1 ≤ b) (hK : 1 ≤ K) : 0 < Mc b K := by
  unfold Mc m₁
  have := T_pos hK
  positivity

lemma m₁_ge_cube {b K : ℕ} (hb : 3 ≤ b) (hK : 1 ≤ K) : K ^ 3 ≤ m₁ b K := by
  refine le_trans ?_ (m₁_ge hb)
  have h1 : 1 ≤ 8 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have h2 : K ^ 3 ≤ K ^ (2 * K + 1) := Nat.pow_le_pow_right hK (by omega)
  calc K ^ 3 = 1 * K ^ 3 := (one_mul _).symm
    _ ≤ 8 ^ K * K ^ (2 * K + 1) := Nat.mul_le_mul h1 h2

lemma twentyone_sq_le_m {b K : ℕ} (h : Hyp b K) : 21 * K ^ 2 ≤ m b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have h1 := m₁_ge_cube hb (by omega : 1 ≤ K)
  have h2 : 21 * K ^ 2 ≤ K ^ 3 := by
    calc 21 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
  unfold m
  omega

lemma logP₀Nat_le_two_pow_m {b K : ℕ} (h : Hyp b K) : logP₀Nat K ≤ 2 ^ m b K :=
  (logP₀Nat_le_two_pow h.hK).trans (Nat.pow_le_pow_right (by norm_num) (twentyone_sq_le_m h))

lemma two_mul_exp_le_X {b K : ℕ} (h : Hyp b K) :
    2 * Real.exp (logP₀Nat K) ≤ (X b K : ℝ) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have h1 := exp_nat_le_two_pow (logP₀Nat K)
  have h2 : 2 * logP₀Nat K + 1 ≤ 100 * 2 ^ m b K := by
    have := logP₀Nat_le_two_pow_m h
    have : 1 ≤ 2 ^ m b K := Nat.one_le_two_pow
    omega
  have h3 : (2 : ℝ) ^ (2 * logP₀Nat K + 1) ≤ (2 : ℝ) ^ (100 * 2 ^ m b K) :=
    pow_le_pow_right₀ (by norm_num) h2
  unfold X
  push_cast
  calc 2 * Real.exp (logP₀Nat K) ≤ 2 * (2 : ℝ) ^ (2 * logP₀Nat K) := by linarith
    _ = (2 : ℝ) ^ (2 * logP₀Nat K + 1) := by ring
    _ ≤ _ := h3

lemma two_mul_P₀_le_X {b K : ℕ} (h : Hyp b K) :
    2 * (gridOf K (N K) h.hK1).P₀ ≤ X b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have h1 := P₀_le_exp (K := K) (by omega)
  have h2 := two_mul_exp_le_X h
  exact_mod_cast (by linarith : (2 * (gridOf K (N K) h.hK1).P₀ : ℝ) ≤ X b K)

lemma gridDm_le_X {b K : ℕ} (h : Hyp b K) : gridDm K (N K) ≤ X b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have h1 := gridDm_le_gridP₀Bound K (N K) (by omega)
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
      have := gridDm_pos K (N K)
      exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 := two_mul_exp_le_X h
  have h4 : (gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by exact_mod_cast h1
  have : (gridDm K (N K) : ℝ) ≤ X b K := by
    have := Real.exp_pos (logP₀Nat K : ℝ)
    linarith
  exact_mod_cast this

/-! ### The sample -/

lemma sample_nonempty {b K : ℕ} (h : Hyp b K) :
    (apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).Nonempty :=
  apSample_nonempty_of_le _ _ _ (gridOf K (N K) h.hK1).P₀_pos
    (gridOf K (N K) h.hK1).b₀_lt_P₀ (two_mul_P₀_le_X h)

/-! ### `farC` -/

theorem farC_le {b K : ℕ} (h : Hyp b K) :
    farC (gridOf K (N K) h.hK1) (X b K) (gridDm K (N K)) ≤ logP₀Nat K + m b K + 10 := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X b K := by unfold X; positivity
  have hcard := card_apSample_ge_half (X b K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X h)
  have hcard0 : (0 : ℝ) < (apSample (X b K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X b K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ X b K := by exact_mod_cast gridDm_le_X h
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  unfold farC
  -- first term: `(X+Dm)/|P| ≤ 4P₀`
  have h1 : (((X b K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X b K) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (X b K : ℝ) + gridDm K (N K) ≤ 2 * X b K := by linarith
      _ = 4 * G.P₀ * ((X b K : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (X b K) G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((X b K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X b K) G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((X b K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X b K) G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((X b K + gridDm K (N K) : ℕ) : ℝ) / (apSample (X b K) G.P₀ G.b₀).card)
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
  have h2 : Real.log (Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ m b K + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogX : Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m b K + 7) := by
      have hle : ((X b K + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m b K + 1) := by
        push_cast
        have : (X b K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m b K) := by unfold X; push_cast; rfl
        rw [pow_succ]
        linarith
      calc Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ m b K + 1)) :=
            Real.log_le_log (by push_cast; positivity) hle
        _ = (100 * 2 ^ m b K + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (100 * 2 ^ m b K + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (100 * 2 ^ m b K + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (m b K + 7) := by
            have : 100 * 2 ^ m b K + 1 ≤ 2 ^ (m b K + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ m b K := Nat.one_le_two_pow
              omega
            exact_mod_cast this
    have hpos : (0 : ℝ) < Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ) :=
        Real.log_nonneg (by push_cast; unfold X; have : (1:ℝ) ≤ 2 ^ (100 * 2 ^ m b K) := one_le_pow₀ (by norm_num); push_cast; linarith [(Nat.cast_nonneg (gridDm K (N K)) : (0:ℝ) ≤ _)])
      linarith
    calc Real.log (Real.log ((X b K + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (m b K + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (m b K + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (m b K + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (m b K + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (m b K + 8 : ℕ) := by positivity
          nlinarith
      _ = m b K + 8 := by push_cast; ring
  linarith

/-! ### The ℕ inequality -/

lemma natLog_Y (b K : ℕ) : Nat.log 2 (Y b K) = 2 ^ m b K := Nat.log_pow (by norm_num) _

lemma natLog_R (b K : ℕ) : Nat.log 2 (R b K) = 2 ^ m₁ b K := Nat.log_pow (by norm_num) _

lemma m_sub_m₁ (b K : ℕ) : m b K - m₁ b K = m₂ K := by unfold m; omega

lemma m₁_le_m (b K : ℕ) : m₁ b K ≤ m b K := by unfold m; omega

lemma dyadic_factor_le (b K : ℕ) :
    1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K)) ≤ 1 + 6 * (K : ℝ) ^ 2 := by
  rw [natLog_Y, natLog_R]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  have h1 : ((m b K : ℝ) - m₁ b K) = m₂ K := by
    rw [← Nat.cast_sub (m₁_le_m b K), m_sub_m₁]
  have h2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have h3 : (m₂ K : ℝ) = 8 * (K : ℝ) ^ 2 := by unfold m₂; push_cast; ring
  have h4 : (m b K : ℝ) * Real.log 2 - m₁ b K * Real.log 2 = 8 * (K : ℝ) ^ 2 * Real.log 2 := by
    rw [← sub_mul, h1, h3]
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg (K : ℝ)]

lemma J_mul_gridDm_le_X {b K : ℕ} (h : Hyp b K) : J K * gridDm K (N K) ≤ X b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
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
  have h3 := two_mul_exp_le_X h
  have h4 : (J K * gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by exact_mod_cast hJ
  have : (J K * gridDm K (N K) : ℝ) ≤ X b K := by
    have := Real.exp_pos (logP₀Nat K : ℝ)
    linarith
  exact_mod_cast this

lemma P₀_le_two_pow {b K : ℕ} (h : Hyp b K) :
    ((gridOf K (N K) h.hK1).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m b K) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  calc ((gridOf K (N K) h.hK1).P₀ : ℝ) ≤ Real.exp (logP₀Nat K) := P₀_le_exp (by omega)
    _ ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := exp_nat_le_two_pow _
    _ ≤ (2 : ℝ) ^ (2 * 2 ^ m b K) :=
        pow_le_pow_right₀ (by norm_num) (by have := logP₀Nat_le_two_pow_m h; omega)

lemma log_Mx_div_le {b K : ℕ} (h : Hyp b K) :
    Real.log ((X b K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y b K) ≤ 101 := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogY : Real.log (Y b K) = (2 : ℝ) ^ m b K * Real.log 2 := by
    unfold Y; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hY0 : 0 < Real.log (Y b K) := by rw [hlogY]; positivity
  rw [div_le_iff₀ hY0, hlogY]
  have hMx : ((X b K + J K * gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m b K + 1) := by
    have := J_mul_gridDm_le_X h
    have hX : (X b K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m b K) := by unfold X; push_cast; rfl
    push_cast
    rw [pow_succ]
    have : (J K * gridDm K (N K) : ℝ) ≤ X b K := by exact_mod_cast this
    linarith
  have hX0 : (0 : ℝ) < X b K := by unfold X; positivity
  calc Real.log ((X b K + J K * gridDm K (N K) : ℕ) : ℝ)
      ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ m b K + 1)) :=
        Real.log_le_log (by push_cast; positivity) hMx
    _ = (100 * 2 ^ m b K + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ 101 * ((2 : ℝ) ^ m b K * Real.log 2) := by
        push_cast
        have : (1 : ℝ) ≤ 2 ^ m b K := one_le_pow₀ (by norm_num)
        nlinarith

lemma log_R (b K : ℕ) : Real.log (R b K) = (2 : ℝ) ^ m₁ b K * Real.log 2 := by
  unfold R; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

lemma log_log_R_ge (b K : ℕ) : (m₁ b K : ℝ) * Real.log 2 - 1 ≤ Real.log (Real.log (R b K)) := by
  rw [log_R, Real.log_mul (by positivity) (Real.log_pos (by norm_num)).ne', Real.log_pow]
  have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h2 : Real.log (1 / 2) ≤ Real.log (Real.log 2) := by
    apply Real.log_le_log (by norm_num)
    linarith [Real.log_two_gt_d9]
  have h3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  linarith

theorem sum_inv_smallPrimes_ge {b K : ℕ} (h : Hyp b K) :
    (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ R b K := by
    unfold R
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ m₁ b K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  -- lower Mertens at `R + 1`
  have hM := log_log_le_sum_inv_primesBelow (R b K + 1) (by omega)
  have hRr : (2 : ℝ) ≤ R b K := by exact_mod_cast hR2
  have hlogR : 0 < Real.log (R b K) := Real.log_pos (by linarith)
  have hmono : Real.log (Real.log (R b K)) ≤ Real.log (Real.log ((R b K + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log hlogR
    apply Real.log_le_log (by linarith)
    push_cast; linarith
  have hlow := log_log_R_ge b K
  -- split the primes below `R+1` by `p ∣ P₀`
  have hsplit := Finset.sum_filter_add_sum_filter_not ((R b K + 1).primesBelow)
    (fun p => p ∣ G.P₀) (fun p => (p : ℝ)⁻¹)
  have hexcl := sum_inv_excluded_le hK (R b K)
  unfold smallPrimes
  linarith

/-! ### The upper bound -/

theorem sum_inv_smallPrimes_le {b K : ℕ} (h : Hyp b K) :
    ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ ≤ 3 * m₁ b K + 5 := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ R b K := by
    unfold R
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ m₁ b K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hsub : smallPrimes (R b K) G.P₀ ⊆ (R b K + 1).primesBelow := Finset.filter_subset _ _
  have h1 : ∑ p ∈ smallPrimes (R b K) G.P₀, (p : ℝ)⁻¹ ≤ ∑ p ∈ (R b K + 1).primesBelow, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hsplit : ∑ p ∈ (R b K + 1).primesBelow, (p : ℝ)⁻¹
      = ∑ p ∈ (R b K + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹
        + ∑ p ∈ (R b K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the dyadic bound for `2 < p ≤ R`
  have hdy := sum_inv_primes_Ioc_le (R := 2) (Y := R b K) le_rfl hR2
  have hlogR : Nat.log 2 (R b K) = 2 ^ m₁ b K := natLog_R b K
  have hlog2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (by norm_num : 1 < 2) 1
  rw [hlogR, hlog2] at hdy
  push_cast at hdy
  rw [Real.log_pow, Real.log_one] at hdy
  have hl2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hm0 : (0 : ℝ) ≤ m₁ b K := by positivity
  have hA : ∑ p ∈ (R b K + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹ ≤ 4 + 3 * m₁ b K := by
    nlinarith
  -- the primes `≤ 2` contribute at most `1/2`
  have hB : ∑ p ∈ (R b K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ ≤ 1 / 2 := by
    have hsub2 : (R b K + 1).primesBelow.filter (fun p => ¬ 2 < p) ⊆ {2} := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have := hp.1.2.two_le
      rw [Finset.mem_singleton]; omega
    calc ∑ p ∈ (R b K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹
        ≤ ∑ p ∈ ({2} : Finset ℕ), (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)
      _ = 1 / 2 := by simp
  linarith

/-! ### The subset count -/

lemma Kr_le_m₁ {b : ℕ} (hb : 3 ≤ b) (K : ℕ) : K * (K ^ 2) ^ K ≤ m₁ b K := by
  refine le_trans ?_ (m₁_ge hb)
  have : K * (K ^ 2) ^ K = K ^ (2 * K + 1) := by rw [← pow_mul]; ring
  rw [this]
  exact Nat.le_mul_of_pos_left _ (by positivity)

lemma m₁_le_T_mul_m₁ {K : ℕ} (hK : 1 ≤ K) : m₁ b K ≤ T K * m₁ b K :=
  Nat.le_mul_of_pos_left _ (T_pos hK)

lemma Kr_le_T_mul_m₁ {b K : ℕ} (hb : 3 ≤ b) (hK : 1 ≤ K) : K * (K ^ 2) ^ K ≤ T K * m₁ b K :=
  (Kr_le_m₁ hb K).trans (m₁_le_T_mul_m₁ hK)

lemma Mc_le_two_pow_m₂ {b K : ℕ} (h : Hyp b K) : Mc b K ≤ 2 ^ m₂ K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  unfold m₂
  calc Mc b K ≤ K ^ (6 * K + 9) := Mc_le h
    _ ≤ 2 ^ (K * (6 * K + 9)) := pow_le_two_pow_mul _ _
    _ ≤ 2 ^ (8 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

lemma Mc_le_two_pow_m {b K : ℕ} (h : Hyp b K) : Mc b K ≤ 2 ^ m b K :=
  (Mc_le_two_pow_m₂ h).trans (Nat.pow_le_pow_right (by norm_num) (by unfold m; omega))

lemma Kr_le_two_pow_m {b K : ℕ} (h : Hyp b K) : K * (K ^ 2) ^ K ≤ 2 ^ m b K :=
  (Kr_le_m₁ h.hb K).trans ((m₁_le_m b K).trans (Nat.lt_two_pow_self).le)

lemma R_pow_two_Mc_le {b K : ℕ} (h : Hyp b K) :
    (R b K : ℝ) ^ (2 * Mc b K) ≤ (2 : ℝ) ^ (10 * 2 ^ m b K) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  unfold R
  push_cast
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  have h1 := Mc_le_two_pow_m₂ h
  have h2 : 2 ^ m b K = 2 ^ m₁ b K * 2 ^ m₂ K := by unfold m; rw [pow_add]
  rw [h2]
  nlinarith [Nat.one_le_two_pow (n := m₁ b K)]

lemma R_ge_two (b K : ℕ) : 2 ≤ R b K := by
  unfold R
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ m₁ b K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

lemma inv_card_le {b K : ℕ} (h : Hyp b K) :
    1 / ((apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
      ≤ 2 * (gridOf K (N K) h.hK1).P₀ / X b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K)
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X b K := by unfold X; positivity
  have hcard := card_apSample_ge_half (X b K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X h)
  have hcard0 : (0 : ℝ) < (apSample (X b K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X b K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  rw [div_le_div_iff₀ hcard0 hXr]
  have := hcard
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-! ### The Jackson term -/

lemma two_pow_div_le {e₁ : ℕ} (K : ℕ) (h : e₁ + 6 ≤ 100 * 2 ^ m b K) :
    (2 : ℝ) ^ e₁ / (2 : ℝ) ^ (100 * 2 ^ m b K) ≤ 1 / 64 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  calc (2 : ℝ) ^ e₁ * 64 = (2 : ℝ) ^ (e₁ + 6) := by rw [pow_add]; norm_num
    _ ≤ (2 : ℝ) ^ (100 * 2 ^ m b K) := pow_le_pow_right₀ (by norm_num) h
    _ = _ := (one_mul _).symm

lemma sizes_le_two_pow_m {K : ℕ} (h : Hyp b K) :
    K * (K ^ 2) ^ K ≤ 2 ^ m b K ∧ Mc b K ≤ 2 ^ m b K ∧ 8 ≤ 2 ^ m b K := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  refine ⟨Kr_le_two_pow_m h, Mc_le_two_pow_m h, ?_⟩
  have h3 : 3 ≤ K ^ 3 := by
    calc 3 ≤ K := by omega
      _ ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have := m₁_ge_cube h.hb h.hK1
  have := m₁_le_m b K
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m b K := Nat.pow_le_pow_right (by norm_num) (by omega)

end SchedB

end NormalNumbers.G4
