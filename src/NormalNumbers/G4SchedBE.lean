/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBParams
import NormalNumbers.G4EntropyMTowerHarmonic
import NormalNumbers.G4SchedBBudget

/-!
# The base-`b` schedule in a FREE cutoff exponent `e`

`G4SchedBParams` hard-codes the cutoff exponent `m₁ b K = 1000 b^{2K+4} K^{2K+1}`
(`R = 2^{2^{m₁}}`).  Campaign A needs the same schedule with a *larger* cutoff, because the
`S`-restricted Mertens supply is only `c · e − C` (`DESIGN-2026-09-16-prime-subset.md`,
`G4SubsetSchedule.exists_cutoff_subset`).  The audit's finding is that the schedule constrains
`e` only through

* a **floor** `m₁ b K ≤ e` — the gain term, and every "`e` is big enough" ladder fact; and
* a **cap** `Mc = 10⁵ · T K · e ≤ 2^{m₂ K}` — the moment order against the counting budget.

`HypE b K e` is exactly those two facts on top of `Hyp b K`, and this module re-derives the
schedule's parameter layer in `e`.  Everything that is *monotone* in the outer scale is inherited
from `G4SchedBParams` by `X b K ≤ XE K e` (`X_le_XE`); the two harmonic bounds come from
`G4EntropyMTowerHarmonic.sum_inv_smallPrimes_{ge,le}_gen`, which were already generic in `e`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J T m₂ logP₀Nat gridDm_le_gridP₀Bound card_apSample_ge_half P₀_le_exp
  pow_le_two_pow_mul card_small_subsets_le card_smallPrimes_le exp_one_le
  prod_one_add_le_exp_sum two_pow_le_exp two_le_exp_one exp_thirteen_half_le
  four_e_div_thirteen_le six_sevenths_pow_le Dj jackson_term_le Lambda_le budget_assembly
  exp_neg_four_le)

/-- `mE = e + m₂ K`. -/
def mE (K e : ℕ) : ℕ := e + m₂ K
/-- The moment order at cutoff exponent `e`. -/
def McE (K e : ℕ) : ℕ := 100000 * T K * e
/-- `RE = 2^{2^e}`. -/
def RE (e : ℕ) : ℕ := 2 ^ 2 ^ e
/-- `YE = 2^{2^{mE}}`. -/
def YE (K e : ℕ) : ℕ := 2 ^ 2 ^ mE K e
/-- `XE = 2^{100·2^{mE}}`. -/
def XE (K e : ℕ) : ℕ := 2 ^ (100 * 2 ^ mE K e)

/-- The standing hypotheses of the schedule at a free cutoff exponent. -/
structure HypE (b K e : ℕ) : Prop where
  base : Hyp b K
  /-- the gain floor: the cutoff is at least the base schedule's -/
  lo : m₁ b K ≤ e
  /-- the moment cap -/
  hi : McE K e ≤ 2 ^ m₂ K

variable {b K e : ℕ}

lemma HypE.hK1 (h : HypE b K e) : 1 ≤ K := h.base.hK1

/-! ### Monotonicity in the cutoff -/

lemma m_le_mE (h : HypE b K e) : m b K ≤ mE K e := by
  have := h.lo; unfold m mE; omega

lemma X_le_XE (h : HypE b K e) : X b K ≤ XE K e := by
  unfold X XE
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (m_le_mE h)))

lemma e_le_mE (K e : ℕ) : e ≤ mE K e := by unfold mE; omega

lemma mE_sub (K e : ℕ) : mE K e - e = m₂ K := by unfold mE; omega

/-! ### The two harmonic bounds -/

theorem sum_inv_smallPrimes_geE (h : HypE b K e) :
    (e : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ :=
  Sched.sum_inv_smallPrimes_ge_gen h.base.hK e rfl

theorem sum_inv_smallPrimes_leE (h : HypE b K e) :
    ∑ p ∈ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ ≤ 3 * (e : ℝ) + 5 :=
  Sched.sum_inv_smallPrimes_le_gen h.base.hK e rfl

/-! ### The size facts -/

lemma RE_ge_two (e : ℕ) : 2 ≤ RE e := Sched.two_le_two_pow_two_pow e

lemma natLog_YE (K e : ℕ) : Nat.log 2 (YE K e) = 2 ^ mE K e := Nat.log_pow (by norm_num) _

lemma natLog_RE (e : ℕ) : Nat.log 2 (RE e) = 2 ^ e := Nat.log_pow (by norm_num) _

lemma dyadic_factor_leE (K e : ℕ) :
    1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)) ≤ 1 + 6 * (K : ℝ) ^ 2 := by
  rw [natLog_YE, natLog_RE]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  have h1 : ((mE K e : ℝ) - e) = m₂ K := by
    rw [← Nat.cast_sub (e_le_mE K e), mE_sub]
  have h2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have h3 : (m₂ K : ℝ) = 8 * (K : ℝ) ^ 2 := by unfold m₂; push_cast; ring
  have h4 : (mE K e : ℝ) * Real.log 2 - (e : ℝ) * Real.log 2 = 8 * (K : ℝ) ^ 2 * Real.log 2 := by
    rw [← sub_mul, h1, h3]
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg (K : ℝ)]

lemma log_RE (e : ℕ) : Real.log (RE e) = (2 : ℝ) ^ e * Real.log 2 := by
  unfold RE; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

lemma log_log_RE_ge (e : ℕ) :
    (e : ℝ) * Real.log 2 - 1 ≤ Real.log (Real.log (RE e)) :=
  Sched.log_log_Rgen_ge e

/-! ### The moment cap -/

lemma McE_le_two_pow_m₂ (h : HypE b K e) : McE K e ≤ 2 ^ m₂ K := h.hi

lemma McE_le_two_pow_mE (h : HypE b K e) : McE K e ≤ 2 ^ mE K e :=
  h.hi.trans (Nat.pow_le_pow_right (by norm_num) (by unfold mE; omega))

lemma Kr_le_T_mul_e (h : HypE b K e) : K * (K ^ 2) ^ K ≤ T K * e :=
  ((Kr_le_m₁ h.base.hb K).trans h.lo).trans (Nat.le_mul_of_pos_left _
    (Sched.T_pos h.base.hK1))

lemma Kr_le_two_pow_mE (h : HypE b K e) : K * (K ^ 2) ^ K ≤ 2 ^ mE K e :=
  ((Kr_le_m₁ h.base.hb K).trans h.lo).trans
    ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (e_le_mE K e)))

lemma RE_pow_two_McE_le (h : HypE b K e) :
    (RE e : ℝ) ^ (2 * McE K e) ≤ (2 : ℝ) ^ (10 * 2 ^ mE K e) := by
  unfold RE
  push_cast
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  have h1 := h.hi
  have h2 : 2 ^ mE K e = 2 ^ e * 2 ^ m₂ K := by unfold mE; rw [pow_add]
  rw [h2]
  nlinarith [Nat.one_le_two_pow (n := e)]

lemma McE_pos (h : HypE b K e) : 0 < McE K e := by
  have h1 : 0 < T K := Sched.T_pos h.base.hK1
  have h2 : 0 < m₁ b K := by
    have := Kr_le_m₁ h.base.hb K
    have hK := h.base.hK
    have : 0 < K * (K ^ 2) ^ K := by positivity
    omega
  have h3 := h.lo
  have : 0 < e := by omega
  unfold McE
  positivity

/-! ### The outer-scale facts, inherited by monotonicity -/

lemma two_mul_P₀_le_XE (h : HypE b K e) :
    2 * (gridOf K (N K) h.hK1).P₀ ≤ XE K e :=
  (two_mul_P₀_le_X h.base).trans (X_le_XE h)

lemma gridDm_le_XE (h : HypE b K e) : gridDm K (N K) ≤ XE K e :=
  (gridDm_le_X h.base).trans (X_le_XE h)

lemma sample_nonemptyE (h : HypE b K e) :
    (apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).Nonempty :=
  apSample_nonempty_of_le _ _ _ (gridOf K (N K) h.hK1).P₀_pos
    (gridOf K (N K) h.hK1).b₀_lt_P₀ (two_mul_P₀_le_XE h)

lemma J_mul_gridDm_le_XE (h : HypE b K e) : J K * gridDm K (N K) ≤ XE K e :=
  (J_mul_gridDm_le_X h.base).trans (X_le_XE h)

lemma sizes_le_two_pow_mE (h : HypE b K e) :
    K * (K ^ 2) ^ K ≤ 2 ^ mE K e ∧ McE K e ≤ 2 ^ mE K e ∧ 8 ≤ 2 ^ mE K e := by
  refine ⟨Kr_le_two_pow_mE h, McE_le_two_pow_mE h, ?_⟩
  have h3 : 3 ≤ K ^ 3 := by
    have := h.base.hK
    calc 3 ≤ K := by omega
      _ ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have h4 := m₁_ge_cube h.base.hb h.base.hK1
  have h5 := h.lo
  have h6 := e_le_mE K e
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ mE K e := Nat.pow_le_pow_right (by norm_num) (by omega)


lemma logP₀Nat_le_two_pow_mE {b K e : ℕ} (h : HypE b K e) : logP₀Nat K ≤ 2 ^ mE K e :=
  (logP₀Nat_le_two_pow_m h.base).trans (Nat.pow_le_pow_right (by norm_num) (m_le_mE h))

theorem farC_leE {b K e : ℕ} (h : HypE b K e) :
    farC (gridOf K (N K) h.hK1) (XE K e) (gridDm K (N K)) ≤ logP₀Nat K + mE K e + 10 := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < XE K e := by unfold XE; positivity
  have hcard := card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_XE h)
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (XE K e : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ XE K e := by exact_mod_cast gridDm_le_XE h
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  unfold farC
  -- first term: `(X+Dm)/|P| ≤ 4P₀`
  have h1 : (((XE K e + gridDm K (N K) : ℕ) : ℝ) / (apSample (XE K e) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (XE K e : ℝ) + gridDm K (N K) ≤ 2 * XE K e := by linarith
      _ = 4 * G.P₀ * ((XE K e : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (XE K e) G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((XE K e + gridDm K (N K) : ℕ) : ℝ) / (apSample (XE K e) G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((XE K e + gridDm K (N K) : ℕ) : ℝ) / (apSample (XE K e) G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((XE K e + gridDm K (N K) : ℕ) : ℝ) / (apSample (XE K e) G.P₀ G.b₀).card)
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
  have h2 : Real.log (Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ mE K e + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogX : Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (mE K e + 7) := by
      have hle : ((XE K e + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mE K e + 1) := by
        push_cast
        have : (XE K e : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mE K e) := by unfold XE; push_cast; rfl
        rw [pow_succ]
        linarith
      calc Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ mE K e + 1)) :=
            Real.log_le_log (by push_cast; positivity) hle
        _ = (100 * 2 ^ mE K e + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (100 * 2 ^ mE K e + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (100 * 2 ^ mE K e + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (mE K e + 7) := by
            have : 100 * 2 ^ mE K e + 1 ≤ 2 ^ (mE K e + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ mE K e := Nat.one_le_two_pow
              omega
            exact_mod_cast this
    have hpos : (0 : ℝ) < Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ) :=
        Real.log_nonneg (by push_cast; unfold XE; have : (1:ℝ) ≤ 2 ^ (100 * 2 ^ mE K e) := one_le_pow₀ (by norm_num); push_cast; linarith [(Nat.cast_nonneg (gridDm K (N K)) : (0:ℝ) ≤ _)])
      linarith
    calc Real.log (Real.log ((XE K e + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (mE K e + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (mE K e + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (mE K e + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (mE K e + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (mE K e + 8 : ℕ) := by positivity
          nlinarith
      _ = mE K e + 8 := by push_cast; ring
  linarith

lemma inv_card_leE {b K e : ℕ} (h : HypE b K e) :
    1 / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
      ≤ 2 * (gridOf K (N K) h.hK1).P₀ / XE K e := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  set G := gridOf K (N K) (by omega : 1 ≤ K)
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < XE K e := by unfold XE; positivity
  have hcard := card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_XE h)
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (XE K e : ℝ) / (2 * G.P₀) := by positivity
    linarith
  rw [div_le_div_iff₀ hcard0 hXr]
  have := hcard
  rw [div_le_iff₀ (by positivity)] at this
  linarith

lemma log_Mx_div_leE {b K e : ℕ} (h : HypE b K e) :
    Real.log ((XE K e + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (YE K e) ≤ 101 := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogY : Real.log (YE K e) = (2 : ℝ) ^ mE K e * Real.log 2 := by
    unfold YE; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hY0 : 0 < Real.log (YE K e) := by rw [hlogY]; positivity
  rw [div_le_iff₀ hY0, hlogY]
  have hMx : ((XE K e + J K * gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ mE K e + 1) := by
    have := J_mul_gridDm_le_XE h
    have hX : (XE K e : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mE K e) := by unfold XE; push_cast; rfl
    push_cast
    rw [pow_succ]
    have : (J K * gridDm K (N K) : ℝ) ≤ XE K e := by exact_mod_cast this
    linarith
  have hX0 : (0 : ℝ) < XE K e := by unfold XE; positivity
  calc Real.log ((XE K e + J K * gridDm K (N K) : ℕ) : ℝ)
      ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ mE K e + 1)) :=
        Real.log_le_log (by push_cast; positivity) hMx
    _ = (100 * 2 ^ mE K e + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ 101 * ((2 : ℝ) ^ mE K e * Real.log 2) := by
        push_cast
        have : (1 : ℝ) ≤ 2 ^ mE K e := one_le_pow₀ (by norm_num)
        nlinarith


/-! ### The main budget term at a free cutoff -/

/-- **The gain term at cutoff `e`.**  Identical to `main_term_le`, and the only place the
Mertens supply enters: raising `e` above `m₁ b K` only helps. -/
lemma main_term_leE_gen (h : HypE b K e) {sm : Finset ℕ}
    (hlow : (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4 ≤ ∑ p ∈ sm, (p : ℝ)⁻¹) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * Real.exp (-∑ p ∈ sm,
          4 * freqSeed b K / p)
      ≤ Real.exp (-4) := by
  have hb := h.base.hb; have hK := h.base.hK
  have hS := hlow
  set Sg := ∑ p ∈ sm, (p : ℝ)⁻¹ with hSgdef
  set θ := freqSeed b K with hθ
  have hθ0 : 0 ≤ θ := freqSeed_nonneg (by exact_mod_cast (show 2 ≤ b by omega)) K
  have hsum : ∑ p ∈ sm, 4 * θ / p = 4 * θ * Sg := by
    rw [hSgdef, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [div_eq_mul_inv]
  rw [hsum]
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set r : ℝ := (((K ^ 2) ^ K : ℕ) : ℝ) with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hKr1 : (1 : ℝ) ≤ K * r := by nlinarith
  have h2K : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hm₁ : θ * m₁ b K = 1000 * (2 : ℝ) ^ K * (K * r) := by
    rw [hθ, hr]; exact freqSeed_mul_m₁ hb K
  have hsmall : θ * (21 * (K : ℝ) ^ 2 + 4) ≤ 1 := by
    have hq := twentyone_sq_add_four_le_four_pow hK
    have h' : (21 * (K : ℝ) ^ 2 + 4) ≤ (4 : ℝ) ^ K := by exact_mod_cast hq
    have hθ8 := freqSeed_le_quarter_pow hb K
    calc θ * (21 * (K : ℝ) ^ 2 + 4) ≤ (1 / 4 : ℝ) ^ K * 4 ^ K := by gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hS8 : 690 * (K * r) - 1 ≤ θ * Sg := by
    have hmul := mul_le_mul_of_nonneg_left hS hθ0
    have ee : θ * ((m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4)
        = 1000 * (2 : ℝ) ^ K * (K * r) * Real.log 2 - θ * (21 * (K : ℝ) ^ 2 + 4) := by
      rw [← hm₁]; ring
    rw [ee] at hmul
    have hKr0 : 0 ≤ K * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2K (by norm_num : (0:ℝ) ≤ 1000)) hKr0]
  have h2 := Sched.two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * r) := by rw [hr]; push_cast; ring
  rw [hcast] at h2
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) * Real.exp (-(4 * θ * Sg))
      ≤ Real.exp (2 * (K * r)) * Real.exp (-(4 * θ * Sg)) := by gcongr
    _ = Real.exp (2 * (K * r) - 4 * θ * Sg) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        nlinarith


/-- The gain term at the schedule's own small primes. -/
lemma main_term_leE (h : HypE b K e) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * Real.exp (-∑ p ∈ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀,
          4 * freqSeed b K / p)
      ≤ Real.exp (-4) :=
  main_term_leE_gen h (by
    refine le_trans ?_ (sum_inv_smallPrimes_geE h)
    have hle : (m₁ b K : ℝ) ≤ (e : ℝ) := by exact_mod_cast h.lo
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith)

lemma P₀_le_two_powE (h : HypE b K e) :
    ((gridOf K (N K) h.hK1).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ mE K e) :=
  (P₀_le_two_pow h.base).trans (pow_le_pow_right₀ (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (m_le_mE h))))

lemma two_pow_div_leE {e₁ : ℕ} (K e : ℕ) (h : e₁ + 6 ≤ 100 * 2 ^ mE K e) :
    (2 : ℝ) ^ e₁ / (2 : ℝ) ^ (100 * 2 ^ mE K e) ≤ 1 / 64 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  calc (2 : ℝ) ^ e₁ * 64 = (2 : ℝ) ^ (e₁ + 6) := by rw [pow_add]; norm_num
    _ ≤ (2 : ℝ) ^ (100 * 2 ^ mE K e) := pow_le_pow_right₀ (by norm_num) h
    _ = _ := (one_mul _).symm

lemma term_a_leE_gen (h : HypE b K e) {sm : Finset ℕ} (hsmcard : sm.card ≤ RE e + 1) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((((sm).powerset.filter
            (fun T' => T'.Nonempty ∧ T'.card ≤ McE K e)).card : ℝ)
          * (2 ^ McE K e * (2 * (RE e : ℝ) ^ McE K e
              / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ))))
      ≤ 1 / 64 := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  have hcardN := card_small_subsets_le sm (McE K e)
  have hsmN := hsmcard
  have hR2 := RE_ge_two e
  have hcard : ((((sm).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ McE K e)).card : ℕ) : ℝ) ≤ McE K e * (2 * (RE e : ℝ)) ^ McE K e := by
    have : ((sm).powerset.filter
        (fun T' => T'.Nonempty ∧ T'.card ≤ McE K e)).card ≤ McE K e * (2 * RE e) ^ McE K e := by
      refine hcardN.trans ?_
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    exact_mod_cast this
  have hinv := inv_card_leE h
  have hMc : (McE K e : ℝ) ≤ 2 ^ McE K e := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hR2Mc := RE_pow_two_McE_le h
  have hP₀ := P₀_le_two_powE h
  have hX : (XE K e : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mE K e) := by unfold XE; push_cast; rfl
  have hXpos : (0 : ℝ) < XE K e := by rw [hX]; positivity
  have hP₀0 : (0 : ℝ) ≤ (gridOf K (N K) h.hK1).P₀ := by positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
  set c := ((((sm).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ McE K e)).card : ℕ) : ℝ)
  have hΛ0 : 0 ≤ Λ := by positivity
  have hRr : (0 : ℝ) ≤ RE e := by positivity
  calc Λ * (c * (2 ^ McE K e * (2 * (RE e : ℝ) ^ McE K e / Psz)))
      = Λ * c * 2 ^ McE K e * 2 * (RE e : ℝ) ^ McE K e * (1 / Psz) := by ring
    _ ≤ Λ * (McE K e * (2 * (RE e : ℝ)) ^ McE K e) * 2 ^ McE K e * 2 * (RE e : ℝ) ^ McE K e
          * (2 * (gridOf K (N K) h.hK1).P₀ / XE K e) := by gcongr
    _ = Λ * McE K e * 2 ^ McE K e * 2 ^ McE K e * 4 * (RE e : ℝ) ^ (2 * McE K e) * (gridOf K (N K) h.hK1).P₀ / XE K e := by
        rw [mul_pow, pow_mul (RE e : ℝ) 2 (McE K e), sq]; ring
    _ ≤ Λ * 2 ^ McE K e * 2 ^ McE K e * 2 ^ McE K e * 4 * (2 : ℝ) ^ (10 * 2 ^ mE K e)
          * (2 : ℝ) ^ (2 * 2 ^ mE K e) / (2 : ℝ) ^ (100 * 2 ^ mE K e) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + McE K e + McE K e + McE K e + 2 + 10 * 2 ^ mE K e + 2 * 2 ^ mE K e)
          / (2 : ℝ) ^ (100 * 2 ^ mE K e) := by
        rw [hΛ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_leE
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_mE h
        omega

/-- Term (a) at the schedule's own small primes. -/
lemma term_a_leE (h : HypE b K e) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((((smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).powerset.filter
            (fun T' => T'.Nonempty ∧ T'.card ≤ McE K e)).card : ℝ)
          * (2 ^ McE K e * (2 * (RE e : ℝ) ^ McE K e
              / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ))))
      ≤ 1 / 64 :=
  term_a_leE_gen h (card_smallPrimes_le _ _)

lemma term_d_leE_gen (h : HypE b K e) {sm : Finset ℕ} (hsmcard : sm.card ≤ RE e + 1) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / McE K e) ^ McE K e * ((sm).card : ℝ) ^ McE K e
          * (2 * (RE e : ℝ) ^ McE K e / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)))
      ≤ 1 / 64 := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  have hsmN := hsmcard
  have hR2 := RE_ge_two e
  have hMc1 : (1 : ℝ) ≤ McE K e := by exact_mod_cast McE_pos h
  have he := exp_one_le
  -- `(2e/Mc)^{Mc}·|sm|^{Mc} ≤ (16R)^{Mc}`
  have hbase : 2 * Real.exp 1 / McE K e * ((sm).card : ℝ) ≤ 16 * RE e := by
    have hsm : ((sm).card : ℝ) ≤ 2 * RE e := by
      have : (sm).card ≤ 2 * RE e := by omega
      exact_mod_cast this
    have hsm0 : (0 : ℝ) ≤ (sm).card := by positivity
    have h1 : 2 * Real.exp 1 / McE K e ≤ 2 * Real.exp 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.exp_pos 1]
    have h2 : 2 * Real.exp 1 / McE K e * ((sm).card : ℝ)
        ≤ 2 * Real.exp 1 * (2 * RE e) := by
      apply mul_le_mul h1 hsm hsm0 (by positivity)
    nlinarith [Real.exp_pos 1]
  have hpow : (2 * Real.exp 1 / McE K e) ^ McE K e * ((sm).card : ℝ) ^ McE K e
      ≤ (2 : ℝ) ^ (4 * McE K e) * (RE e : ℝ) ^ McE K e := by
    rw [← mul_pow, pow_mul, show (2 : ℝ) ^ 4 = 16 by norm_num, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hinv := inv_card_leE h
  have hR2Mc := RE_pow_two_McE_le h
  have hP₀ := P₀_le_two_powE h
  have hX : (XE K e : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mE K e) := by unfold XE; push_cast; rfl
  have hXpos : (0 : ℝ) < XE K e := by rw [hX]; positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
  set q := (2 * Real.exp 1 / McE K e) ^ McE K e * ((sm).card : ℝ) ^ McE K e with hq
  have hq0 : 0 ≤ q := by positivity
  calc Λ * (2 * (2 * Real.exp 1 / McE K e) ^ McE K e * ((sm).card : ℝ) ^ McE K e
          * (2 * (RE e : ℝ) ^ McE K e / Psz))
      = Λ * q * 2 * 2 * (RE e : ℝ) ^ McE K e * (1 / Psz) := by rw [hq]; ring
    _ ≤ Λ * ((2 : ℝ) ^ (4 * McE K e) * (RE e : ℝ) ^ McE K e) * 2 * 2 * (RE e : ℝ) ^ McE K e
          * (2 * (gridOf K (N K) h.hK1).P₀ / XE K e) := by gcongr
    _ = Λ * (2 : ℝ) ^ (4 * McE K e) * 8 * (RE e : ℝ) ^ (2 * McE K e) * (gridOf K (N K) h.hK1).P₀ / XE K e := by
        rw [pow_mul (RE e : ℝ) 2 (McE K e), sq]; ring
    _ ≤ Λ * (2 : ℝ) ^ (4 * McE K e) * 8 * (2 : ℝ) ^ (10 * 2 ^ mE K e) * (2 : ℝ) ^ (2 * 2 ^ mE K e)
          / (2 : ℝ) ^ (100 * 2 ^ mE K e) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + 4 * McE K e + 3 + 10 * 2 ^ mE K e + 2 * 2 ^ mE K e)
          / (2 : ℝ) ^ (100 * 2 ^ mE K e) := by
        rw [hΛ, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_leE
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_mE h
        omega

/-- Term (d) at the schedule's own small primes. -/
lemma term_d_leE (h : HypE b K e) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / McE K e) ^ McE K e
            * ((smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).card : ℝ) ^ McE K e
          * (2 * (RE e : ℝ) ^ McE K e
              / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)))
      ≤ 1 / 64 :=
  term_d_leE_gen h (card_smallPrimes_le _ _)

/-! ### The two harmonic-upper budget terms

`term_b` and `term_c` are the two places where the *upper* Mertens bound
`∑_{p<R} 1/p ≤ 3e + 5` is consumed (everything else uses the lower bound or is monotone).
At a free cutoff this is exactly where the moment cap `Mc ≈ 10⁵·T·e` earns its constant:
the harmonic factor costs `≤ 44·T·e` in `term_b` and `≤ 8800·T·e` in `term_c`, and the
moment order pays `10⁵·T·e` (resp. `10⁵·T·e/7`). -/

lemma one_le_eE (h : HypE b K e) : 1 ≤ e :=
  ((Nat.one_le_pow 3 K h.base.hK1).trans (m₁_ge_cube h.base.hb h.base.hK1)).trans h.lo

lemma term_b_leE_gen (h : HypE b K e) {sm : Finset ℕ}
    (hsum : ∑ p ∈ sm, (p : ℝ)⁻¹ ≤ 3 * (e : ℝ) + 5) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((∏ p ∈ sm, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          / Real.exp 1 ^ McE K e)
      ≤ Real.exp (-4) := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  have hS := hsum
  have hprod := prod_le_exp_mul_sum (sm) (Real.exp 1)
    (2 * (T K : ℝ)) (Real.exp_pos 1).le (by positivity)
  have he := exp_one_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast Sched.T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast one_le_eE h
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * e := by exact_mod_cast Kr_le_T_mul_e h
  have hMc : (McE K e : ℝ) = 100000 * T K * e := by unfold McE; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ sm, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ sm, (p : ℝ)⁻¹
      ≤ 44 * (T K * (e : ℝ)) := by
    have : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ sm, (p : ℝ)⁻¹
        ≤ Real.exp 1 * (2 * (T K : ℝ)) * (3 * (e : ℝ) + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos 1, mul_le_mul_of_nonneg_left he hT0]
  rw [Real.exp_one_pow, div_eq_mul_inv, ← Real.exp_neg]
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * ((∏ p ∈ sm, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          * Real.exp (-(McE K e : ℝ)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp (Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ sm, (p : ℝ)⁻¹)
          * Real.exp (-(McE K e : ℝ))) := by gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K)
        + Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ sm, (p : ℝ)⁻¹ - McE K e) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ (e : ℝ)),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-- Term (b) at the schedule's own small primes. -/
lemma term_b_leE (h : HypE b K e) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((∏ p ∈ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          / Real.exp 1 ^ McE K e)
      ≤ Real.exp (-4) :=
  term_b_leE_gen h (sum_inv_smallPrimes_leE h)

lemma term_c_leE_gen (h : HypE b K e) {sm : Finset ℕ}
    (hsum : ∑ p ∈ sm, (p : ℝ)⁻¹ ≤ 3 * (e : ℝ) + 5) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / (13 / 2)) ^ McE K e
          * ∏ p ∈ sm, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (-4) := by
  have hb := h.base.hb; have hbK := h.base.hbK; have hK := h.base.hK
  have hS := hsum
  have hprod := prod_le_exp_mul_sum (sm)
    (Real.exp (13 / 2)) (T K : ℝ) (Real.exp_pos _).le (by positivity)
  have he := exp_thirteen_half_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast Sched.T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast one_le_eE h
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * e := by exact_mod_cast Kr_le_T_mul_e h
  have hMc : (McE K e : ℝ) = 100000 * T K * e := by unfold McE; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ sm, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ sm, (p : ℝ)⁻¹
      ≤ 8800 * (T K * (e : ℝ)) := by
    have : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ sm, (p : ℝ)⁻¹
        ≤ Real.exp (13 / 2) * (T K : ℝ) * (3 * (e : ℝ) + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos (13 / 2 : ℝ), mul_le_mul_of_nonneg_left he hT0]
  have hlam : (2 * Real.exp 1 / (13 / 2)) ^ McE K e ≤ Real.exp (-(McE K e : ℝ) / 7) :=
    (pow_le_pow_left₀ (by positivity) four_e_div_thirteen_le _).trans (six_sevenths_pow_le _)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * (2 * (2 * Real.exp 1 / (13 / 2)) ^ McE K e
          * ∏ p ∈ sm, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp 1 * Real.exp (-(McE K e : ℝ) / 7)
          * Real.exp (Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ sm, (p : ℝ)⁻¹)) := by
        gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K) + 1 - McE K e / 7
        + Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ sm, (p : ℝ)⁻¹) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ (e : ℝ)),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-- Term (c) at the schedule's own small primes. -/
lemma term_c_leE (h : HypE b K e) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / (13 / 2)) ^ McE K e
          * ∏ p ∈ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀,
              (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (-4) :=
  term_c_leE_gen h (sum_inv_smallPrimes_leE h)

/-! ### The closed budget at a free cutoff, over an arbitrary sub-family of small primes

This is the form campaign A needs.  The four junk terms (a)–(d) only *shrink* when small primes
are dropped, so they are bounded for any `sm ⊆ smallPrimes (RE e) P₀`; the gain term is the one
place where the family matters, and it is supplied as the hypothesis `hlow` — exactly the shape
`MertensAP.exists_cutoff_subset` produces for `sm = (smallPrimes (RE e) P₀).filter S`. -/

/-- **`hbudget` at a free cutoff `e`, for any sub-family `sm` of the schedule's small primes.** -/
theorem hbudget_holdsE_gen {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e)
    {sm : Finset ℕ} (hsub : sm ⊆ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀)
    (hlow : (m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4 ≤ ∑ p ∈ sm, (p : ℝ)⁻¹) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound sm (T K) (RE e) (McE K e)
            (apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed b K) < 1 := by
  have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hJ := jackson_term_le (K := K) (k₄ := k₄) (by omega)
  have hΛ := Lambda_le hK4 hk
  have hsmcard : sm.card ≤ RE e + 1 :=
    (Finset.card_le_card hsub).trans (card_smallPrimes_le _ _)
  have hsum : ∑ p ∈ sm, (p : ℝ)⁻¹ ≤ 3 * (e : ℝ) + 5 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
      (sum_inv_smallPrimes_leE h)
  unfold smallPrimeBound
  exact budget_assembly hΛ (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (main_term_leE_gen h hlow) (term_a_leE_gen h hsmcard)
    (term_b_leE_gen h hsum) (term_c_leE_gen h hsum) (term_d_leE_gen h hsmcard)  hJ

/-- **`hbudget` at a free cutoff `e`**, at the schedule's own small primes. -/
theorem hbudget_holdsE {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀) (T K) (RE e) (McE K e)
            (apSample (XE K e) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed b K) < 1 :=
  hbudget_holdsE_gen hK4 h (le_refl _) (by
    refine le_trans ?_ (sum_inv_smallPrimes_geE h)
    have hle : (m₁ b K : ℝ) ≤ (e : ℝ) := by exact_mod_cast h.lo
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith)


end SchedB

end NormalNumbers.G4
