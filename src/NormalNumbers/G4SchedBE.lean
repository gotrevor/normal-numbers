/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBParams
import NormalNumbers.G4EntropyMTowerHarmonic

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
  pow_le_two_pow_mul)

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

end SchedB

end NormalNumbers.G4
