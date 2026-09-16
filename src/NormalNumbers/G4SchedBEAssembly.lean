/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBE
import NormalNumbers.G4SchedBAssembly
import NormalNumbers.G4SubsetWitness
import NormalNumbers.G4SubsetSchedule

/-!
# The base-`b` schedule witness at a **free cutoff exponent `e`**

`G4SchedBAssembly` builds `scheduleWitnessB` at the hard-coded cutoff `e = m₁ b K`.  Campaign A
needs the same witness at any `e` satisfying `HypE b K e` (floor `m₁ b K ≤ e`, cap
`10⁵·T K·e ≤ 2^{m₂ K}`), because the `S`-restricted Mertens supply only meets the schedule's
demand at an inflated cutoff.

Everything ported here is the `D`-side of the witness — `hbig` and `hfar` — plus the one size
fact they need that is *not* monotone in the cutoff: `four_mul_le_two_pow_NE`, which says the
far-tail constant still fits under `2^{N K}` when `mE K e = e + m₂ K` replaces `m b K`.  It does,
with room: the moment cap forces `e ≤ 2^{m₂ K} = 2^{8K²}` while `N K = 100 K²`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J W H T logP₀Nat m₂ Dj T_pos N_pos logP₀Nat_le J_le m_le pow_le_two_pow_mul
  two_Dj_add_one_le k₄_bounds card_apSample_ge_half)

/-! ### The sample ratio and the far-tail size fact at a free cutoff -/

/-- `YE²/|P| ≤ 2^{−K}/2` at a free cutoff. -/
lemma sample_ratio_leE {b K e : ℕ} (h : HypE b K e) :
    (YE K e : ℝ) ^ 2 / ((apSample (XE K e) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ)
      ≤ (1 / 2 : ℝ) ^ K / 2 := by
  have hK := h.base.hK
  set G := gridOf K (Sched.N K) h.hK1 with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < XE K e := by unfold XE; positivity
  have hcard := Sched.card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_XE h)
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (XE K e : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hP₀2 := P₀_le_two_powE h
  have hY : (YE K e : ℝ) ^ 2 = (2 : ℝ) ^ (2 * 2 ^ mE K e) := by
    unfold YE; push_cast; rw [← pow_mul]; ring_nf
  have hX : (XE K e : ℝ) = (2 : ℝ) ^ (100 * 2 ^ mE K e) := by unfold XE; push_cast; rfl
  have hkey : (YE K e : ℝ) ^ 2 * G.P₀ * 4 ≤ (XE K e : ℝ) * (1 / 2 : ℝ) ^ K := by
    have hpow : (2 : ℝ) ^ (2 * 2 ^ mE K e) * (2 : ℝ) ^ (2 * 2 ^ mE K e) * 4 * (2 : ℝ) ^ K
        ≤ (2 : ℝ) ^ (100 * 2 ^ mE K e) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : K ≤ 2 ^ mE K e := by
        calc K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
          _ ≤ m₁ b K := m₁_ge_cube h.base.hb h.hK1
          _ ≤ e := h.lo
          _ ≤ mE K e := e_le_mE K e
          _ ≤ 2 ^ mE K e := (Nat.lt_two_pow_self).le
      have h2 : 2 ≤ 2 ^ mE K e := by
        calc 2 ≤ K := by omega
          _ ≤ 2 ^ mE K e := h1
      omega
    have hη : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
    rw [hY, hX, hη]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (2 * 2 ^ mE K e) * G.P₀ * 4 * 2 ^ K
        ≤ (2 : ℝ) ^ (2 * 2 ^ mE K e) * (2 : ℝ) ^ (2 * 2 ^ mE K e) * 4 * 2 ^ K := by gcongr
      _ ≤ _ := hpow
  rw [div_le_iff₀ hcard0]
  have hc : (XE K e : ℝ) / (2 * G.P₀) ≤ (apSample (XE K e) G.P₀ G.b₀).card := hcard
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  calc (YE K e : ℝ) ^ 2 = ((YE K e : ℝ) ^ 2 * G.P₀ * 4) / (4 * G.P₀) := by field_simp
    _ ≤ ((XE K e : ℝ) * (1 / 2 : ℝ) ^ K) / (4 * G.P₀) := by gcongr
    _ = (1 / 2 : ℝ) ^ K / 2 * ((XE K e : ℝ) / (2 * G.P₀)) := by field_simp; ring
    _ ≤ (1 / 2 : ℝ) ^ K / 2 * (apSample (XE K e) G.P₀ G.b₀).card := by gcongr

lemma four_mul_le_two_pow_half {b K : ℕ} (h : Hyp b K) :
    4 * K * (logP₀Nat K + m b K + 2 * J K + 13) ≤ 2 ^ (50 * K ^ 2) := by
  have hK := h.hK
  have h1 := logP₀Nat_le hK
  have h2 := m_le h
  have h3 := J_le hK
  have hK2 : 2 ≤ K := by omega
  have hA : logP₀Nat K + m b K + 2 * J K + 13 ≤ K ^ (20 * K + 18) := by
    have a1 : m b K ≤ K ^ (20 * K + 17) := h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
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
  have hC : K ^ (20 * K + 20) ≤ 2 ^ (50 * K ^ 2) := by
    calc K ^ (20 * K + 20) ≤ 2 ^ (K * (20 * K + 20)) := pow_le_two_pow_mul _ _
      _ ≤ 2 ^ (50 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 4 * K * (logP₀Nat K + m b K + 2 * J K + 13) ≤ 4 * K * K ^ (20 * K + 18) := by gcongr
    _ ≤ K ^ (20 * K + 20) := hB
    _ ≤ 2 ^ (50 * K ^ 2) := hC


/-- **The far-tail size fact at a free cutoff.**  `mE K e = e + m₂ K` replaces `m b K`, and the
moment cap `10⁵·T K·e ≤ 2^{m₂ K}` is exactly what keeps it under `2^{N K}`. -/
lemma four_mul_le_two_pow_NE {b K e : ℕ} (h : HypE b K e) :
    4 * K * (logP₀Nat K + mE K e + 2 * J K + 13) ≤ 2 ^ Sched.N K := by
  have hK := h.base.hK
  have hhalf := four_mul_le_two_pow_half h.base
  have hm2 : m₂ K ≤ m b K := by unfold m; omega
  have h1 : 4 * K * (logP₀Nat K + m₂ K + 2 * J K + 13) ≤ 2 ^ (50 * K ^ 2) := by
    refine le_trans ?_ hhalf
    exact Nat.mul_le_mul_left _ (by omega)
  have hT1 : 1 ≤ T K := T_pos (by omega)
  have hecap : e ≤ 2 ^ m₂ K := by
    have := h.hi
    unfold McE at this
    have : e ≤ 100000 * T K * e := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hKlt : K < 2 ^ K := Nat.lt_two_pow_self
  have h4K : 4 * K ≤ 2 ^ (K + 2) := by
    calc 4 * K ≤ 4 * 2 ^ K := by omega
      _ = 2 ^ (K + 2) := by rw [pow_add]; ring
  have h2 : 4 * K * e ≤ 2 ^ (50 * K ^ 2) := by
    have hm2' : m₂ K = 8 * K ^ 2 := rfl
    calc 4 * K * e ≤ 2 ^ (K + 2) * 2 ^ m₂ K := Nat.mul_le_mul h4K hecap
      _ = 2 ^ (K + 2 + m₂ K) := by rw [← pow_add]
      _ ≤ 2 ^ (50 * K ^ 2) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          rw [hm2']
          nlinarith
  have hsplit : 4 * K * (logP₀Nat K + mE K e + 2 * J K + 13)
      = 4 * K * (logP₀Nat K + m₂ K + 2 * J K + 13) + 4 * K * e := by
    unfold mE; ring
  have hfin : 2 ^ (50 * K ^ 2) + 2 ^ (50 * K ^ 2) ≤ 2 ^ Sched.N K := by
    have : 2 ^ (50 * K ^ 2) + 2 ^ (50 * K ^ 2) = 2 ^ (50 * K ^ 2 + 1) := by
      rw [pow_succ]; ring
    rw [this]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold Sched.N
    nlinarith
  omega

/-! ### `hbig` and `hfar` at a free cutoff -/

/-- **`hbig` in base `b ≥ 3`**, with `K = 4k₄`, `η = 2^{−k₄}`, `ε = 1/K`, `δbig = 1/8`,
`Mx = X + J·Dm`. -/
theorem hbig_holdsE {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * rowL2 b K
          + 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2
            / ((apSample (XE K e) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ))
      + (Real.log ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (YE K e)) * rowL1 b K
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.base.hb; have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hb1r : (512 : ℝ) * k₄ ^ 2 ≤ 2 ^ (3 * k₄) := by exact_mod_cast k₄_bound_three hk
  have hb2r : (4096 : ℝ) * k₄ ≤ 2 ^ k₄ := by exact_mod_cast k₄_bound_one hk
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hL1 : rowL1 b K ≤ a ^ 2 / 2 := by
    have := rowL1_le_three hb K; have := two_thirds_pow_le (k₄ := k₄) hK4; linarith
  have hL2 : rowL2 b K ≤ a ^ 8 / 8 := by
    have := rowL2_le_three hb K; have := two_ninths_pow_le (k₄ := k₄) hK4; linarith
  have hL10 := rowL1_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  have hL20 := rowL2_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  set Psz : ℝ := ((apSample (XE K e) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ)
    with hPsz
  have hPsz0 : 0 < Psz := by
    rw [hPsz]; exact_mod_cast (sample_nonemptyE h).card_pos
  -- the square root
  have hs1 := dyadic_factor_leE K e
  have hs2 := sample_ratio_leE h
  rw [← hPsz] at hs2
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * rowL2 b K
        + 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz) ≤ 2 * K * a ^ 4 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * rowL2 b K
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 8 / 8) := by
      have h0 : 0 ≤ 1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)) := by
        have hRY : Nat.log 2 (RE e) ≤ Nat.log 2 (YE K e) := by
          rw [natLog_RE, natLog_YE]; exact Nat.pow_le_pow_right (by norm_num) (e_le_mE K e)
        have hRpos : (0 : ℝ) < Nat.log 2 (RE e) := by
          rw [natLog_RE]; positivity
        have hRY' : (Nat.log 2 (RE e) : ℝ) ≤ (Nat.log 2 (YE K e) : ℝ) := by exact_mod_cast hRY
        have := Real.log_le_log hRpos hRY'
        linarith
      gcongr
    have hsamp : 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz ≤ a ^ 8 / 4 := by
      have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
      have hL1sq : (rowL1 b K) ^ 2 ≤ (a ^ 2 / 2) ^ 2 := by gcongr
      calc 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz
          = 2 * (rowL1 b K) ^ 2 * ((YE K e : ℝ) ^ 2 / Psz) := by ring
        _ ≤ 2 * (a ^ 2 / 2) ^ 2 * ((1 / 2 : ℝ) ^ K / 2) := by gcongr
        _ = a ^ 8 / 4 := by rw [h2K]; ring
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have ha8 : 0 ≤ a ^ 8 := by positivity
    calc 4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * rowL2 b K
          + 2 * (YE K e : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 8 / 8) + a ^ 8 / 4 := add_le_add hfac hsamp
      _ ≤ 4 * (K : ℝ) ^ 2 * a ^ 8 := by nlinarith
      _ = (2 * K * a ^ 4) ^ 2 := by ring
  -- the third term
  have ht3 : (Real.log ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (YE K e)) * rowL1 b K
      ≤ 51 * a ^ 2 := by
    have := log_Mx_div_leE h
    have hl : 0 ≤ Real.log ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (YE K e) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hX1 : (1 : ℝ) ≤ XE K e := by unfold XE; exact_mod_cast Nat.one_le_two_pow
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (Sched.N K)) : (0 : ℝ) ≤ _)
        nlinarith
      · apply Real.log_nonneg; unfold YE; push_cast; exact one_le_pow₀ (by norm_num)
    calc (Real.log ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (YE K e)) * rowL1 b K
        ≤ 101 * (a ^ 2 / 2) := by gcongr
      _ ≤ 51 * a ^ 2 := by nlinarith
  -- close: `2K a⁴ ≤ (1/16)(1/K) a` and `51 a² ≤ (1/16)(1/K) a`
  have hc1 : 2 * K * a ^ 4 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (32 : ℝ) * K ^ 2 * a ^ 3 ≤ 1 := by
      have e : a ^ 3 = 1 / (2 : ℝ) ^ (3 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  have hc2 : 51 * a ^ 2 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (816 : ℝ) * K * a ≤ 1 := by
      have e : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  calc _ ≤ 2 * K * a ^ 4 + 51 * a ^ 2 := add_le_add hsq ht3
    _ ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) + (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := add_le_add hc1 hc2
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

/-- **`hfar` in base `b ≥ 3`**, against `η = 2^{−k₄}`. -/
theorem hfar_holdsE {b K k₄ e : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K / Real.log 2 * farBound b (K + Sched.N K) (farC (gridOf K (Sched.N K) h.hK1) (XE K e) (gridDm K (Sched.N K)))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.base.hb; have hK := h.base.hK
  have hfarC := farC_leE h
  have hfar0 := farC_nonneg (gridOf K (Sched.N K) h.hK1) (XE K e) (sample_nonemptyE h) (gridDm K (Sched.N K))
  set C := farC (gridOf K (Sched.N K) h.hK1) (XE K e) (gridDm K (Sched.N K)) with hC
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
  have hfb := farBound_le_three hb (K + Sched.N K) hfar0
  -- the bracket at `b = 3` is at most `A/2`
  set A : ℕ := logP₀Nat K + mE K e + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + Sched.N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2 ≤ (A : ℝ) / 2 := by
    have hJ : (J K : ℝ) = K + Sched.N K := by unfold J; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hN := four_mul_le_two_pow_NE h
  have hNr : (4 : ℝ) * K * A ≤ (2 : ℝ) ^ Sched.N K := by exact_mod_cast hN
  have h3N : (2 : ℝ) ^ Sched.N K ≤ (3 : ℝ) ^ Sched.N K := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq : (1 / 3 : ℝ) ^ Sched.N K * (A : ℝ) ≤ 1 / (4 * K) := by
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by rw [← mul_pow]; norm_num
  have h23a := two_thirds_pow_le (k₄ := k₄) hK4
  have hA0 : (0 : ℝ) ≤ A := by positivity
  calc (2 : ℝ) ^ K / Real.log 2 * farBound b (K + Sched.N K) C
      ≤ (2 : ℝ) ^ K / Real.log 2 * farBound 3 (K + Sched.N K) C := by gcongr
    _ = (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + Sched.N K)
          * ((C + 2 * (K + Sched.N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2)) := by
        unfold farBound; push_cast; ring_nf
    _ ≤ (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + Sched.N K) * ((A : ℝ) / 2)) := by gcongr
    _ = (2 / 3 : ℝ) ^ K * ((1 / 3 : ℝ) ^ Sched.N K * A) / (2 * Real.log 2) := by
        rw [pow_add, ← h23]; field_simp
    _ ≤ a ^ 2 * (1 / (4 * K)) / (2 * (2 / 3)) := by
        gcongr
    _ = a * a * (3 / (16 * K)) := by field_simp; ring
    _ ≤ a * (1 / 2) * (3 / (16 * K)) := by gcongr
    _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
        rw [show (1 / 8 : ℝ) * ((1 / K : ℝ) * a) = a * (1 / (8 * K)) by field_simp]
        have : (1 / 2 : ℝ) * (3 / (16 * K)) ≤ 1 / (8 * K) := by
          rw [show (1 / 2 : ℝ) * (3 / (16 * K)) = 3 / (32 * K) by field_simp; ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        nlinarith


/-! ### The schedule's outer dimension at a free `k₄` -/

/-- `M = ⌈K log 2 / (4 ℓ log b)⌉`, at a free outer dimension `K`. -/
noncomputable def MG (b ℓ K : ℕ) : ℕ :=
  ⌈(K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b)⌉₊

lemma MG_lo {b ℓ K : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    (K : ℝ) / 4 * Real.log 2 ≤ (MG b ℓ K : ℝ) * ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have h := Nat.le_ceil ((K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b))
  unfold MG
  rw [div_le_iff₀ hden] at h
  nlinarith

lemma MG_hi {b ℓ K : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    (MG b ℓ K : ℝ) * ℓ * Real.log b ≤ (K : ℝ) / 4 * Real.log 2 + ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have hnn : 0 ≤ (K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b) := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
  have h := Nat.ceil_lt_add_one hnn
  unfold MG
  have h' : (⌈(K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b)⌉₊ : ℝ) * (4 * ℓ * Real.log b)
      < (K : ℝ) * Real.log 2 + 4 * ℓ * Real.log b := by
    have := mul_lt_mul_of_pos_right h hden
    rwa [add_mul, div_mul_cancel₀ _ hden.ne', one_mul] at this
  nlinarith [h']

/-- `hM`: `b^{−ℓM} ≤ 2^{−k₄}`. -/
lemma hM_holdsG {b ℓ K k₄ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (hK4 : K = 4 * k₄) :
    1 / ((b : ℝ) ^ ℓ) ^ MG b ℓ K ≤ (1 / 2 : ℝ) ^ k₄ := by
  have hbr : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hlo := MG_lo (K := K) hb hℓ
  have hK4' : (K : ℝ) / 4 = k₄ := by rw [hK4]; push_cast; ring
  rw [hK4'] at hlo
  have e1 : ((b : ℝ) ^ ℓ) ^ MG b ℓ K = Real.exp ((MG b ℓ K : ℝ) * ℓ * Real.log b) := by
    rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    push_cast; ring_nf
  have e2 : (2 : ℝ) ^ k₄ = Real.exp ((k₄ : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [one_div_pow, e1, one_div, one_div, e2]
  exact inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.2 hlo)


/-- Enlarging `k₄` keeps the `hB` size hypothesis. -/
lemma KG_ge {b ℓ k₄ : ℕ} (hk : k₄bℓ b ℓ ≤ k₄) :
    8464 * ℓ ^ 2 * b ^ (2 * ℓ) * Nat.clog 2 b ^ 2 ≤ 4 * k₄ :=
  Kbℓ_ge.trans (Nat.mul_le_mul_left _ hk)

/-- Enlarging `k₄` keeps the standing schedule hypotheses. -/
lemma hyp_KG {b ℓ k₄ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (hk : k₄bℓ b ℓ ≤ k₄) :
    Hyp b (4 * k₄) := by
  have h := hyp_Kbℓ hb hℓ
  have hKle : Kbℓ b ℓ ≤ 4 * k₄ := Nat.mul_le_mul_left _ hk
  exact ⟨h.hb, le_trans h.hbK hKle, le_trans h.hK hKle⟩

/-! ### The `S`-restricted schedule witness at a free cutoff -/

lemma RE_le_YE (K e : ℕ) : RE e ≤ YE K e :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (e_le_mE K e))

variable (S : ℕ → Prop) [DecidablePred S]

/-- **The prime-subset schedule witness in base `b ≥ 3`**, at any cutoff exponent `e` admissible
for the schedule (`HypE`) at which the `S`-restricted small primes still meet the schedule's
Mertens demand (`hlow`).  Every field except `hbudget` is the base-`b` witness at the inflated
cutoff; `hbudget` is `hbudget_holdsE_gen` applied to the `S`-filtered small primes. -/
noncomputable def scheduleWitnessSE (b ℓ w e k₄ : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ)
    (hk : k₄bℓ b ℓ ≤ k₄)
    (hE : HypE b (4 * k₄) e)
    (hlow : (m₁ b (4 * k₄) : ℝ) * Real.log 2 - 21 * ((4 * k₄ : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e)
          (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1).P₀).filter S, (p : ℝ)⁻¹) :
    ScheduleWitnessS S b ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp b K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (Sched.N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    X := XE K e
    hne := sample_nonemptyE hE
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := MG b ℓ K
    hM := hM_holdsG hb hℓ hK4
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (Sched.N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (Sched.N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := b) (by omega) hℓ (KG_ge hk) (MG_lo hb hℓ) (MG_hi hb hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := RE e
    hR := RE_ge_two e
    Y := YE K e
    hRY := RE_le_YE K e
    D := Dj K k₄
    hN := hN_holds (by omega) hK4 hK100
    Mc := McE K e
    hMc := McE_pos hE
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    Mx := ((XE K e + J K * gridDm K (Sched.N K) : ℕ) : ℝ)
    hMx1 := by
      have : 1 ≤ XE K e := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    hMx := fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    Dm := gridDm K (Sched.N K)
    hDm := gridOf.d_le hK1
    δbig := 1 / 8
    δfar := 1 / 8
    hbig := hbig_holdsE hK4 hE
    hfar := hfar_holdsE hK4 hE
    hbudget := by
      have hsub : (smallPrimes (RE e) (gridOf K (Sched.N K) hK1).P₀).filter S
          ⊆ smallPrimes (RE e) (gridOf K (Sched.N K) hK1).P₀ := Finset.filter_subset _ _
      have hbud := hbudget_holdsE_gen (k₄ := k₄) hK4 hE hsub hlow
      have hc : Fintype.card (gridOf K (Sched.N K) hK1).Idx = T K := gridOf.card_Idx hK1
      rw [← hc] at hbud
      exact hbud }


end SchedB

end NormalNumbers.G4
