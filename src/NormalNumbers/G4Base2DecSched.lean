/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBE2
import NormalNumbers.G4Base2Sched
import NormalNumbers.G4SubsetWitnessCovS

/-!
# The base-2 schedule on the decoupled frame `HypE2`

`G4Base2Sched` at a cutoff `e` and an independent moment parameter `s`: `hbig` and `hbudget`
carry over verbatim (they never used the moment cap), and `hfar` is redone through the
`S`-restricted far-tail constant `farCS`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

namespace Dec

open Sched (N J T logP₀Nat m₂ Dj)

theorem hbig_two {K k₄ e s x : ℕ} (hK4 : K = 4 * k₄) (h : HypE2 3 K e s)
    (hx : 100 * 2 ^ mE K e ≤ x) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)))
          * rowL2 ((2 : ℕ) : ℝ) K
        + 2 * (YE K e : ℝ) ^ 2 * (rowL1 ((2 : ℕ) : ℝ) K) ^ 2
          / ((apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ))
      + Real.sqrt (rowL2 ((2 : ℕ) : ℝ) K * 20000 + rowL1 ((2 : ℕ) : ℝ) K ^ 2 * (1 / 2 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  rw [rowL1_two', rowL2_two']
  set G := gridOf K (N K) h.hK1 with hG
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha4 : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4, mul_comm]
  rw [ha4]
  have hfac := dyadic_factor_leE K e
  -- the sample term
  set m := mE K e with hm
  have hKm : K ≤ 2 ^ m := by
    have : K * (K ^ 2) ^ K ≤ 2 ^ m := Kr_le_two_pow_mE h
    have : K ≤ K * (K ^ 2) ^ K := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hP₀ : (G.P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m) := P₀_le_two_powE h
  have hP₀pos : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXle : 2 * G.P₀ ≤ 2 ^ x := by
    have h1 : ((2 * G.P₀ : ℕ) : ℝ) ≤ ((2 ^ x : ℕ) : ℝ) := by
      push_cast
      calc 2 * (G.P₀ : ℝ) ≤ 2 * (2 : ℝ) ^ (2 * 2 ^ m) := by gcongr
        _ = (2 : ℝ) ^ (2 * 2 ^ m + 1) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ x := pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast h1
  have hcard := Sched.card_apSample_ge_half (2 ^ x) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ hXle
  have hcard0 : (0 : ℝ) < (apSample (2 ^ x) G.P₀ G.b₀).card := by
    refine lt_of_lt_of_le ?_ hcard; push_cast; positivity
  have hY : (YE K e : ℝ) = (2 : ℝ) ^ (2 ^ m) := by unfold YE; push_cast; rfl
  have hsamp : 2 * (YE K e : ℝ) ^ 2 * 1 ^ 2 / (apSample (2 ^ x) G.P₀ G.b₀).card ≤ a ^ 4 := by
    rw [div_le_iff₀ hcard0, hY]
    have h2x : (2 : ℝ) ^ x ≥ (2 : ℝ) ^ (100 * 2 ^ m) := pow_le_pow_right₀ (by norm_num) hx
    have hc' : (2 : ℝ) ^ x / (2 * G.P₀) ≤ (apSample (2 ^ x) G.P₀ G.b₀).card := by
      have := hcard; push_cast at this; exact this
    -- `a⁴ · 2^x/(2P₀) ≥ 2·Y²`
    have key : 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀) ≤ a ^ 4 * (2 : ℝ) ^ x := by
      have e1 : 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * (2 : ℝ) ^ (2 * 2 ^ m))
          = (2 : ℝ) ^ (4 * 2 ^ m + 2) := by
        rw [← pow_mul]; rw [show 4 * 2 ^ m + 2 = 2 ^ m * 2 + 2 * 2 ^ m + 2 by ring]
        rw [pow_add, pow_add]; ring
      have e2 : a ^ 4 * (2 : ℝ) ^ (K + (4 * 2 ^ m + 2)) = (2 : ℝ) ^ (4 * 2 ^ m + 2) := by
        rw [← ha4, pow_add, ← mul_assoc, ← mul_pow]; norm_num
      calc 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀)
          ≤ 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * (2 : ℝ) ^ (2 * 2 ^ m)) := by gcongr
        _ = a ^ 4 * (2 : ℝ) ^ (K + (4 * 2 ^ m + 2)) := by rw [e1, e2]
        _ ≤ a ^ 4 * (2 : ℝ) ^ x := by
            gcongr
            · norm_num
            · omega
    have hP2 : (0 : ℝ) < 2 * G.P₀ := by positivity
    calc 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * 1 ^ 2 = 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀) / (2 * G.P₀) := by
          field_simp
      _ ≤ a ^ 4 * (2 : ℝ) ^ x / (2 * G.P₀) := by gcongr
      _ = a ^ 4 * ((2 : ℝ) ^ x / (2 * G.P₀)) := by ring
      _ ≤ a ^ 4 * (apSample (2 ^ x) G.P₀ G.b₀).card := by gcongr
  -- term 1 ≤ 4K a², term 2 ≤ 84 a²
  have ht1 : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)))
        * (a ^ 4 / 3) + 2 * (YE K e : ℝ) ^ 2 * 1 ^ 2 / (apSample (2 ^ x) G.P₀ G.b₀).card)
      ≤ 4 * K * a ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hf0 : 0 ≤ 1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)) := by
      have h1 : Real.log (Nat.log 2 (RE e)) ≤ Real.log (Nat.log 2 (YE K e)) := by
        rw [natLog_YE, natLog_RE]
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (e_le_mE K e)
      linarith
    have : 4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * (a ^ 4 / 3)
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 4 / 3) := by gcongr
    have ha4' : 0 ≤ a ^ 4 := by positivity
    have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hK2 ha4'
    have e : (4 * (K : ℝ) * a ^ 2) ^ 2 = 16 * (K : ℝ) ^ 2 * a ^ 4 := by ring
    rw [e]
    nlinarith
  have ht2 : Real.sqrt (a ^ 4 / 3 * 20000 + 1 ^ 2 * a ^ 4) ≤ 84 * a ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have ha4' : 0 ≤ a ^ 4 := by positivity
    nlinarith
  have hfin : 4 * K * a ^ 2 + 84 * a ^ 2 ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
    have hb := sq_le_two_pow' hk
    have hbr : (2048 : ℝ) * k₄ ^ 2 ≤ 2 ^ k₄ := by exact_mod_cast hb
    have e : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show (1 / 8 : ℝ) * ((1 / K : ℝ) * a) = a / (8 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have : (4 * K + 84) * 8 * K * a ≤ 1 := by
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      have hk' : (25 : ℝ) ≤ k₄ := by exact_mod_cast hk
      nlinarith
    nlinarith
  linarith

/-- **`hfar` at `b = 2` from any far-tail constant `C ≤ 2^{40K²}`.** -/
theorem hfar_of_C {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ (2 : ℝ) ^ (40 * K ^ 2)) :
    (2 : ℝ) ^ K / Real.log 2 * farBound ((2 : ℕ) : ℝ) (K + N K) C
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hNK : N K = 100 * K ^ 2 := rfl
  have e1 : (2 : ℝ) ^ K / Real.log 2 * farBound ((2 : ℕ) : ℝ) (K + N K) C
      = (C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2) / (2 ^ N K * Real.log 2) := by
    unfold farBound
    push_cast
    rw [one_div_pow, pow_add]
    field_simp
    ring
  rw [e1, div_le_iff₀ (by positivity)]
  -- `C + 2J + 4 ≤ 2^{40K²+1}`
  have hJ : (2 : ℝ) * ((K + N K : ℕ) : ℝ) + 4 ≤ 8 * (2 : ℝ) ^ (40 * K ^ 2) := by
    have h1 : 40 * K ^ 2 < 2 ^ (40 * K ^ 2) := Nat.lt_two_pow_self
    have h2 : 2 * (K + N K) + 4 ≤ 8 * (40 * K ^ 2) := by rw [hNK]; nlinarith
    have : 2 * (K + N K) + 4 ≤ 8 * 2 ^ (40 * K ^ 2) := by omega
    exact_mod_cast this
  have hnum : C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2 ≤ (2 : ℝ) ^ (40 * K ^ 2 + 4) := by
    rw [pow_add]; linarith
  -- `8K·2^{k₄} ≤ 2^{2K}`
  have hKk : 8 * K * 2 ^ k₄ ≤ 2 ^ (2 * K + 3) := by
    have h1 : 8 * K ≤ 2 ^ (K + 3) := by
      have := Nat.lt_two_pow_self (n := K)
      rw [pow_add]; omega
    have h2 : 2 ^ k₄ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 8 * K * 2 ^ k₄ ≤ 2 ^ (K + 3) * 2 ^ K := Nat.mul_le_mul h1 h2
      _ = 2 ^ (2 * K + 3) := by rw [← pow_add]; ring_nf
  have hKkr : (8 : ℝ) * K * 2 ^ k₄ ≤ (2 : ℝ) ^ (2 * K + 3) := by exact_mod_cast hKk
  have hexp : 2 * K + 3 + (40 * K ^ 2 + 4) + 1 ≤ N K := by rw [hNK]; nlinarith
  have hbig : (2 : ℝ) ^ (2 * K + 3) * (2 : ℝ) ^ (40 * K ^ 2 + 4) * 2 ≤ 2 ^ N K := by
    rw [← pow_add, ← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hexp
  have ha : (1 / 2 : ℝ) ^ k₄ * 2 ^ k₄ = 1 := by rw [← mul_pow]; norm_num
  have hKpos : (0 : ℝ) < K := by linarith
  have hpk : (0 : ℝ) < 2 ^ k₄ := by positivity
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with hadef
  have hnum0 : 0 ≤ C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2 := by positivity
  -- RHS ≥ a/(8K)·2^N·(2/3) ≥ a/(8K)·(8K·2^{k₄})·2^{40K²+1}·(4/3) ≥ numerator
  have h1 : (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * (2 ^ N K * Real.log 2)
      ≥ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * ((8 * K * 2 ^ k₄) * (2 : ℝ) ^ (40 * K ^ 2 + 4) * 2 * (2 / 3)) := by
    gcongr
    calc (8 * (K : ℝ) * 2 ^ k₄) * (2 : ℝ) ^ (40 * K ^ 2 + 4) * 2
        ≤ (2 : ℝ) ^ (2 * K + 3) * (2 : ℝ) ^ (40 * K ^ 2 + 4) * 2 := by gcongr
      _ ≤ 2 ^ N K := hbig
  have e2 : (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * ((8 * K * 2 ^ k₄) * (2 : ℝ) ^ (40 * K ^ 2 + 4) * 2 * (2 / 3))
      = (4 / 3) * (a * 2 ^ k₄) * (2 : ℝ) ^ (40 * K ^ 2 + 4) := by field_simp; ring
  rw [e2, ha] at h1
  have : (0 : ℝ) ≤ (2 : ℝ) ^ (40 * K ^ 2 + 4) := by positivity
  linarith

/-- `log((2^x + Dm)/|P|) ≤ 2 + logP₀Nat K` at a sample above `XE`. -/
theorem log_sample_le {b K e s x : ℕ} (h : HypE2 b K e s) (hx1 : 100 * 2 ^ mE K e ≤ x) :
    Real.log (((2 ^ x + gridDm K (N K) : ℕ) : ℝ)
        / (apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card)
      ≤ 2 + logP₀Nat K := by
  set G := gridOf K (N K) h.hK1 with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXE : XE K e ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx1
  have h2P : 2 * G.P₀ ≤ 2 ^ x := (two_mul_P₀_le_XE h).trans hXE
  have hcard := Sched.card_apSample_ge_half (2 ^ x) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ h2P
  have hcard0 : (0 : ℝ) < (apSample (2 ^ x) G.P₀ G.b₀).card := by
    refine lt_of_lt_of_le ?_ hcard; push_cast; positivity
  have hDm : gridDm K (N K) ≤ 2 ^ x := (gridDm_le_XE h).trans hXE
  have hDmX : (gridDm K (N K) : ℝ) ≤ ((2 ^ x : ℕ) : ℝ) := by exact_mod_cast hDm
  have hP₀exp := Sched.P₀_le_exp (K := K) h.hK1
  have h1 : (((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    have hc' : ((2 ^ x : ℕ) : ℝ) / (2 * G.P₀) ≤ (apSample (2 ^ x) G.P₀ G.b₀).card := hcard
    push_cast at hDmX hc'
    calc (2 : ℝ) ^ x + gridDm K (N K) ≤ 2 * 2 ^ x := by linarith
      _ = 4 * G.P₀ * ((2 : ℝ) ^ x / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (2 ^ x) G.P₀ G.b₀).card := by gcongr
  have hpos : (0 : ℝ) < ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card := by
    push_cast; positivity
  calc Real.log (((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card)
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

/-- `logP₀Nat K + 2 ≤ 2^{39K²}`. -/
lemma logP₀Nat_add_two_le {K : ℕ} (hK : 100 ≤ K) : logP₀Nat K + 2 ≤ 2 ^ (39 * K ^ 2) := by
  have h1 := Sched.logP₀Nat_le hK
  have h2 : K ^ (20 * K + 17) ≤ (2 ^ K) ^ (20 * K + 17) :=
    Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h3 : (2 ^ K) ^ (20 * K + 17) = 2 ^ (K * (20 * K + 17)) := by rw [← pow_mul]
  have h4 : 2 ^ (K * (20 * K + 17)) * 2 ≤ 2 ^ (39 * K ^ 2) := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h5 : 2 ≤ 2 ^ (K * (20 * K + 17)) :=
    Nat.one_lt_two_pow (by positivity)
  rw [h3] at h2
  omega

/-- **`hfar` at `b = 2` through `farCS`**, given `F_S(2^x + Dm) ≤ 2^{39K²}`. -/
theorem hfar_twoS (S : ℕ → Prop) [DecidablePred S] {K k₄ e s x : ℕ} (hK4 : K = 4 * k₄)
    (h : HypE2 3 K e s) (hx1 : 100 * 2 ^ mE K e ≤ x)
    (hFS : MertensAP.sumInvPrimesIn S (2 ^ x + gridDm K (N K)) ≤ (2 : ℝ) ^ (39 * K ^ 2)) :
    (2 : ℝ) ^ K / Real.log 2 * farBound ((2 : ℕ) : ℝ) (K + N K)
        (farCS S (gridOf K (N K) h.hK1) (2 ^ x) (gridDm K (N K)))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hK := h.base.hK
  have hne : (apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).Nonempty := by
    obtain ⟨n, hn⟩ := sample_nonemptyE h
    exact ⟨n, apSample_mono (Nat.pow_le_pow_right (by norm_num) hx1) _ _ hn⟩
  refine hfar_of_C hK4 hK (farCS_nonneg S _ _ hne _) ?_
  have hl := log_sample_le h hx1
  have hL : ((logP₀Nat K + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (39 * K ^ 2) := by
    exact_mod_cast logP₀Nat_add_two_le hK
  unfold farCS
  push_cast at hL
  have : (2 : ℝ) ^ (40 * K ^ 2) = (2 : ℝ) ^ (39 * K ^ 2) * 2 ^ (K ^ 2) := by
    rw [← pow_add]; ring_nf
  have h1 : (2 : ℝ) ≤ 2 ^ (K ^ 2) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (K ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.one_le_pow _ _ (by omega))
  have h0 : (0 : ℝ) ≤ 2 ^ (39 * K ^ 2) := by positivity
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

variable (S : ℕ → Prop) [DecidablePred S]

/-- **`hbudget` at `b = 2`**, at the sample `2^x ≥ XE`, from the `b = 3` budget. -/
theorem hbudget_two {K k₄ e s x : ℕ} (hK4 : K = 4 * k₄) (h : HypE2 3 K e s)
    (hx1 : 100 * 2 ^ mE K e ≤ x)
    (hlow : (m₁ 3 K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S, (p : ℝ)⁻¹)
    (hsum : ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S, (p : ℝ)⁻¹
      ≤ 3 * (s : ℝ) + 5) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound ((smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S)
            (Fintype.card (gridOf K (N K) h.hK1).Idx) (RE e) (McE K s)
            (apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed ((2 : ℕ) : ℝ) K) < 1 := by
  have hsub : (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S
      ⊆ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀ := Finset.filter_subset _ _
  have hbud := hbudget_holdsE_gen (k₄ := k₄) hK4 h hsub hlow hsum
  have hc : Fintype.card (gridOf K (N K) h.hK1).Idx = T K := gridOf.card_Idx h.hK1
  rw [hc]
  refine lt_of_le_of_lt ?_ hbud
  gcongr
  apply smallPrimeBound_anti
  · exact (sample_nonemptyE h).card_pos
  · exact Finset.card_le_card (apSample_mono (Nat.pow_le_pow_right (by norm_num) hx1) _ _)
  · exact freqSeed_three_le_two K
  · intro p hp
    exact (mem_smallPrimes.1 (hsub hp)).1.pos

/-- **The base-2 schedule witness on the decoupled frame.**  The `b = 3` parameter layer at cutoff `e`, the base-2
cylinder count, and a very-large covariance bound at a sample `2^x`, `x ∈ [100, 101]·2^{mE}`. -/
noncomputable def scheduleWitnessSCS2 (ℓ w e s k₄ x : ℕ) (hℓ : 1 ≤ ℓ) (hk : k₄bℓ 3 ℓ ≤ k₄)
    (hE : HypE2 3 (4 * k₄) e s)
    (hlow : (m₁ 3 (4 * k₄) : ℝ) * Real.log 2 - 21 * ((4 * k₄ : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e)
          (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1).P₀).filter S, (p : ℝ)⁻¹)
    (hsum : ∑ p ∈ (smallPrimes (RE e)
          (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ ≤ 3 * (s : ℝ) + 5)
    (hFS : MertensAP.sumInvPrimesIn S (2 ^ x + gridDm (4 * k₄) (Sched.N (4 * k₄)))
      ≤ (2 : ℝ) ^ (39 * (4 * k₄) ^ 2))
    (hx1 : 100 * 2 ^ mE (4 * k₄) e ≤ x) (hx2 : x ≤ 101 * 2 ^ mE (4 * k₄) e)
    (hcov : VeryLargeCov S (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1) (2 ^ x) (YE (4 * k₄) e) 20000
      ((1 / 2 : ℝ) ^ (4 * k₄))) :
    ScheduleWitnessSCS S 2 ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp 3 K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    X := 2 ^ x
    hne := by
      obtain ⟨n, hn⟩ := sample_nonemptyE hE
      exact ⟨n, apSample_mono (Nat.pow_le_pow_right (by norm_num) hx1) _ _ hn⟩
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := MG 2 ℓ K
    hM := hM_holds' (b := 2) (le_refl 2) hℓ hK4
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := 2) (le_refl 2) hℓ (KG_ge_two hk)
        (MG_lo' (K := 4 * k₄) (le_refl 2) hℓ) (MG_hi' (K := 4 * k₄) (le_refl 2) hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := RE e
    hR := RE_ge_two e
    Y := YE K e
    hRY := RE_le_YE K e
    D := Dj K k₄
    hN := hN_holds (b := 2) (le_refl 2) hK4 hK100
    Mc := McE K s
    hMc := McE_pos hE
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    V := 20000
    κ := (1 / 2 : ℝ) ^ K
    hV := by norm_num
    hκ := by positivity
    hcov := hcov
    Dm := gridDm K (N K)
    hDm := gridOf.d_le hK1
    δbig := 1 / 8
    δfar := 1 / 8
    hbig := hbig_two (x := x) hK4 hE hx1
    hfar := hfar_twoS S (x := x) hK4 hE hx1 hFS
    hbudget := hbudget_two S (x := x) hK4 hE hx1 hlow hsum }

end Dec

end SchedB

end NormalNumbers.G4
