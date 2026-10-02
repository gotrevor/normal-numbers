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

end Dec

end SchedB

end NormalNumbers.G4
