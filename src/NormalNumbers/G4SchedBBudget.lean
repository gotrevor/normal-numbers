/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBParams

/-!
# G4B §5: **`hbudget`** in base `b` — the closed budget `δ₁ + δ₂ + 2κ + Λδ₃ < 1`

Same shape as `G4ScheduleBudget`, with the seed `θ₀ = freqSeed b K = b^{−4}(2/b²)^K` and
`m₁ = 1000·b^{2K+4}·K^{2K+1}`, so that `θ₀·m₁ = 1000·2^K·Kr` — the main term is *better*
than at base four.  Terms (a)–(d) are the same text (`m₁` enters them only through the ladder
and through `Mc = 10⁵·T·m₁`).
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J W H T logP₀Nat m₂ Dj T_pos exp_one_le two_le_exp_one exp_neg_four_le
  exp_thirteen_half_le four_e_div_thirteen_le six_sevenths_pow_le prod_one_add_le_exp_sum
  two_pow_le_exp jackson_term_le Lambda_le budget_assembly card_small_subsets_le
  card_smallPrimes_le twentyone_sq_add_four_le)

section terms

variable {b K : ℕ}

lemma freqSeed_le_quarter_pow {b : ℕ} (hb : 3 ≤ b) (K : ℕ) :
    freqSeed b K ≤ (1 / 4 : ℝ) ^ K := by
  unfold freqSeed
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (1 : ℝ) / (b : ℝ) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by linarith)
  have h2 : (2 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hbr hbr (by norm_num) (by linarith)]
  have h3 : (0 : ℝ) ≤ 2 / (b : ℝ) ^ 2 := by positivity
  calc 1 / (b : ℝ) ^ 4 * (2 / (b : ℝ) ^ 2) ^ K ≤ 1 * (1 / 4 : ℝ) ^ K := by
        gcongr
    _ = (1 / 4 : ℝ) ^ K := one_mul _

lemma sq_le_two_pow {K : ℕ} (hK : 4 ≤ K) : K ^ 2 ≤ 2 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := this
      _ ≤ 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

lemma twentyone_sq_add_four_le_four_pow {K : ℕ} (hK : 100 ≤ K) : 21 * K ^ 2 + 4 ≤ 4 ^ K := by
  have h1 := sq_le_two_pow (K := K) (by omega)
  have h2 : 25 ≤ 2 ^ K := by
    calc 25 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (4 : ℕ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  rw [h3]
  have : 21 * K ^ 2 + 4 ≤ 25 * K ^ 2 := by nlinarith
  calc 21 * K ^ 2 + 4 ≤ 25 * K ^ 2 := this
    _ ≤ 2 ^ K * 2 ^ K := Nat.mul_le_mul h2 h1

/-- `θ₀ · m₁ = 1000 · 2^K · Kr`. -/
lemma freqSeed_mul_m₁ {b : ℕ} (hb : 3 ≤ b) (K : ℕ) :
    freqSeed b K * m₁ b K = 1000 * (2 : ℝ) ^ K * (K * ((K ^ 2) ^ K : ℕ)) := by
  unfold freqSeed m₁
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  push_cast
  have e1 : (b : ℝ) ^ (2 * K + 4) = ((b : ℝ) ^ 2) ^ K * (b : ℝ) ^ 4 := by
    rw [← pow_mul, ← pow_add]
  have e2 : (K : ℝ) ^ (2 * K + 1) = K * ((K : ℝ) ^ 2) ^ K := by
    rw [← pow_mul, pow_succ]; ring
  rw [e1, e2, div_pow]
  field_simp

/-- main: `Λ·exp(−4θ₀∑1/p) ≤ e^{−4}`, base `b`. -/
lemma main_term_le (h : Hyp b K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * Real.exp (-∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, 4 * freqSeed b K / p)
      ≤ Real.exp (-4) := by
  have hb := h.hb; have hK := h.hK
  have hS := sum_inv_smallPrimes_ge h
  set Sg := ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ with hSgdef
  set θ := freqSeed b K with hθ
  have hθ0 : 0 ≤ θ := freqSeed_nonneg (by exact_mod_cast (show 2 ≤ b by omega)) K
  have hsum : ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, 4 * θ / p = 4 * θ * Sg := by
    rw [hSgdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv]
  rw [hsum]
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set r : ℝ := (((K ^ 2) ^ K : ℕ) : ℝ) with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hKr1 : (1 : ℝ) ≤ K * r := by nlinarith
  have h2K : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hm₁ : θ * m₁ b K = 1000 * (2 : ℝ) ^ K * (K * r) := by rw [hθ, hr]; exact freqSeed_mul_m₁ hb K
  have hsmall : θ * (21 * (K : ℝ) ^ 2 + 4) ≤ 1 := by
    have h := twentyone_sq_add_four_le_four_pow hK
    have h' : (21 * (K : ℝ) ^ 2 + 4) ≤ (4 : ℝ) ^ K := by exact_mod_cast h
    have hθ8 := freqSeed_le_quarter_pow hb K
    calc θ * (21 * (K : ℝ) ^ 2 + 4) ≤ (1 / 4 : ℝ) ^ K * 4 ^ K := by
          gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hS8 : 690 * (K * r) - 1 ≤ θ * Sg := by
    have := mul_le_mul_of_nonneg_left hS hθ0
    have e : θ * (m₁ b K * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4)
        = 1000 * (2 : ℝ) ^ K * (K * r) * Real.log 2 - θ * (21 * (K : ℝ) ^ 2 + 4) := by
      rw [← hm₁]; ring
    rw [e] at this
    have hKr0 : 0 ≤ K * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2K (by norm_num : (0:ℝ) ≤ 1000)) hKr0]
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * r) := by rw [hr]; push_cast; ring
  rw [hcast] at h2
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) * Real.exp (-(4 * θ * Sg))
      ≤ Real.exp (2 * (K * r)) * Real.exp (-(4 * θ * Sg)) := by
        gcongr
    _ = Real.exp (2 * (K * r) - 4 * θ * Sg) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        nlinarith

lemma term_a_le (h : Hyp b K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).powerset.filter
            (fun T' => T'.Nonempty ∧ T'.card ≤ Mc b K)).card : ℝ)
          * (2 ^ Mc b K * (2 * (R b K : ℝ) ^ Mc b K
              / ((apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ))))
      ≤ 1 / 64 := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have hcardN := card_small_subsets_le (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀) (Mc b K)
  have hsmN := card_smallPrimes_le (R b K) (gridOf K (N K) h.hK1).P₀
  have hR2 := R_ge_two b K
  have hcard : ((((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mc b K)).card : ℕ) : ℝ) ≤ Mc b K * (2 * (R b K : ℝ)) ^ Mc b K := by
    have : ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).powerset.filter
        (fun T' => T'.Nonempty ∧ T'.card ≤ Mc b K)).card ≤ Mc b K * (2 * R b K) ^ Mc b K := by
      refine hcardN.trans ?_
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    exact_mod_cast this
  have hinv := inv_card_le h
  have hMc : (Mc b K : ℝ) ≤ 2 ^ Mc b K := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hR2Mc := R_pow_two_Mc_le h
  have hP₀ := P₀_le_two_pow h
  have hX : (X b K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m b K) := by unfold X; push_cast; rfl
  have hXpos : (0 : ℝ) < X b K := by rw [hX]; positivity
  have hP₀0 : (0 : ℝ) ≤ (gridOf K (N K) h.hK1).P₀ := by positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
  set c := ((((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mc b K)).card : ℕ) : ℝ)
  have hΛ0 : 0 ≤ Λ := by positivity
  have hRr : (0 : ℝ) ≤ R b K := by positivity
  calc Λ * (c * (2 ^ Mc b K * (2 * (R b K : ℝ) ^ Mc b K / Psz)))
      = Λ * c * 2 ^ Mc b K * 2 * (R b K : ℝ) ^ Mc b K * (1 / Psz) := by ring
    _ ≤ Λ * (Mc b K * (2 * (R b K : ℝ)) ^ Mc b K) * 2 ^ Mc b K * 2 * (R b K : ℝ) ^ Mc b K
          * (2 * (gridOf K (N K) h.hK1).P₀ / X b K) := by gcongr
    _ = Λ * Mc b K * 2 ^ Mc b K * 2 ^ Mc b K * 4 * (R b K : ℝ) ^ (2 * Mc b K) * (gridOf K (N K) h.hK1).P₀ / X b K := by
        rw [mul_pow, pow_mul (R b K : ℝ) 2 (Mc b K), sq]; ring
    _ ≤ Λ * 2 ^ Mc b K * 2 ^ Mc b K * 2 ^ Mc b K * 4 * (2 : ℝ) ^ (10 * 2 ^ m b K)
          * (2 : ℝ) ^ (2 * 2 ^ m b K) / (2 : ℝ) ^ (100 * 2 ^ m b K) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + Mc b K + Mc b K + Mc b K + 2 + 10 * 2 ^ m b K + 2 * 2 ^ m b K)
          / (2 : ℝ) ^ (100 * 2 ^ m b K) := by
        rw [hΛ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_m h
        omega

lemma term_d_le (h : Hyp b K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / Mc b K) ^ Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ^ Mc b K
          * (2 * (R b K : ℝ) ^ Mc b K / ((apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)))
      ≤ 1 / 64 := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have hsmN := card_smallPrimes_le (R b K) (gridOf K (N K) h.hK1).P₀
  have hR2 := R_ge_two b K
  have hMc1 : (1 : ℝ) ≤ Mc b K := by exact_mod_cast Mc_pos (b := b) (by omega) h.hK1
  have he := exp_one_le
  -- `(2e/Mc)^{Mc}·|sm|^{Mc} ≤ (16R)^{Mc}`
  have hbase : 2 * Real.exp 1 / Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ≤ 16 * R b K := by
    have hsm : ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ≤ 2 * R b K := by
      have : (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card ≤ 2 * R b K := by omega
      exact_mod_cast this
    have hsm0 : (0 : ℝ) ≤ (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card := by positivity
    have h1 : 2 * Real.exp 1 / Mc b K ≤ 2 * Real.exp 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.exp_pos 1]
    have h2 : 2 * Real.exp 1 / Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ)
        ≤ 2 * Real.exp 1 * (2 * R b K) := by
      apply mul_le_mul h1 hsm hsm0 (by positivity)
    nlinarith [Real.exp_pos 1]
  have hpow : (2 * Real.exp 1 / Mc b K) ^ Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ^ Mc b K
      ≤ (2 : ℝ) ^ (4 * Mc b K) * (R b K : ℝ) ^ Mc b K := by
    rw [← mul_pow, pow_mul, show (2 : ℝ) ^ 4 = 16 by norm_num, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hinv := inv_card_le h
  have hR2Mc := R_pow_two_Mc_le h
  have hP₀ := P₀_le_two_pow h
  have hX : (X b K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m b K) := by unfold X; push_cast; rfl
  have hXpos : (0 : ℝ) < X b K := by rw [hX]; positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ)
  set q := (2 * Real.exp 1 / Mc b K) ^ Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ^ Mc b K with hq
  have hq0 : 0 ≤ q := by positivity
  calc Λ * (2 * (2 * Real.exp 1 / Mc b K) ^ Mc b K * ((smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀).card : ℝ) ^ Mc b K
          * (2 * (R b K : ℝ) ^ Mc b K / Psz))
      = Λ * q * 2 * 2 * (R b K : ℝ) ^ Mc b K * (1 / Psz) := by rw [hq]; ring
    _ ≤ Λ * ((2 : ℝ) ^ (4 * Mc b K) * (R b K : ℝ) ^ Mc b K) * 2 * 2 * (R b K : ℝ) ^ Mc b K
          * (2 * (gridOf K (N K) h.hK1).P₀ / X b K) := by gcongr
    _ = Λ * (2 : ℝ) ^ (4 * Mc b K) * 8 * (R b K : ℝ) ^ (2 * Mc b K) * (gridOf K (N K) h.hK1).P₀ / X b K := by
        rw [pow_mul (R b K : ℝ) 2 (Mc b K), sq]; ring
    _ ≤ Λ * (2 : ℝ) ^ (4 * Mc b K) * 8 * (2 : ℝ) ^ (10 * 2 ^ m b K) * (2 : ℝ) ^ (2 * 2 ^ m b K)
          / (2 : ℝ) ^ (100 * 2 ^ m b K) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + 4 * Mc b K + 3 + 10 * 2 ^ m b K + 2 * 2 ^ m b K)
          / (2 : ℝ) ^ (100 * 2 ^ m b K) := by
        rw [hΛ, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_m h
        omega

lemma prod_le_exp_mul_sum (s : Finset ℕ) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    ∏ p ∈ s, (1 + c * (a / p)) ≤ Real.exp (c * a * ∑ p ∈ s, (p : ℝ)⁻¹) := by
  have := prod_one_add_le_exp_sum s (fun p => c * (a / p)) (fun p _ => by positivity)
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv]; ring

lemma term_b_le (h : Hyp b K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((∏ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          / Real.exp 1 ^ Mc b K)
      ≤ Real.exp (-4) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have hS := sum_inv_smallPrimes_le h
  have hprod := prod_le_exp_mul_sum (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀) (Real.exp 1) (2 * (T K : ℝ))
    (Real.exp_pos 1).le (by positivity)
  have he := exp_one_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ m₁ b K := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1.trans (m₁_ge_cube h.hb h.hK1)
  have hKr := Kr_le_T_mul_m₁ h.hb h.hK1
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * m₁ b K := by exact_mod_cast hKr
  have hMc : (Mc b K : ℝ) = 100000 * T K * m₁ b K := by unfold Mc; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹
      ≤ 44 * (T K * m₁ b K) := by
    have : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹
        ≤ Real.exp 1 * (2 * (T K : ℝ)) * (3 * m₁ b K + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos 1, mul_le_mul_of_nonneg_left he hT0]
  rw [Real.exp_one_pow, div_eq_mul_inv, ← Real.exp_neg]
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * ((∏ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          * Real.exp (-(Mc b K : ℝ)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp (Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹)
          * Real.exp (-(Mc b K : ℝ))) := by gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K)
        + Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ - Mc b K) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ m₁ b K),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

lemma term_c_le (h : Hyp b K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mc b K
          * ∏ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (-4) := by
  have hb := h.hb; have hbK := h.hbK; have hK := h.hK
  have hS := sum_inv_smallPrimes_le h
  have hprod := prod_le_exp_mul_sum (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀) (Real.exp (13 / 2)) (T K : ℝ)
    (Real.exp_pos _).le (by positivity)
  have he := exp_thirteen_half_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ m₁ b K := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1.trans (m₁_ge_cube h.hb h.hK1)
  have hKr := Kr_le_T_mul_m₁ h.hb h.hK1
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * m₁ b K := by exact_mod_cast hKr
  have hMc : (Mc b K : ℝ) = 100000 * T K * m₁ b K := by unfold Mc; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹
      ≤ 8800 * (T K * m₁ b K) := by
    have : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹
        ≤ Real.exp (13 / 2) * (T K : ℝ) * (3 * m₁ b K + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos (13 / 2 : ℝ), mul_le_mul_of_nonneg_left he hT0]
  have hlam : (2 * Real.exp 1 / (13 / 2)) ^ Mc b K ≤ Real.exp (-(Mc b K : ℝ) / 7) :=
    (pow_le_pow_left₀ (by positivity) four_e_div_thirteen_le _).trans (six_sevenths_pow_le _)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mc b K
          * ∏ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp 1 * Real.exp (-(Mc b K : ℝ) / 7)
          * Real.exp (Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹)) := by
        gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K) + 1 - Mc b K / 7
        + Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀, (p : ℝ)⁻¹) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ m₁ b K),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-! ### The budget -/

end terms

/-- **The `hbudget` field of `ScheduleWitnessB`**, base `b`, with `δ₁ = δbig = δfar = 1/8`,
`ε = 1/K`, `η = 2^{−k₄}`, `D = Dj K k₄`, `lam' = e`, `lam = 13/2`, `θ₀ = freqSeed b K`. -/
theorem hbudget_holds {b K k₄ : ℕ} (hK4 : K = 4 * k₄) (h : Hyp b K) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound (smallPrimes (R b K) (gridOf K (N K) h.hK1).P₀)
            (T K) (R b K) (Mc b K)
            (apSample (X b K) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed b K) < 1 := by
  have hK := h.hK
  have hk : 25 ≤ k₄ := by omega
  have hJ := jackson_term_le (K := K) (k₄ := k₄) (by omega)
  have hΛ := Lambda_le hK4 hk
  unfold smallPrimeBound
  exact budget_assembly hΛ (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (main_term_le h) (term_a_le h) (term_b_le h)
    (term_c_le h) (term_d_le h) hJ

end SchedB

end NormalNumbers.G4
