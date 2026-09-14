/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleHarmonic

/-!
# G4 §5: **`hbudget`**, the closed budget `δ₁ + δ₂ + 2κ + Λδ₃ < 1`

With `δ₁ = δbig = δfar = 1/8`, `ε = 1/K`, `η = 2^{−k₄}` (`K = 4k₄`), `D = (16K·2^{k₄})²`,
`r = (K²)^K`, `Λ = (2D+1)^r ≤ 4^{Kr}`, and the five terms of `smallPrimeBound` at
`lam' = e`, `lam = 13/2`, `Mc = 10⁵·T·m₁`:

* Jackson: `2κ = 2/(εη√(D+1)) ≤ 1/8`                              (`jackson_term_le`)
* main:    `Λ·exp(−4θ₀ ∑_{sm} 1/p) ≤ e^{−4}`, since `8^{−K}∑ ≥ 690Kr − 1 ≥ 128Kr + 256`
* (a),(d): `≤ 1/64`, since `R^{2Mc} ≤ X^{1/10}`, `P₀ ≤ X^{1/50}`, and `2^{2Kr+4Mc+O(1)} ≤ X^{1/2}`
* (b):     `≤ e^{−4}`, since `2eT·∑ ≤ 44Tm₁ ≪ Mc`
* (c):     `≤ e^{−4}`, since `(4e/13)^{Mc} ≤ e^{−Mc/7}` and `e^{13/2}T∑ ≤ 8800Tm₁ ≪ Mc/7`

Total: `1/8 + 1/4 + 1/8 + (3e^{−4} + 1/32) < 1`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

/-- The Jackson degree `D = (16K·2^{k₄})²`. -/
def Dj (K k₄ : ℕ) : ℕ := (16 * K * 2 ^ k₄) ^ 2

/-! ### Elementary bounds -/

lemma exp_one_le : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
lemma two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]

lemma exp_four_ge : (40 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [Real.exp_one_pow]; norm_num
  rw [this]
  have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  calc (40 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ h0 h.le 4

lemma exp_neg_four_le : Real.exp (-4) ≤ 1 / 40 := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp_four_ge

lemma exp_thirteen_half_le : Real.exp (13 / 2) ≤ 1100 := by
  have h := Real.exp_one_lt_d9
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [Real.exp_one_pow]; norm_num
  calc Real.exp (13 / 2) ≤ Real.exp 7 := Real.exp_le_exp.2 (by norm_num)
    _ = Real.exp 1 ^ 7 := h7
    _ ≤ (2.7182818286 : ℝ) ^ 7 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 7
    _ ≤ 1100 := by norm_num

lemma four_e_div_thirteen_le : 2 * Real.exp 1 / (13 / 2) ≤ 6 / 7 := by
  have := exp_one_le
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma six_sevenths_pow_le (n : ℕ) : (6 / 7 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 7) := by
  have h : (6 / 7 : ℝ) ≤ Real.exp (-1 / 7) := by
    have := Real.add_one_le_exp (-1 / 7 : ℝ)
    linarith
  calc (6 / 7 : ℝ) ^ n ≤ Real.exp (-1 / 7) ^ n := pow_le_pow_left₀ (by norm_num) h n
    _ = Real.exp (n * (-1 / 7)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(n : ℝ) / 7) := by ring_nf

/-- `∏ (1 + f p) ≤ exp (∑ f p)` for `f ≥ 0`. -/
lemma prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, (1 + f i) ≤ Real.exp (∑ i ∈ s, f i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun i hi => by linarith [hf i hi])
    (fun i hi => by linarith [Real.add_one_le_exp (f i)])

lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  calc (2 : ℝ) ^ n ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) two_le_exp_one n
    _ = Real.exp n := Real.exp_one_pow n

/-! ### Sizes -/

lemma Kr_le_m₁ (K : ℕ) : K * (K ^ 2) ^ K ≤ m₁ K := by
  refine le_trans ?_ (m₁_ge K)
  have : K * (K ^ 2) ^ K = K ^ (2 * K + 1) := by rw [← pow_mul]; ring
  rw [this]
  exact Nat.le_mul_of_pos_left _ (by positivity)

lemma m₁_eq (K : ℕ) : (m₁ K : ℝ) = 1000 * 8 ^ K * (K * ((K ^ 2) ^ K : ℕ)) := by
  unfold m₁
  push_cast
  rw [← pow_mul, pow_succ]
  ring

lemma m₁_le_T_mul_m₁ {K : ℕ} (hK : 1 ≤ K) : m₁ K ≤ T K * m₁ K :=
  Nat.le_mul_of_pos_left _ (T_pos hK)

lemma Kr_le_T_mul_m₁ {K : ℕ} (hK : 1 ≤ K) : K * (K ^ 2) ^ K ≤ T K * m₁ K :=
  (Kr_le_m₁ K).trans (m₁_le_T_mul_m₁ hK)

lemma Mc_le_two_pow_m₂ {K : ℕ} (hK : 100 ≤ K) : Mc K ≤ 2 ^ m₂ K := by
  unfold m₂
  calc Mc K ≤ K ^ (6 * K + 9) := Mc_le hK
    _ ≤ 2 ^ (K * (6 * K + 9)) := pow_le_two_pow_mul _ _
    _ ≤ 2 ^ (8 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

lemma Mc_le_two_pow_m {K : ℕ} (hK : 100 ≤ K) : Mc K ≤ 2 ^ m K :=
  (Mc_le_two_pow_m₂ hK).trans (Nat.pow_le_pow_right (by norm_num) (by unfold m; omega))

lemma Kr_le_two_pow_m {K : ℕ} (hK : 100 ≤ K) : K * (K ^ 2) ^ K ≤ 2 ^ m K :=
  (Kr_le_m₁ K).trans ((m₁_le_m K).trans (Nat.lt_two_pow_self).le)

lemma twentyone_sq_add_four_le {K : ℕ} (hK : 100 ≤ K) : 21 * K ^ 2 + 4 ≤ 8 ^ K := by
  have h1 : K ^ 2 ≤ 2 ^ (2 * K) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h2 : 25 ≤ 2 ^ K := by
    calc 25 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (8 : ℕ) ^ K = 2 ^ K * 2 ^ (2 * K) := by
    rw [← pow_add, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]; ring_nf
  rw [h3]
  have : 21 * K ^ 2 + 4 ≤ 25 * K ^ 2 := by nlinarith
  calc 21 * K ^ 2 + 4 ≤ 25 * K ^ 2 := this
    _ ≤ 2 ^ K * 2 ^ (2 * K) := Nat.mul_le_mul h2 h1

/-- `R^{2Mc} ≤ 2^{10·2^m}`. -/
lemma R_pow_two_Mc_le {K : ℕ} (hK : 100 ≤ K) :
    (R K : ℝ) ^ (2 * Mc K) ≤ (2 : ℝ) ^ (10 * 2 ^ m K) := by
  unfold R
  push_cast
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  have h1 := Mc_le_two_pow_m₂ hK
  have h2 : 2 ^ m K = 2 ^ m₁ K * 2 ^ m₂ K := by unfold m; rw [pow_add]
  rw [h2]
  nlinarith [Nat.one_le_two_pow (n := m₁ K)]

lemma R_ge_two (K : ℕ) : 2 ≤ R K := by
  unfold R
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ m₁ K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

/-- `1/|P| ≤ 2P₀/X`. -/
lemma inv_card_le {K : ℕ} (hK : 100 ≤ K) :
    1 / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)
      ≤ 2 * (gridOf K (N K) (by omega)).P₀ / X K := by
  set G := gridOf K (N K) (by omega : 1 ≤ K)
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X K := by unfold X; positivity
  have hcard := card_apSample_ge_half (X K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X hK)
  have hcard0 : (0 : ℝ) < (apSample (X K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  rw [div_le_div_iff₀ hcard0 hXr]
  have := hcard
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-! ### The Jackson term -/

lemma jackson_term_le {K k₄ : ℕ} (hK : 1 ≤ K) :
    2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1))) ≤ 1 / 8 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : (16 * K * 2 ^ k₄ : ℝ) ≤ Real.sqrt ((Dj K k₄ : ℕ) + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    unfold Dj; push_cast; linarith
  have h16 : (16 : ℝ) ≤ (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1) := by
    have e1 : (1 / 2 : ℝ) ^ k₄ * 2 ^ k₄ = 1 := by rw [← mul_pow]; norm_num
    have e2 : (1 / K : ℝ) * K = 1 := by field_simp
    have e3 : (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * (16 * K * 2 ^ k₄)
        = 16 * ((1 / K : ℝ) * K) * ((1 / 2 : ℝ) ^ k₄ * 2 ^ k₄) := by ring
    calc (16 : ℝ) = (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * (16 * K * 2 ^ k₄) := by
          rw [e3, e1, e2]; ring
      _ ≤ _ := by gcongr
  have : 1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)) ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by norm_num) h16
  linarith

/-! ### `Λ ≤ 4^{Kr}` -/

lemma two_Dj_add_one_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 25 ≤ k₄) :
    2 * Dj K k₄ + 1 ≤ 4 ^ K := by
  unfold Dj
  subst hK4
  have h1 : k₄ ^ 2 ≤ 2 ^ (2 * k₄) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h2 : (16 * (4 * k₄) * 2 ^ k₄) ^ 2 = 4096 * k₄ ^ 2 * 2 ^ (2 * k₄) := by
    rw [mul_pow, mul_pow, ← pow_mul]; ring
  rw [h2]
  have h3 : (4 : ℕ) ^ (4 * k₄) = 2 ^ 14 * 2 ^ (2 * k₄) * 2 ^ (2 * k₄) * 2 ^ (4 * k₄ - 14) := by
    rw [← pow_add, ← pow_add, ← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    (congr 1) <;> omega
  rw [h3]
  have h4 : 1 ≤ 2 ^ (4 * k₄ - 14) := Nat.one_le_two_pow
  have h5 : 1 ≤ 2 ^ (2 * k₄) := Nat.one_le_two_pow
  have h6 : 2 * (4096 * k₄ ^ 2 * 2 ^ (2 * k₄)) + 1 ≤ 2 ^ 14 * 2 ^ (2 * k₄) * 2 ^ (2 * k₄) := by
    have : 4096 * k₄ ^ 2 * 2 ^ (2 * k₄) ≤ 4096 * 2 ^ (2 * k₄) * 2 ^ (2 * k₄) := by gcongr
    have : 2 ^ 14 = 16384 := by norm_num
    nlinarith
  calc 2 * (4096 * k₄ ^ 2 * 2 ^ (2 * k₄)) + 1 ≤ 2 ^ 14 * 2 ^ (2 * k₄) * 2 ^ (2 * k₄) := h6
    _ = 2 ^ 14 * 2 ^ (2 * k₄) * 2 ^ (2 * k₄) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

lemma Lambda_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 25 ≤ k₄) :
    (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) := by
  have h := two_Dj_add_one_le hK4 hk
  have : (2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) ≤ 2 ^ (2 * (K * (K ^ 2) ^ K)) := by
    calc (2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) ≤ (4 ^ K) ^ ((K ^ 2) ^ K) := Nat.pow_le_pow_left h _
      _ = 2 ^ (2 * (K * (K ^ 2) ^ K)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  exact_mod_cast this

/-! ### The five terms of `smallPrimeBound` -/

section terms

variable {K : ℕ}

/-- main: `Λ·exp(−4θ₀∑1/p) ≤ e^{−4}`. -/
lemma main_term_le (hK : 100 ≤ K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * Real.exp (-∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, 4 * (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) / p)
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_ge hK
  set Sg := ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ with hSgdef
  have hsum : ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, 4 * (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) / p
      = (1 / 8 : ℝ) ^ K / 64 * Sg := by
    rw [hSgdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv]; ring
  rw [hsum]
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set r : ℝ := (((K ^ 2) ^ K : ℕ) : ℝ) with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hKr1 : (1 : ℝ) ≤ K * r := by nlinarith
  -- `8^{−K}·Σ ≥ 690Kr − 1`
  have h8 : (0 : ℝ) < (1 / 8 : ℝ) ^ K := by positivity
  have hm₁ : (1 / 8 : ℝ) ^ K * m₁ K = 1000 * (K * r) := by
    rw [m₁_eq, hr]
    have : (1 / 8 : ℝ) ^ K * 8 ^ K = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 8 : ℝ) ^ K * (1000 * 8 ^ K * (K * ((K ^ 2) ^ K : ℕ)))
        = ((1 / 8 : ℝ) ^ K * 8 ^ K) * (1000 * (K * ((K ^ 2) ^ K : ℕ))) := by ring
      _ = 1000 * (K * ((K ^ 2) ^ K : ℕ)) := by rw [this, one_mul]
  have hsmall : (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) ≤ 1 := by
    have h := twentyone_sq_add_four_le hK
    have h' : (21 * (K : ℝ) ^ 2 + 4) ≤ (8 : ℝ) ^ K := by exact_mod_cast h
    calc (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) ≤ (1 / 8 : ℝ) ^ K * 8 ^ K := by gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hS8 : 690 * (K * r) - 1 ≤ (1 / 8 : ℝ) ^ K * Sg := by
    have := mul_le_mul_of_nonneg_left hS h8.le
    have e : (1 / 8 : ℝ) ^ K * (m₁ K * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4)
        = 1000 * (K * r) * Real.log 2 - (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) := by
      rw [← hm₁]; ring
    rw [e] at this
    nlinarith
  -- assemble: `2^{2Kr} ≤ e^{2Kr}` and `e^{2Kr − 8^{−K}Σ/64} ≤ e^{−4}`
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * r) := by rw [hr]; push_cast; ring
  rw [hcast] at h2
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) * Real.exp (-((1 / 8 : ℝ) ^ K / 64 * Sg))
      ≤ Real.exp (2 * (K * r)) * Real.exp (-((1 / 8 : ℝ) ^ K / 64 * Sg)) := by
        gcongr
    _ = Real.exp (2 * (K * r) - (1 / 8 : ℝ) ^ K / 64 * Sg) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        nlinarith

/-- The common tail of terms (a) and (d): `2^{e₁}/2^{100·2^m} ≤ 1/64` whenever `e₁ + 6 ≤ 100·2^m`. -/
lemma two_pow_div_le {e₁ : ℕ} (K : ℕ) (h : e₁ + 6 ≤ 100 * 2 ^ m K) :
    (2 : ℝ) ^ e₁ / (2 : ℝ) ^ (100 * 2 ^ m K) ≤ 1 / 64 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  calc (2 : ℝ) ^ e₁ * 64 = (2 : ℝ) ^ (e₁ + 6) := by rw [pow_add]; norm_num
    _ ≤ (2 : ℝ) ^ (100 * 2 ^ m K) := pow_le_pow_right₀ (by norm_num) h
    _ = _ := (one_mul _).symm

lemma sizes_le_two_pow_m (hK : 100 ≤ K) :
    K * (K ^ 2) ^ K ≤ 2 ^ m K ∧ Mc K ≤ 2 ^ m K ∧ 8 ≤ 2 ^ m K := by
  refine ⟨Kr_le_two_pow_m hK, Mc_le_two_pow_m hK, ?_⟩
  have h3 : 3 ≤ K ^ 3 := by
    calc 3 ≤ K := by omega
      _ ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have := m₁_ge_cube (K := K) (by omega)
  have := m₁_le_m K
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m K := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- (a): the residue-transfer term. -/
lemma term_a_le (hK : 100 ≤ K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).powerset.filter
            (fun T' => T'.Nonempty ∧ T'.card ≤ Mc K)).card : ℝ)
          * (2 ^ Mc K * (2 * (R K : ℝ) ^ Mc K
              / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ))))
      ≤ 1 / 64 := by
  have hcardN := card_small_subsets_le (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀) (Mc K)
  have hsmN := card_smallPrimes_le (R K) (gridOf K (N K) (by omega)).P₀
  have hR2 := R_ge_two K
  have hcard : ((((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mc K)).card : ℕ) : ℝ) ≤ Mc K * (2 * (R K : ℝ)) ^ Mc K := by
    have : ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).powerset.filter
        (fun T' => T'.Nonempty ∧ T'.card ≤ Mc K)).card ≤ Mc K * (2 * R K) ^ Mc K := by
      refine hcardN.trans ?_
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    exact_mod_cast this
  have hinv := inv_card_le hK
  have hMc : (Mc K : ℝ) ≤ 2 ^ Mc K := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hR2Mc := R_pow_two_Mc_le hK
  have hP₀ := P₀_le_two_pow hK
  have hX : (X K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
  have hXpos : (0 : ℝ) < X K := by rw [hX]; positivity
  have hP₀0 : (0 : ℝ) ≤ (gridOf K (N K) (by omega)).P₀ := by positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)
  set c := ((((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mc K)).card : ℕ) : ℝ)
  have hΛ0 : 0 ≤ Λ := by positivity
  have hRr : (0 : ℝ) ≤ R K := by positivity
  calc Λ * (c * (2 ^ Mc K * (2 * (R K : ℝ) ^ Mc K / Psz)))
      = Λ * c * 2 ^ Mc K * 2 * (R K : ℝ) ^ Mc K * (1 / Psz) := by ring
    _ ≤ Λ * (Mc K * (2 * (R K : ℝ)) ^ Mc K) * 2 ^ Mc K * 2 * (R K : ℝ) ^ Mc K
          * (2 * (gridOf K (N K) (by omega)).P₀ / X K) := by gcongr
    _ = Λ * Mc K * 2 ^ Mc K * 2 ^ Mc K * 4 * (R K : ℝ) ^ (2 * Mc K) * (gridOf K (N K) (by omega)).P₀ / X K := by
        rw [mul_pow, pow_mul (R K : ℝ) 2 (Mc K), sq]; ring
    _ ≤ Λ * 2 ^ Mc K * 2 ^ Mc K * 2 ^ Mc K * 4 * (2 : ℝ) ^ (10 * 2 ^ m K)
          * (2 : ℝ) ^ (2 * 2 ^ m K) / (2 : ℝ) ^ (100 * 2 ^ m K) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + Mc K + Mc K + Mc K + 2 + 10 * 2 ^ m K + 2 * 2 ^ m K)
          / (2 : ℝ) ^ (100 * 2 ^ m K) := by
        rw [hΛ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_m hK
        omega

/-- (d): the moment-tail term. -/
lemma term_d_le (hK : 100 ≤ K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / Mc K) ^ Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mc K
          * (2 * (R K : ℝ) ^ Mc K / ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)))
      ≤ 1 / 64 := by
  have hsmN := card_smallPrimes_le (R K) (gridOf K (N K) (by omega)).P₀
  have hR2 := R_ge_two K
  have hMc1 : (1 : ℝ) ≤ Mc K := by exact_mod_cast Mc_pos (K := K) (by omega)
  have he := exp_one_le
  -- `(2e/Mc)^{Mc}·|sm|^{Mc} ≤ (16R)^{Mc}`
  have hbase : 2 * Real.exp 1 / Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ≤ 16 * R K := by
    have hsm : ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ≤ 2 * R K := by
      have : (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card ≤ 2 * R K := by omega
      exact_mod_cast this
    have hsm0 : (0 : ℝ) ≤ (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card := by positivity
    have h1 : 2 * Real.exp 1 / Mc K ≤ 2 * Real.exp 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.exp_pos 1]
    have h2 : 2 * Real.exp 1 / Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ)
        ≤ 2 * Real.exp 1 * (2 * R K) := by
      apply mul_le_mul h1 hsm hsm0 (by positivity)
    nlinarith [Real.exp_pos 1]
  have hpow : (2 * Real.exp 1 / Mc K) ^ Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mc K
      ≤ (2 : ℝ) ^ (4 * Mc K) * (R K : ℝ) ^ Mc K := by
    rw [← mul_pow, pow_mul, show (2 : ℝ) ^ 4 = 16 by norm_num, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hinv := inv_card_le hK
  have hR2Mc := R_pow_two_Mc_le hK
  have hP₀ := P₀_le_two_pow hK
  have hX : (X K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
  have hXpos : (0 : ℝ) < X K := by rw [hX]; positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card : ℝ)
  set q := (2 * Real.exp 1 / Mc K) ^ Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mc K with hq
  have hq0 : 0 ≤ q := by positivity
  calc Λ * (2 * (2 * Real.exp 1 / Mc K) ^ Mc K * ((smallPrimes (R K) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mc K
          * (2 * (R K : ℝ) ^ Mc K / Psz))
      = Λ * q * 2 * 2 * (R K : ℝ) ^ Mc K * (1 / Psz) := by rw [hq]; ring
    _ ≤ Λ * ((2 : ℝ) ^ (4 * Mc K) * (R K : ℝ) ^ Mc K) * 2 * 2 * (R K : ℝ) ^ Mc K
          * (2 * (gridOf K (N K) (by omega)).P₀ / X K) := by gcongr
    _ = Λ * (2 : ℝ) ^ (4 * Mc K) * 8 * (R K : ℝ) ^ (2 * Mc K) * (gridOf K (N K) (by omega)).P₀ / X K := by
        rw [pow_mul (R K : ℝ) 2 (Mc K), sq]; ring
    _ ≤ Λ * (2 : ℝ) ^ (4 * Mc K) * 8 * (2 : ℝ) ^ (10 * 2 ^ m K) * (2 : ℝ) ^ (2 * 2 ^ m K)
          / (2 : ℝ) ^ (100 * 2 ^ m K) := by
        rw [hX]; gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + 4 * Mc K + 3 + 10 * 2 ^ m K + 2 * 2 ^ m K)
          / (2 : ℝ) ^ (100 * 2 ^ m K) := by
        rw [hΛ, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_m hK
        omega

/-- The harmonic sum in the product form used by terms (b),(c):
`∏_{p∈sm}(1 + c·(a/p)) ≤ exp(c·a·∑ 1/p)`. -/
lemma prod_le_exp_mul_sum (s : Finset ℕ) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    ∏ p ∈ s, (1 + c * (a / p)) ≤ Real.exp (c * a * ∑ p ∈ s, (p : ℝ)⁻¹) := by
  have := prod_one_add_le_exp_sum s (fun p => c * (a / p)) (fun p _ => by positivity)
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv]; ring

/-- (b): the Laplace-`lam'` term. -/
lemma term_b_le (hK : 100 ≤ K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((∏ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          / Real.exp 1 ^ Mc K)
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_le hK
  have hprod := prod_le_exp_mul_sum (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀) (Real.exp 1) (2 * (T K : ℝ))
    (Real.exp_pos 1).le (by positivity)
  have he := exp_one_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ m₁ K := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1.trans (m₁_ge_cube (K := K) (by omega))
  have hKr := Kr_le_T_mul_m₁ (K := K) (by omega)
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * m₁ K := by exact_mod_cast hKr
  have hMc : (Mc K : ℝ) = 100000 * T K * m₁ K := by unfold Mc; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 44 * (T K * m₁ K) := by
    have : Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
        ≤ Real.exp 1 * (2 * (T K : ℝ)) * (3 * m₁ K + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos 1, mul_le_mul_of_nonneg_left he hT0]
  rw [Real.exp_one_pow, div_eq_mul_inv, ← Real.exp_neg]
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * ((∏ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (1 + Real.exp 1 * (2 * (T K : ℝ) / p)))
          * Real.exp (-(Mc K : ℝ)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp (Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹)
          * Real.exp (-(Mc K : ℝ))) := by gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K)
        + Real.exp 1 * (2 * (T K : ℝ)) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ - Mc K) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ m₁ K),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-- (c): the Laplace-`lam` term at `lam = 13/2`. -/
lemma term_c_le (hK : 100 ≤ K) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mc K
          * ∏ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_le hK
  have hprod := prod_le_exp_mul_sum (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀) (Real.exp (13 / 2)) (T K : ℝ)
    (Real.exp_pos _).le (by positivity)
  have he := exp_thirteen_half_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ m₁ K := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1.trans (m₁_ge_cube (K := K) (by omega))
  have hKr := Kr_le_T_mul_m₁ (K := K) (by omega)
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * m₁ K := by exact_mod_cast hKr
  have hMc : (Mc K : ℝ) = 100000 * T K * m₁ K := by unfold Mc; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 8800 * (T K * m₁ K) := by
    have : Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
        ≤ Real.exp (13 / 2) * (T K : ℝ) * (3 * m₁ K + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos (13 / 2 : ℝ), mul_le_mul_of_nonneg_left he hT0]
  have hlam : (2 * Real.exp 1 / (13 / 2)) ^ Mc K ≤ Real.exp (-(Mc K : ℝ) / 7) :=
    (pow_le_pow_left₀ (by positivity) four_e_div_thirteen_le _).trans (six_sevenths_pow_le _)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mc K
          * ∏ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp 1 * Real.exp (-(Mc K : ℝ) / 7)
          * Real.exp (Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹)) := by
        gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K) + 1 - Mc K / 7
        + Real.exp (13 / 2) * (T K : ℝ) * ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ m₁ K),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

end terms

/-! ### The budget -/

/-- The pure arithmetic of the budget: five bounded terms and a bounded Jackson term. -/
lemma budget_assembly {Λ Λ' t0 ta tb tc td A : ℝ} (hΛ : Λ ≤ Λ') (_hΛ0 : 0 ≤ Λ)
    (h0' : 0 ≤ t0) (ha' : 0 ≤ ta) (hb' : 0 ≤ tb) (hc' : 0 ≤ tc) (hd' : 0 ≤ td)
    (h0 : Λ' * t0 ≤ Real.exp (-4)) (ha : Λ' * ta ≤ 1 / 64) (hb : Λ' * tb ≤ Real.exp (-4))
    (hc : Λ' * tc ≤ Real.exp (-4)) (hd : Λ' * td ≤ 1 / 64) (hJ : A ≤ 1 / 8) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ)) + A + Λ * (t0 + (ta + tb + tc + td)) < 1 := by
  have he4 := exp_neg_four_le
  have hsum : Λ * (t0 + (ta + tb + tc + td)) ≤ Λ' * t0 + Λ' * ta + Λ' * tb + Λ' * tc + Λ' * td := by
    have : Λ * (t0 + (ta + tb + tc + td)) = Λ * t0 + Λ * ta + Λ * tb + Λ * tc + Λ * td := by ring
    rw [this]
    gcongr
  linarith

/-- **The `hbudget` field of `ScheduleWitness`**, with `δ₁ = δbig = δfar = 1/8`, `ε = 1/K`,
`η = 2^{−k₄}`, `D = Dj K k₄`, `lam' = e`, `lam = 13/2`. -/
theorem hbudget_holds {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
            (T K) (R K) (Mc K)
            (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
            (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) < 1 := by
  have hk : 25 ≤ k₄ := by omega
  have hJ := jackson_term_le (K := K) (k₄ := k₄) (by omega)
  have hΛ := Lambda_le hK4 hk
  unfold smallPrimeBound
  exact budget_assembly hΛ (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (main_term_le hK) (term_a_le hK) (term_b_le hK)
    (term_c_le hK) (term_d_le hK) hJ

end Sched

end NormalNumbers.G4
