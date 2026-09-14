/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMTowerHarmonic
import NormalNumbers.G4EntropyE1Down

/-!
# The marched ladder, step 3: the **small-prime budget** at the marched parameters `(K, j)`

The third and last input of `Sched.entropy_E1_march`: the five `smallPrimeBound` terms with
`R ↦ Rm K j`, `Mc ↦ Mcm K j`, and the sample taken at any `X' ≥ Xlom K j`.

Every term is `G4ScheduleBudget`'s (or `G4EntropyE0Down`'s downward) proof with three
substitutions, and each of the three is an *improvement* or a wash:

* `Mc_le_two_pow_m₂ ↦ Mcm_le_two_pow_m₂` (proved in `G4EntropyMTower`, the one genuine
  `m₁`-ceiling, valid for every `j ≤ jstar K`);
* the harmonic sums `↦ sum_inv_smallPrimes_ge_m` / `sum_inv_smallPrimes_le_m`
  (`G4EntropyMTowerHarmonic`);
* the main term's closed-form equality `(1/8)^K·m₁ K = 1000·K·r` becomes the inequality
  `1000·K·r ≤ (1/8)^K·mm₁ K j`, since `m₁ K ≤ mm₁ K j` by definition of the march.

The exponent budget of terms (a) and (d) is `2Kr + 4·Mcm + 3 + 12·2^{mm} + 6 ≤ 50·2^{mm}`, the
same shape as E0-down's with `Mc ↦ Mcm`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

variable {K j : ℕ}

/-! ### The marched scales: elementary facts -/

lemma Rm_ge_two (K j : ℕ) : 2 ≤ Rm K j := two_le_two_pow_two_pow _

lemma Rm_le_Ym (K j : ℕ) : Rm K j ≤ Ym K j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (mm₁_le_mm K j))

lemma Mcm_pos (hK : 1 ≤ K) (j : ℕ) : 0 < Mcm K j := by
  have hT := T_pos hK
  have hm : 0 < mm₁ K j := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    have := m₁_ge_cube (K := K) hK
    show 0 < m₁ K + j
    omega
  show 0 < 100000 * T K * mm₁ K j
  positivity

lemma mm_eq_mm₁_add (K j : ℕ) : mm K j = mm₁ K j + m₂ K := by
  show m₁ K + m₂ K + j = m₁ K + j + m₂ K
  omega

lemma Xlom_pos (K j : ℕ) : 0 < Xlom K j := Nat.one_le_two_pow

lemma Xlom_cast (K j : ℕ) : ((Xlom K j : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
  show (((2 : ℕ) ^ (50 * 2 ^ mm K j) : ℕ) : ℝ) = _
  push_cast; rfl

lemma Xlo_le_Xlom (K j : ℕ) : Xlo K ≤ Xlom K j := by
  rw [← Xlom_zero]
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul (le_refl 50) (Nat.pow_le_pow_right (by norm_num)
      (show mm K 0 ≤ mm K j by show m K + 0 ≤ m K + j; omega)))

lemma two_mul_P₀_le_Xlom (hK : 100 ≤ K) (j : ℕ) :
    2 * (gridOf K (N K) (by omega)).P₀ ≤ Xlom K j :=
  le_trans (two_mul_P₀_le_Xlo hK) (Xlo_le_Xlom K j)

lemma b₀_lt_of_Xlom_le {K j X' : ℕ} (hK : 100 ≤ K) (h : Xlom K j ≤ X') :
    (gridOf K (N K) (by omega)).b₀ < X' :=
  b₀_lt_of_Xlo_le hK (le_trans (Xlo_le_Xlom K j) h)

/-- `Rm^{2·Mcm} ≤ 2^{10·2^{mm}}` — the march's version of `R_pow_two_Mc_le`. -/
lemma R_pow_two_Mc_le_m (hK : 100 ≤ K) (hj : j ≤ jstar K) :
    (Rm K j : ℝ) ^ (2 * Mcm K j) ≤ (2 : ℝ) ^ (10 * 2 ^ mm K j) := by
  show ((2 ^ 2 ^ mm₁ K j : ℕ) : ℝ) ^ (2 * Mcm K j) ≤ _
  push_cast
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  have h1 := Mcm_le_two_pow_m₂ hK hj
  have h2 : 2 ^ mm K j = 2 ^ mm₁ K j * 2 ^ m₂ K := by rw [mm_eq_mm₁_add, pow_add]
  rw [h2]
  nlinarith [Nat.one_le_two_pow (n := mm₁ K j)]

lemma Kr_le_two_pow_mm (hK : 100 ≤ K) (j : ℕ) : K * (K ^ 2) ^ K ≤ 2 ^ mm K j :=
  (Kr_le_m₁ K).trans (((m₁_le_m K).trans (m_le_mm K j)).trans (Nat.lt_two_pow_self).le)

lemma sizes_le_two_pow_mm (hK : 100 ≤ K) (hj : j ≤ jstar K) :
    K * (K ^ 2) ^ K ≤ 2 ^ mm K j ∧ Mcm K j ≤ 2 ^ mm K j ∧ 8 ≤ 2 ^ mm K j := by
  refine ⟨Kr_le_two_pow_mm hK j, ?_, ?_⟩
  · exact (Mcm_le_two_pow_m₂ hK hj).trans
      (Nat.pow_le_pow_right (by norm_num) (by rw [mm_eq_mm₁_add]; omega))
  · have h3 : 3 ≤ K ^ 3 := by
      calc 3 ≤ K := by omega
        _ ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
    have := m₁_ge_cube (K := K) (by omega)
    have := m₁_le_m K
    have := m_le_mm K j
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mm K j := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `1/|P'| ≤ 2P₀/2^{50·2^{mm}}` for any `X' ≥ Xlom K j`. -/
lemma inv_card_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hlo : Xlom K j ≤ X') :
    1 / ((apSample X' (gridOf K (N K) (by omega)).P₀
        (gridOf K (N K) (by omega)).b₀).card : ℝ)
      ≤ 2 * (gridOf K (N K) (by omega)).P₀ / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
  set G := gridOf K (N K) (by omega : 1 ≤ K)
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hX'pos : 0 < X' := by have := Xlom_pos K j; omega
  have hXr : (0 : ℝ) < X' := by exact_mod_cast hX'pos
  have hXlo' : (2 : ℝ) ^ (50 * 2 ^ mm K j) ≤ (X' : ℝ) := by
    rw [← Xlom_cast K j]; exact_mod_cast hlo
  have hcard := card_apSample_ge_half X' G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (le_trans (two_mul_P₀_le_Xlom hK j) hlo)
  have hcard0 : (0 : ℝ) < (apSample X' G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X' : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have step : 1 / ((apSample X' G.P₀ G.b₀).card : ℝ) ≤ 2 * G.P₀ / (X' : ℝ) := by
    rw [div_le_div_iff₀ hcard0 hXr]
    have := hcard
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  refine step.trans ?_
  gcongr

lemma two_pow_div_le_down_m {e₁ : ℕ} (K j : ℕ) (h : e₁ + 6 ≤ 50 * 2 ^ mm K j) :
    (2 : ℝ) ^ e₁ / (2 : ℝ) ^ (50 * 2 ^ mm K j) ≤ 1 / 64 := by
  rw [div_le_div_iff₀ (show (0:ℝ) < 2 ^ (50 * 2 ^ mm K j) by positivity)
    (show (0:ℝ) < 64 by norm_num)]
  calc (2 : ℝ) ^ e₁ * 64 = (2 : ℝ) ^ (e₁ + 6) := by rw [pow_add]; norm_num
    _ ≤ (2 : ℝ) ^ (50 * 2 ^ mm K j) := pow_le_pow_right₀ (by norm_num) h
    _ = _ := (one_mul _).symm

/-! ### The five terms -/

/-- main: `Λ·exp(−4θ₀∑1/p) ≤ e^{−4}` at the marched cutoff. -/
lemma main_term_le_m (hK : 100 ≤ K) (j : ℕ) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * Real.exp (-∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
          4 * (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) / p)
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_ge_m hK j
  set Sg := ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ with hSgdef
  have hsum : ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
      4 * (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) / p = (1 / 8 : ℝ) ^ K / 64 * Sg := by
    rw [hSgdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv]; ring
  rw [hsum]
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set r : ℝ := (((K ^ 2) ^ K : ℕ) : ℝ) with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hKr1 : (1 : ℝ) ≤ K * r := by nlinarith
  have h8 : (0 : ℝ) < (1 / 8 : ℝ) ^ K := by positivity
  have hm₁ : (1 / 8 : ℝ) ^ K * m₁ K = 1000 * (K * r) := by
    rw [m₁_eq, hr]
    have : (1 / 8 : ℝ) ^ K * 8 ^ K = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 8 : ℝ) ^ K * (1000 * 8 ^ K * (K * ((K ^ 2) ^ K : ℕ)))
        = ((1 / 8 : ℝ) ^ K * 8 ^ K) * (1000 * (K * ((K ^ 2) ^ K : ℕ))) := by ring
      _ = 1000 * (K * ((K ^ 2) ^ K : ℕ)) := by rw [this, one_mul]
  -- the march only raises the main term's driver
  have hmarch : (1 / 8 : ℝ) ^ K * m₁ K ≤ (1 / 8 : ℝ) ^ K * mm₁ K j := by
    have : (m₁ K : ℝ) ≤ mm₁ K j := by
      have : m₁ K ≤ mm₁ K j := by show m₁ K ≤ m₁ K + j; omega
      exact_mod_cast this
    nlinarith
  have hsmall : (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) ≤ 1 := by
    have h := twentyone_sq_add_four_le hK
    have h' : (21 * (K : ℝ) ^ 2 + 4) ≤ (8 : ℝ) ^ K := by exact_mod_cast h
    calc (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) ≤ (1 / 8 : ℝ) ^ K * 8 ^ K := by gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hS8 : 690 * (K * r) - 1 ≤ (1 / 8 : ℝ) ^ K * Sg := by
    have hmul := mul_le_mul_of_nonneg_left hS h8.le
    have e : (1 / 8 : ℝ) ^ K * ((mm₁ K j : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4)
        = ((1 / 8 : ℝ) ^ K * mm₁ K j) * Real.log 2
          - (1 / 8 : ℝ) ^ K * (21 * (K : ℝ) ^ 2 + 4) := by ring
    rw [e] at hmul
    nlinarith
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * r) := by rw [hr]; push_cast; ring
  rw [hcast] at h2
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) * Real.exp (-((1 / 8 : ℝ) ^ K / 64 * Sg))
      ≤ Real.exp (2 * (K * r)) * Real.exp (-((1 / 8 : ℝ) ^ K / 64 * Sg)) := by gcongr
    _ = Real.exp (2 * (K * r) - (1 / 8 : ℝ) ^ K / 64 * Sg) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        nlinarith

/-- (a): the residue-transfer term, marched and downward. -/
lemma term_a_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K) (hlo : Xlom K j ≤ X') :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).powerset.filter
            (fun T' => T'.Nonempty ∧ T'.card ≤ Mcm K j)).card : ℝ)
          * (2 ^ Mcm K j * (2 * (Rm K j : ℝ) ^ Mcm K j
              / ((apSample X' (gridOf K (N K) (by omega)).P₀
                  (gridOf K (N K) (by omega)).b₀).card : ℝ))))
      ≤ 1 / 64 := by
  have hcardN := card_small_subsets_le (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
    (Mcm K j)
  have hsmN := card_smallPrimes_le (Rm K j) (gridOf K (N K) (by omega)).P₀
  have hR2 := Rm_ge_two K j
  have hcard : ((((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mcm K j)).card : ℕ) : ℝ)
      ≤ Mcm K j * (2 * (Rm K j : ℝ)) ^ Mcm K j := by
    have : ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).powerset.filter
        (fun T' => T'.Nonempty ∧ T'.card ≤ Mcm K j)).card ≤ Mcm K j * (2 * Rm K j) ^ Mcm K j := by
      refine hcardN.trans ?_
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    exact_mod_cast this
  have hinv := inv_card_le_down_m hK hlo
  have hMc : (Mcm K j : ℝ) ≤ 2 ^ Mcm K j := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hR2Mc := R_pow_two_Mc_le_m hK hj
  have hP₀ := P₀_le_two_pow_m hK j
  have hP₀0 : (0 : ℝ) ≤ (gridOf K (N K) (by omega)).P₀ := by positivity
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample X' (gridOf K (N K) (by omega)).P₀
    (gridOf K (N K) (by omega)).b₀).card : ℝ)
  set c := ((((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).powerset.filter
      (fun T' => T'.Nonempty ∧ T'.card ≤ Mcm K j)).card : ℕ) : ℝ)
  have hΛ0 : 0 ≤ Λ := by positivity
  have hRr : (0 : ℝ) ≤ Rm K j := by positivity
  calc Λ * (c * (2 ^ Mcm K j * (2 * (Rm K j : ℝ) ^ Mcm K j / Psz)))
      = Λ * c * 2 ^ Mcm K j * 2 * (Rm K j : ℝ) ^ Mcm K j * (1 / Psz) := by ring
    _ ≤ Λ * (Mcm K j * (2 * (Rm K j : ℝ)) ^ Mcm K j) * 2 ^ Mcm K j * 2
          * (Rm K j : ℝ) ^ Mcm K j
          * (2 * (gridOf K (N K) (by omega)).P₀ / (2 : ℝ) ^ (50 * 2 ^ mm K j)) := by gcongr
    _ = Λ * Mcm K j * 2 ^ Mcm K j * 2 ^ Mcm K j * 4 * (Rm K j : ℝ) ^ (2 * Mcm K j)
          * (gridOf K (N K) (by omega)).P₀ / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        rw [mul_pow, pow_mul (Rm K j : ℝ) 2 (Mcm K j), sq]; ring
    _ ≤ Λ * 2 ^ Mcm K j * 2 ^ Mcm K j * 2 ^ Mcm K j * 4 * (2 : ℝ) ^ (10 * 2 ^ mm K j)
          * (2 : ℝ) ^ (2 * 2 ^ mm K j) / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + Mcm K j + Mcm K j + Mcm K j + 2 + 10 * 2 ^ mm K j
          + 2 * 2 ^ mm K j) / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        rw [hΛ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le_down_m
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_mm hK hj
        omega

/-- (d): the moment-tail term, marched and downward. -/
lemma term_d_le_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K) (hlo : Xlom K j ≤ X') :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / Mcm K j) ^ Mcm K j
          * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mcm K j
          * (2 * (Rm K j : ℝ) ^ Mcm K j
              / ((apSample X' (gridOf K (N K) (by omega)).P₀
                  (gridOf K (N K) (by omega)).b₀).card : ℝ)))
      ≤ 1 / 64 := by
  have hsmN := card_smallPrimes_le (Rm K j) (gridOf K (N K) (by omega)).P₀
  have hR2 := Rm_ge_two K j
  have hMc1 : (1 : ℝ) ≤ Mcm K j := by exact_mod_cast Mcm_pos (K := K) (by omega) j
  have he := exp_one_le
  have hbase : 2 * Real.exp 1 / Mcm K j
      * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ) ≤ 16 * Rm K j := by
    have hsm : ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ)
        ≤ 2 * Rm K j := by
      have : (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card ≤ 2 * Rm K j := by omega
      exact_mod_cast this
    have hsm0 : (0 : ℝ) ≤ (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card := by
      positivity
    have h1 : 2 * Real.exp 1 / Mcm K j ≤ 2 * Real.exp 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.exp_pos 1]
    have h2 : 2 * Real.exp 1 / Mcm K j
        * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ)
        ≤ 2 * Real.exp 1 * (2 * Rm K j) := by
      apply mul_le_mul h1 hsm hsm0 (by positivity)
    nlinarith [Real.exp_pos 1]
  have hpow : (2 * Real.exp 1 / Mcm K j) ^ Mcm K j
      * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mcm K j
      ≤ (2 : ℝ) ^ (4 * Mcm K j) * (Rm K j : ℝ) ^ Mcm K j := by
    rw [← mul_pow, pow_mul, show (2 : ℝ) ^ 4 = 16 by norm_num, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hinv := inv_card_le_down_m hK hlo
  have hR2Mc := R_pow_two_Mc_le_m hK hj
  have hP₀ := P₀_le_two_pow_m hK j
  set Λ := (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) with hΛ
  set Psz := ((apSample X' (gridOf K (N K) (by omega)).P₀
    (gridOf K (N K) (by omega)).b₀).card : ℝ)
  set q := (2 * Real.exp 1 / Mcm K j) ^ Mcm K j
    * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mcm K j with hq
  have hq0 : 0 ≤ q := by positivity
  calc Λ * (2 * (2 * Real.exp 1 / Mcm K j) ^ Mcm K j
          * ((smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀).card : ℝ) ^ Mcm K j
          * (2 * (Rm K j : ℝ) ^ Mcm K j / Psz))
      = Λ * q * 2 * 2 * (Rm K j : ℝ) ^ Mcm K j * (1 / Psz) := by rw [hq]; ring
    _ ≤ Λ * ((2 : ℝ) ^ (4 * Mcm K j) * (Rm K j : ℝ) ^ Mcm K j) * 2 * 2
          * (Rm K j : ℝ) ^ Mcm K j
          * (2 * (gridOf K (N K) (by omega)).P₀ / (2 : ℝ) ^ (50 * 2 ^ mm K j)) := by gcongr
    _ = Λ * (2 : ℝ) ^ (4 * Mcm K j) * 8 * (Rm K j : ℝ) ^ (2 * Mcm K j)
          * (gridOf K (N K) (by omega)).P₀ / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        rw [pow_mul (Rm K j : ℝ) 2 (Mcm K j), sq]; ring
    _ ≤ Λ * (2 : ℝ) ^ (4 * Mcm K j) * 8 * (2 : ℝ) ^ (10 * 2 ^ mm K j)
          * (2 : ℝ) ^ (2 * 2 ^ mm K j) / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        gcongr
    _ = (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K) + 4 * Mcm K j + 3 + 10 * 2 ^ mm K j + 2 * 2 ^ mm K j)
          / (2 : ℝ) ^ (50 * 2 ^ mm K j) := by
        rw [hΛ, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ 1 / 64 := by
        apply two_pow_div_le_down_m
        obtain ⟨h1, h2, h3⟩ := sizes_le_two_pow_mm hK hj
        omega

/-- (b): the Laplace-`lam'` term at the marched cutoff. -/
lemma term_b_le_m (hK : 100 ≤ K) (j : ℕ) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * ((∏ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
            (1 + Real.exp 1 * (2 * (T K : ℝ) / p))) / Real.exp 1 ^ Mcm K j)
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_le_m hK j
  have hprod := prod_le_exp_mul_sum (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
    (Real.exp 1) (2 * (T K : ℝ)) (Real.exp_pos 1).le (by positivity)
  have he := exp_one_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ mm₁ K j := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ m₁ K := h1.trans (m₁_ge_cube (K := K) (by omega))
    have : 1 ≤ mm₁ K j := by show 1 ≤ m₁ K + j; omega
    exact_mod_cast this
  have hKr : K * (K ^ 2) ^ K ≤ T K * mm₁ K j := by
    refine (Kr_le_T_mul_m₁ (K := K) (by omega)).trans ?_
    exact Nat.mul_le_mul_left _ (by show m₁ K ≤ m₁ K + j; omega)
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * mm₁ K j := by exact_mod_cast hKr
  have hMc : (Mcm K j : ℝ) = 100000 * T K * mm₁ K j := by
    show ((100000 * T K * mm₁ K j : ℕ) : ℝ) = _; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp 1 * (2 * (T K : ℝ))
      * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 44 * (T K * (mm₁ K j : ℝ)) := by
    have : Real.exp 1 * (2 * (T K : ℝ))
        * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
        ≤ Real.exp 1 * (2 * (T K : ℝ)) * (3 * (mm₁ K j : ℝ) + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos 1, mul_le_mul_of_nonneg_left he hT0]
  rw [Real.exp_one_pow, div_eq_mul_inv, ← Real.exp_neg]
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * ((∏ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
              (1 + Real.exp 1 * (2 * (T K : ℝ) / p))) * Real.exp (-(Mcm K j : ℝ)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp (Real.exp 1 * (2 * (T K : ℝ))
            * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹)
          * Real.exp (-(Mcm K j : ℝ))) := by gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K)
        + Real.exp 1 * (2 * (T K : ℝ))
          * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
        - Mcm K j) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ (mm₁ K j : ℝ)),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-- (c): the Laplace-`lam` term at `lam = 13/2`, marched. -/
lemma term_c_le_m (hK : 100 ≤ K) (j : ℕ) :
    (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mcm K j
          * ∏ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
              (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (-4) := by
  have hS := sum_inv_smallPrimes_le_m hK j
  have hprod := prod_le_exp_mul_sum (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
    (Real.exp (13 / 2)) (T K : ℝ) (Real.exp_pos _).le (by positivity)
  have he := exp_thirteen_half_le
  have hT1 : (1 : ℝ) ≤ T K := by exact_mod_cast T_pos (K := K) (by omega)
  have hm1 : (1 : ℝ) ≤ mm₁ K j := by
    have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ m₁ K := h1.trans (m₁_ge_cube (K := K) (by omega))
    have : 1 ≤ mm₁ K j := by show 1 ≤ m₁ K + j; omega
    exact_mod_cast this
  have hKr : K * (K ^ 2) ^ K ≤ T K * mm₁ K j := by
    refine (Kr_le_T_mul_m₁ (K := K) (by omega)).trans ?_
    exact Nat.mul_le_mul_left _ (by show m₁ K ≤ m₁ K + j; omega)
  have hKrr : (K * (K ^ 2) ^ K : ℝ) ≤ T K * mm₁ K j := by exact_mod_cast hKr
  have hMc : (Mcm K j : ℝ) = 100000 * T K * mm₁ K j := by
    show ((100000 * T K * mm₁ K j : ℕ) : ℝ) = _; push_cast; ring
  have h2 := two_pow_le_exp (2 * (K * (K ^ 2) ^ K))
  have hcast : ((2 * (K * (K ^ 2) ^ K) : ℕ) : ℝ) = 2 * (K * (K ^ 2) ^ K) := by push_cast; ring
  rw [hcast] at h2
  have hS0 : 0 ≤ ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hexpo : Real.exp (13 / 2) * (T K : ℝ)
      * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 8800 * (T K * (mm₁ K j : ℝ)) := by
    have : Real.exp (13 / 2) * (T K : ℝ)
        * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
        ≤ Real.exp (13 / 2) * (T K : ℝ) * (3 * (mm₁ K j : ℝ) + 5) := by gcongr
    have hT0 : (0 : ℝ) ≤ T K := by linarith
    nlinarith [Real.exp_pos (13 / 2 : ℝ), mul_le_mul_of_nonneg_left he hT0]
  have hlam : (2 * Real.exp 1 / (13 / 2)) ^ Mcm K j ≤ Real.exp (-(Mcm K j : ℝ) / 7) :=
    (pow_le_pow_left₀ (by positivity) four_e_div_thirteen_le _).trans (six_sevenths_pow_le _)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  calc (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
        * (2 * (2 * Real.exp 1 / (13 / 2)) ^ Mcm K j
          * ∏ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀,
              (1 + Real.exp (13 / 2) * ((T K : ℝ) / p)))
      ≤ Real.exp (2 * (K * (K ^ 2) ^ K))
        * (Real.exp 1 * Real.exp (-(Mcm K j : ℝ) / 7)
          * Real.exp (Real.exp (13 / 2) * (T K : ℝ)
              * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹)) := by
        gcongr
    _ = Real.exp (2 * (K * (K ^ 2) ^ K) + 1 - Mcm K j / 7
        + Real.exp (13 / 2) * (T K : ℝ)
          * ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-4) := by
        apply Real.exp_le_exp.2
        rw [hMc]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T K) (by linarith : (0:ℝ) ≤ (mm₁ K j : ℝ)),
          mul_le_mul hT1 hm1 (by norm_num) (by linarith)]

/-! ### The assembled small-prime term -/

lemma smallPrimeBound_tiny_down_m {K j X' : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K)
    (hlo : Xlom K j ≤ X') :
    smallPrimeBound (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
        (T K) (Rm K j) (Mcm K j)
        (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) := by
  have hbig : (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * smallPrimeBound (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
        (T K) (Rm K j) (Mcm K j)
        (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ 3 * Real.exp (-4) + 1 / 32 := by
    unfold smallPrimeBound
    exact budget_terms_le le_rfl (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (main_term_le_m hK j)
      (term_a_le_down_m hK hj hlo) (term_b_le_m hK j) (term_c_le_m hK j)
      (term_d_le_down_m hK hj hlo)
  have he4 := exp_neg_four_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hbig, he4]

theorem smallPrime_term_tiny_down_m {K k₄ j X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hj : j ≤ jstar K) (hlo : Xlom K j ≤ X') :
    (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
          (T K) (Rm K j) (Mcm K j)
          (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ K := by
  have hk : 25 ≤ k₄ := by omega
  have hq := smallPrimeBound_tiny_down_m hK hj hlo
  have hΛ := LambdaE_le hK4 hk
  have hq0 : (0 : ℝ) ≤ smallPrimeBound (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
      (T K) (Rm K j) (Mcm K j)
      (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
      (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hstep : (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀)
          (T K) (Rm K j) (Mcm K j)
          (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (2 : ℝ) ^ (K * (K ^ 2) ^ K) * ((1 / 8 : ℝ) / (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))) :=
    mul_le_mul hΛ hq hq0 (by positivity)
  refine hstep.trans ?_
  have hsplit : (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      = (2 : ℝ) ^ (K * (K ^ 2) ^ K) * (2 : ℝ) ^ (K * (K ^ 2) ^ K) := by
    rw [← pow_add]; ring_nf
  rw [hsplit]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (K * (K ^ 2) ^ K) := by positivity
  have he : (2 : ℝ) ^ (K * (K ^ 2) ^ K) * ((1 / 8 : ℝ)
      / ((2 : ℝ) ^ (K * (K ^ 2) ^ K) * (2 : ℝ) ^ (K * (K ^ 2) ^ K)))
      = (1 / 8 : ℝ) / (2 : ℝ) ^ (K * (K ^ 2) ^ K) := by field_simp
  rw [he]
  have hKr : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (K * (K ^ 2) ^ K) :=
    pow_le_pow_right₀ (by norm_num)
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by positivity)))
  gcongr

end Sched

end NormalNumbers.G4
