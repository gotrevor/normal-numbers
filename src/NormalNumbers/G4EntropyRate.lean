/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBudget

/-!
# Entropy expedition §4: the **rate** — `δ_K ≍ 1/√K`, hence E1

`G4EntropyBudget.entropy_E0` proves E0 at the *fixed* deficit `δ = 4/5`, because the three error
allowances it inherits from the disjunctivity argument (`δbig`, `δfar`, `κ`) are pinned at `1/8`.
The brief's qualitative E0 (`H₂/(m_K H_K) → 1`) and quantitative E1
(`H₂ ≥ m_K H_K − C H_K √K`) both need `δ_K → 0`, and `entropy_cover_bound` already permits any

    `δ ≥ (92√K + 51)/(K log 2)  ≍  133/√K`,

so the whole remaining question is brief §4's `e_K = a_K/ρ_K + 2κ_K + Λ_K q_K = o(K^{−1/2})`.
This file makes each of the four allowances *exponentially* small, which is far more than needed:

| allowance | new bound | how |
|---|---|---|
| cover | `(1/8)/2^K` | `entropy_cover_bound` (already) |
| `δfar` | `(1/8)·2^{−3k₄}` | pure arithmetic on the **existing** `hfar_holds` (`(1/2)^K` vs `(1/2)^{k₄}`) |
| `δbig` | `2^{−k₄}` | `hbig_small`: `hbig_holds`'s own inputs, with `2Ka⁶+34a⁴ ≤ a·((1/K)a)` |
| `2κ` | `1/(8K)` | a larger Jackson degree `DjE = (16K²2^{k₄})²` |
| `Λδ₃` | `(1/8)/2^{K·r}` | `smallPrimeBound_tiny`: the five term bounds hold against `2^{2Kr}`, while `DjE` keeps `Λ ≤ 2^{Kr}` — half the budget is spent as *decay* |

The last row is the trick that avoids re-proving `main_term_le`/`term_a..d_le` with sharper
right-hand sides: `2^{2Kr}·q ≤ 1/8` says `q ≤ (1/8)2^{−2Kr}`, and `Λ ≤ 2^{Kr}` then gives
`Λq ≤ (1/8)2^{−Kr}`.  `DjE` is small enough for `2·DjE+1 ≤ 2^K` (not merely `≤ 4^K`), which is
exactly what halves the exponent.

Main results: `entropy_E0_rate` (`H₂ > (1 − 200/√K)·m_K H_K`) and `entropy_E1`
(`H₂ > m_K H_K − 50·H_K·√K`).
-/

open Real Finset MeasureTheory
open scoped BigOperators

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### A power comparison -/

/-- `n⁴ ≤ 2ⁿ` for `n ≥ 16` (equality at `16`). -/
lemma pow_four_le_two_pow : ∀ {n : ℕ}, 16 ≤ n → n ^ 4 ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
        have hexp : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
        have h1 : 16 * n ^ 3 ≤ n ^ 4 := by
          calc 16 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
            _ = n ^ 4 := by ring
        have h2 : 6 * n ^ 2 + 4 * n + 1 ≤ 12 * n ^ 3 := by nlinarith
        omega
      calc (n + 1) ^ 4 ≤ 2 * n ^ 4 := hstep
        _ ≤ 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-! ### The entropy schedule's Jackson degree -/

/-- `D = (16K²2^{k₄})²`: a factor `K` larger than the disjunctivity schedule's `Dj`, which buys
`2κ ≤ 1/(8K)`, and still small enough that `2D+1 ≤ 2^K`. -/
def DjE (K k₄ : ℕ) : ℕ := (16 * K ^ 2 * 2 ^ k₄) ^ 2

lemma two_DjE_add_one_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 25 ≤ k₄) :
    2 * DjE K k₄ + 1 ≤ 2 ^ K := by
  subst hK4
  have hk4 : k₄ ^ 4 ≤ 2 ^ k₄ := pow_four_le_two_pow (by omega)
  have hDE : DjE (4 * k₄) k₄ = 65536 * k₄ ^ 4 * 2 ^ (2 * k₄) := by
    unfold DjE
    rw [show 16 * (4 * k₄) ^ 2 * 2 ^ k₄ = 256 * k₄ ^ 2 * 2 ^ k₄ by ring]
    rw [mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hDE]
  have h1 : 2 * (65536 * k₄ ^ 4 * 2 ^ (2 * k₄)) ≤ 2 ^ 17 * 2 ^ k₄ * 2 ^ (2 * k₄) := by
    have : 2 * (65536 * k₄ ^ 4 * 2 ^ (2 * k₄)) = 2 ^ 17 * k₄ ^ 4 * 2 ^ (2 * k₄) := by
      norm_num; ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk4)
  have h2 : 2 ^ 17 * 2 ^ k₄ * 2 ^ (2 * k₄) = 2 ^ (3 * k₄ + 17) := by
    rw [← pow_add, ← pow_add]; ring_nf
  have h3 : 2 ^ (3 * k₄ + 17) ≤ 2 ^ (4 * k₄ - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (4 * k₄ - 1) + 1 ≤ 2 ^ (4 * k₄) := by
    have he : 2 ^ (4 * k₄) = 2 * 2 ^ (4 * k₄ - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hp : 1 ≤ 2 ^ (4 * k₄ - 1) := Nat.one_le_two_pow
    omega
  omega

lemma DjE_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 25 ≤ k₄) : DjE K k₄ ≤ 2 ^ K := by
  have := two_DjE_add_one_le hK4 hk
  omega

lemma two_pow_mul_DjE_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    2 ^ K * DjE K k₄ ≤ 4 ^ (N K - 1) := by
  have hk : 25 ≤ k₄ := by omega
  have h1 : 2 ^ K * DjE K k₄ ≤ 2 ^ K * 2 ^ K := Nat.mul_le_mul_left _ (DjE_le hK4 hk)
  have h2 : 2 ^ K * 2 ^ K = 4 ^ K := by
    rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have h3 : K ≤ N K - 1 := by
    unfold N
    have : K + 1 ≤ 100 * K ^ 2 := by nlinarith
    omega
  calc 2 ^ K * DjE K k₄ ≤ 4 ^ K := by rw [← h2]; exact h1
    _ ≤ 4 ^ (N K - 1) := Nat.pow_le_pow_right (by norm_num) h3

/-- `Λ_E ≤ 2^{K·r}` — *half* the exponent `Lambda_le` allows. -/
lemma LambdaE_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 25 ≤ k₄) :
    (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (K * (K ^ 2) ^ K) := by
  have h : (2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) ≤ 2 ^ (K * (K ^ 2) ^ K) := by
    calc (2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K)
        ≤ (2 ^ K) ^ ((K ^ 2) ^ K) := Nat.pow_le_pow_left (two_DjE_add_one_le hK4 hk) _
      _ = 2 ^ (K * (K ^ 2) ^ K) := by rw [← pow_mul]
  exact_mod_cast h

/-- **`2κ ≤ 1/(8K)`.** -/
lemma jackson_term_small {K k₄ : ℕ} (hK : 1 ≤ K) :
    2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((DjE K k₄ : ℕ) + 1)))
      ≤ 1 / (8 * K) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : (16 * (K : ℝ) ^ 2 * 2 ^ k₄) ≤ Real.sqrt ((DjE K k₄ : ℕ) + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    unfold DjE; push_cast; linarith
  have h16 : (16 : ℝ) * K ≤ (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((DjE K k₄ : ℕ) + 1) := by
    have e1 : (1 / 2 : ℝ) ^ k₄ * 2 ^ k₄ = 1 := by rw [← mul_pow]; norm_num
    have e2 : (1 / K : ℝ) * K = 1 := by field_simp
    have e3 : (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * (16 * (K : ℝ) ^ 2 * 2 ^ k₄)
        = 16 * K * ((1 / K : ℝ) * K) * ((1 / 2 : ℝ) ^ k₄ * 2 ^ k₄) := by
      field_simp
    calc (16 : ℝ) * K = (1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * (16 * (K : ℝ) ^ 2 * 2 ^ k₄) := by
          rw [e3, e1, e2]; ring
      _ ≤ _ := by gcongr
  have hpos : (0 : ℝ) < 16 * K := by linarith
  have h : 1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((DjE K k₄ : ℕ) + 1))
      ≤ 1 / (16 * K) := one_div_le_one_div_of_le hpos h16
  have he : (2 : ℝ) * (1 / (16 * K)) = 1 / (8 * K) := by field_simp; ring
  linarith [mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2), he]

/-! ### The small-prime term, made exponentially small -/

/-- `q_K ≤ (1/8)·2^{−2Kr}`: the five term bounds of `G4ScheduleBudget` read as a bound on
`smallPrimeBound` itself rather than on `Λ'·smallPrimeBound`. -/
lemma smallPrimeBound_tiny {K : ℕ} (hK : 100 ≤ K) :
    smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
        (T K) (R K) (Mc K)
        (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) := by
  have hbig : (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
        (T K) (R K) (Mc K)
        (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ 3 * Real.exp (-4) + 1 / 32 := by
    unfold smallPrimeBound
    exact budget_terms_le le_rfl (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (main_term_le hK) (term_a_le hK)
      (term_b_le hK) (term_c_le hK) (term_d_le hK)
  have he4 := exp_neg_four_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hbig, he4]

/-- **`Λ_E·q_K ≤ (1/8)/2^K`.** -/
lemma smallPrime_term_tiny {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ K := by
  have hk : 25 ≤ k₄ := by omega
  have hq := smallPrimeBound_tiny hK
  have hΛ := LambdaE_le hK4 hk
  have hq0 : (0 : ℝ) ≤ smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
      (T K) (R K) (Mc K)
      (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
      (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hstep : (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (2 : ℝ) ^ (K * (K ^ 2) ^ K) * ((1 / 8 : ℝ) / (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))) := by
    refine mul_le_mul hΛ hq hq0 (by positivity)
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

/-! ### `δbig` and `δfar`, made exponentially small -/

lemma big_aux1 {k₄ : ℕ} (hk : 25 ≤ k₄) : 64 * k₄ ^ 2 ≤ 2 ^ (4 * k₄) := by
  have h1 : k₄ ≤ 2 ^ k₄ := Nat.lt_two_pow_self.le
  have h2 : (64 : ℕ) ≤ 2 ^ k₄ := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ k₄ := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 64 * k₄ ^ 2 ≤ 2 ^ k₄ * (2 ^ k₄) ^ 2 := Nat.mul_le_mul h2 (Nat.pow_le_pow_left h1 2)
    _ = 2 ^ (3 * k₄) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ (4 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma big_aux2 {k₄ : ℕ} (hk : 25 ≤ k₄) : 272 * k₄ ≤ 2 ^ (2 * k₄) := by
  have h1 : k₄ ≤ 2 ^ k₄ := Nat.lt_two_pow_self.le
  have h2 : (272 : ℕ) ≤ 2 ^ k₄ := by
    calc (272 : ℕ) ≤ 2 ^ 9 := by norm_num
      _ ≤ 2 ^ k₄ := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 272 * k₄ ≤ 2 ^ k₄ * 2 ^ k₄ := Nat.mul_le_mul h2 h1
    _ = 2 ^ (2 * k₄) := by rw [← pow_add]; ring_nf

/-- **`δbig = 2^{−k₄}`.**  The same proof as `hbig_holds` — whose inputs `dyadic_factor_le`,
`sample_term_le`, `log_Mx_div_le` are all top-level — with `2Ka⁶ + 34a⁴ ≤ a·((1/K)·a)` in place
of `≤ (1/8)·((1/K)·a)`.  The slack is `a³ = 2^{−3k₄}`, so nothing here is tight. -/
theorem hbig_small {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K)) * (1 / 2 : ℝ) ^ K / 3
      ≤ (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h8K : (1 / 8 : ℝ) ^ K = a ^ 12 := by
    rw [ha, ← pow_mul, hK4, show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]; ring_nf
  have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
  -- the square root (verbatim from `hbig_holds`)
  have hs2 := sample_term_le hK
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      ≤ 2 * K * a ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15) ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by
      have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
      have hd := dyadic_factor_le K
      have : 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          ≤ 30 * (K : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ K := by positivity
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc 4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X K) (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ)
        ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K + (1 / 8 : ℝ) ^ K := add_le_add hfac hs2
      _ ≤ 4 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by nlinarith
      _ = (2 * K * a ^ 6) ^ 2 := by rw [h8K]; ring
  have ht3 : (Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K))
        * (1 / 2 : ℝ) ^ K / 3 ≤ 34 * a ^ 4 := by
    have := log_Mx_div_le hK
    have hl : 0 ≤ Real.log ((X K + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hX1 : (1 : ℝ) ≤ X K := by unfold X; exact_mod_cast Nat.one_le_two_pow
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (N K)) : (0 : ℝ) ≤ _)
        nlinarith
      · apply Real.log_nonneg; unfold Y; push_cast; exact one_le_pow₀ (by norm_num)
    rw [h2K]
    have ha4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  -- close, with the **exponentially small** right-hand side
  have hc1 : 2 * K * a ^ 6 ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) := by
    have hnat : (64 : ℝ) * (k₄ : ℝ) ^ 2 ≤ (2 : ℝ) ^ (4 * k₄) := by
      exact_mod_cast big_aux1 hk
    have he : a ^ 4 = 1 / (2 : ℝ) ^ (4 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
    have hkey : (4 : ℝ) * K ^ 2 * a ^ 4 ≤ 1 := by
      rw [he, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) = a ^ 2 / (2 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0, pow_pos ha0 2]
  have hc2 : 34 * a ^ 4 ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) := by
    have hnat : (272 : ℝ) * (k₄ : ℝ) ≤ (2 : ℝ) ^ (2 * k₄) := by exact_mod_cast big_aux2 hk
    have he : a ^ 2 = 1 / (2 : ℝ) ^ (2 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
    have hkey : (68 : ℝ) * K * a ^ 2 ≤ 1 := by
      rw [he, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) = a ^ 2 / (2 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0, pow_pos ha0 2]
  calc _ ≤ 2 * K * a ^ 6 + 34 * a ^ 4 := add_le_add hsq ht3
    _ ≤ (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) + (1 / 2 : ℝ) * (a * ((1 / K : ℝ) * a)) :=
        add_le_add hc1 hc2
    _ = (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

/-- **`δfar = (1/8)·2^{−3k₄}`** — pure arithmetic on the *existing* `hfar_holds`, which bounds
the far tail by `(1/8)(1/K)(1/2)^K` while `ε·η = (1/K)(1/2)^{k₄}` and `K = 4k₄`. -/
theorem hfar_small {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) (X K) (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have h := hfar_holds hK
  have hKpos : (0 : ℝ) < K := by
    have : (100 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
  rw [h2K] at h
  refine h.trans ?_
  have hrw : (1 / 8 : ℝ) * (1 / (K : ℝ) * a ^ 4) = a ^ 4 / (8 * K) := by field_simp
  have hrw2 : a * (1 / (K : ℝ) * a) = a ^ 2 / K := by field_simp
  rw [hrw, hrw2, div_le_div_iff₀ (by positivity) hKpos]
  have h42 : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
  nlinarith [pow_pos ha0 2, pow_pos ha0 4, ha0, ha1, hKpos, h42]

/-! ### E0 at rate `1/√K`, and E1 -/

set_option maxHeartbeats 2000000 in
/-- **E0 with the rate `δ_K = 200/√K`, and hence E1.**  For every `K = 4k₄ ≥ 160000`,

    `m_K·H_K − 50·√K·H_K  <  H₂(Z^{G4}_K)`,      `m_K = k₄ = K/4`, `H_K = (K²+1)^K`,

which is the brief's E1 with `C = 50`, `K₀ = 160000`; dividing by `m_K H_K` gives the
qualitative E0 `H₂/(m_K H_K) ≥ 1 − 200/√K → 1`.

The deficit `δ_K = 200/√K` is admissible for `entropy_cover_bound` because
`92√K + 51 ≤ 200√K·log 2`, and the four error allowances are all `O(1/K)`
(`hbig_small`, `hfar_small`, `jackson_term_small`, `smallPrime_term_tiny`), comfortably
inside `δ_K/(2−δ_K) ≥ 100/√K`. -/
theorem entropy_E1 {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 160000 ≤ K) :
    (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
        - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
      < (NormalNumbers.G4Entropy.jointLaw (gridOf K (N K) (by omega))
          (b₀_lt_X (show 100 ≤ K by omega)) k₄ (primeLambertAtBase 4)).H₂ := by
  have hK100 : 100 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hk : 25 ≤ k₄ := by omega
  have hKr : (160000 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  -- `√K ≥ 400`
  have hS0 : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have hSsq : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by positivity)
  have hS400 : (400 : ℝ) ≤ Real.sqrt K := by
    have h : Real.sqrt (160000 : ℝ) ≤ Real.sqrt K := Real.sqrt_le_sqrt hKr
    have he : Real.sqrt (160000 : ℝ) = 400 := by
      rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [he ▸ h]
  set δ : ℝ := 200 / Real.sqrt K with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hS0 (by norm_num)]
    linarith
  have hδ1 : δ < 1 := by linarith
  set G := gridOf K (N K) hK1 with hGdef
  set hX := b₀_lt_X (show 100 ≤ K by omega) with hXdef
  set η : ℝ := (1 / 2 : ℝ) ^ k₄ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; positivity
  set ε : ℝ := 1 / (K : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set hne := NormalNumbers.G4Entropy.apSample_nonempty G hX with hnedef
  set fr := gridFrame 4 (by norm_num) G (X K) hne (smallPrimes (R K) G.P₀)
    (frozenGamma 4 G) hη hε (DjE K k₄) with hfrdef
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective (fr.θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective (fr.γ ν)
  set M : ℝ := (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) with hMdef
  have hHcast : (0 : ℝ) < (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
    have : 0 < (K ^ 2 + 1) ^ K := Nat.pow_pos (by positivity)
    exact_mod_cast this
  have hk₄pos : (0 : ℝ) < (k₄ : ℝ) := by exact_mod_cast (show 0 < k₄ by omega)
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
  -- (1) the cover term
  have hcover : (2 : ℝ) ^ ((1 - δ / 2) * M)
      * (∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal)
      ≤ (1 / 8 : ℝ) / 2 ^ K := by
    refine entropy_cover_sum_le 4 (by norm_num) G (X K) hne _ _ hη hε (DjE K k₄)
      (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
      (by rw [hεdef, div_lt_one (by linarith)]; linarith)
      (Nat.one_le_pow _ _ (show 0 < K ^ 2 by positivity)) ?_ (by positivity) (by positivity) ?_
    · have h := log_det_one_add_tensorGram_le' (K := K) hK1
      show Real.log (1 + tensorGram G.K G.s).det
        ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
      push_cast
      exact h
    · intro g hglo hghi
      have h := entropy_cover_bound (K := K) (m := k₄) (g := g) (η := η)
        (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)) (δ := δ)
        (by omega) ?_ hδ0.le hδ1.le ?_ hη ?_ le_rfl ?_ ?_
      · refine h.trans_eq ?_
        show (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) = (1 / 8 : ℝ) / 2 ^ K / 2 ^ G.rDim
        rw [show G.rDim = (K ^ 2) ^ K from rfl, pow_add]
        field_simp
      · rw [hK4]; push_cast; ring_nf; rfl
      · -- `92√K + 51 ≤ δ·K·log 2`, with `δ·K = 200√K`
        have hl2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hδK : δ * (K : ℝ) = 200 * Real.sqrt K := by
          rw [hδdef, div_mul_eq_mul_div, eq_comm, eq_div_iff hS0.ne']
          rw [mul_assoc, hSsq]
        rw [hδK]
        nlinarith [hS400, hl2, hS0]
      · rw [hηdef, ← pow_mul, hK4, mul_comm]
      · exact hglo
      · exact hghi
  -- (2) the Jackson term
  have hjack : 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) ≤ 1 / (8 * K) := by
    have h := jackson_term_small (K := K) (k₄ := k₄) hK1
    have hres : fr.res = (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ := by rw [hfrdef]; rfl
    rw [hres]
    exact h
  -- (3) `PropD` with the small allowances
  have hD : fr.PropD ((1 / 2 : ℝ) ^ k₄ + (1 / 2 : ℝ) ^ k₄) := by
    refine gridFrame_propD_of_bounds 4 (by norm_num) G (X K) (R K) (Y K) hne
      (show 0 < K from hK1) (R_ge_two K) (R_le_Y K)
      (Mx := ((X K + J K * gridDm K (N K) : ℕ) : ℝ)) ?_ ?_
      (Dm := gridDm K (N K)) (gridOf.d_le hK1) hη hε (DjE K k₄) ?_ ?_
    · have : 1 ≤ X K := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    · exact fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    · have h := hbig_small hK4 hK100
      simp only [Nat.cast_ofNat, rowL1_four, rowL2_four, hεdef, hηdef,
        show G.K = K from rfl, show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      ring_nf
      ring_nf at h
      linarith
    · have h := hfar_small hK4 hK100
      simp only [Nat.cast_ofNat, farBound_four, hεdef, hηdef,
        show G.K = K from rfl, show G.N = N K from rfl]
      exact h
  -- (4) `PropC` and the small-prime term
  set δ₃ : ℝ := smallPrimeBound (smallPrimes (R K) G.P₀) (Fintype.card G.Idx) (R K) (Mc K)
    (apSample (X K) G.P₀ G.b₀).card (Real.exp 1) (13 / 2)
    (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) with hδ₃def
  have hC : fr.PropC δ₃ :=
    gridFrame_propC_four G (X K) hne _ _ hη hε (R := R K)
      (fun p hp => (mem_smallPrimes.1 hp).1) (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := R_ge_two K; omega) (fun p hp => (mem_smallPrimes.1 hp).2.1)
      (by
        show 1 + Nat.clog 4 (2 ^ K * DjE K k₄) ≤ N K
        have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_DjE_le hK4 hK100)
        have hN : 1 ≤ N K := N_pos hK1
        omega)
      (Mc_pos hK1) (Real.one_le_exp zero_le_one) (by norm_num)
  have hδ₃nn : (0 : ℝ) ≤ δ₃ :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hsmall : (((2 * DjE K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ ≤ (1 / 8 : ℝ) / 2 ^ K := by
    have h := smallPrime_term_tiny hK4 hK100
    have hcard : Fintype.card G.Idx = T K := gridOf.card_Idx hK1
    rw [hδ₃def, hcard]
    exact h
  -- ### assemble
  have hmη : ((2 : ℝ)⁻¹) ^ k₄ ≤ η := by rw [hηdef]; norm_num
  have hmain := NormalNumbers.G4Entropy.entropy_gt_of_budget G (X K) hX (by norm_num)
    (smallPrimes (R K) G.P₀) (frozenGamma 4 G) hη hε (DjE K k₄) k₄ θr γr hθr hγr hmη
    (δ := δ) (M := M) hδ0 hδ1 hMpos hD hC hδ₃nn ?_
  · -- `(1 − δ)M = k₄H − 50√K H`
    have he : (1 - δ) * M
        = (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
          - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
      have hk4 : (k₄ : ℝ) = (K : ℝ) / 4 := by rw [hK4]; push_cast; ring
      rw [hMdef, hδdef, hk4]
      field_simp
      nlinarith [hSsq, hS0, hHcast]
    rw [he] at hmain
    exact hmain
  · -- the budget
    have h2K : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have hk₄2 : (k₄ : ℝ) ≤ (2 : ℝ) ^ k₄ := by
      have : k₄ < 2 ^ k₄ := Nat.lt_two_pow_self
      exact_mod_cast this.le
    -- each allowance is `≤ 5/K`
    have e1 : (1 / 8 : ℝ) / 2 ^ K ≤ 5 / (K : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith [h2K, hKpos]
    have ehalf : (1 / 2 : ℝ) ^ k₄ ≤ 5 / (K : ℝ) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ k₄ := by positivity
      have he : (1 / 2 : ℝ) ^ k₄ = 1 / (2 : ℝ) ^ k₄ := by rw [one_div_pow]
      rw [he, div_le_div_iff₀ hpos hKpos]
      have hKk : (K : ℝ) = 4 * (k₄ : ℝ) := by rw [hK4]; push_cast; ring
      nlinarith [hk₄2, hpos]
    have e2 : 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) ≤ 5 / (K : ℝ) := by
      refine hjack.trans ?_
      rw [div_le_div_iff₀ (by positivity) hKpos]
      linarith
    -- `δ/(2−δ) ≥ 100/√K ≥ 20/K`
    have h2d : (0 : ℝ) < 2 - δ := by linarith
    have hRHS : (100 : ℝ) / Real.sqrt K ≤ δ / (2 - δ) := by
      have hmono : δ / 2 ≤ δ / (2 - δ) :=
        div_le_div_of_nonneg_left hδ0.le h2d (by linarith)
      have hδ2 : δ / 2 = 100 / Real.sqrt K := by rw [hδdef]; ring
      linarith [hmono, hδ2.le, hδ2.ge]
    set B : ℝ := 5 / (K : ℝ) with hBdef
    have h25 : 5 * B < 100 / Real.sqrt K := by
      rw [hBdef, show (5 : ℝ) * (5 / (K : ℝ)) = 25 / (K : ℝ) by ring,
        div_lt_div_iff₀ hKpos hS0]
      nlinarith [hS400, hS0, hSsq]
    clear_value B
    have hfreq : gridFrame 4 (by norm_num) G (X K)
        (NormalNumbers.G4Entropy.apSample_nonempty G hX) (smallPrimes (R K) G.P₀)
        (frozenGamma 4 G) hη hε (DjE K k₄) = fr := rfl
    rw [hfreq]
    refine lt_of_le_of_lt (b := 5 * B) ?_ (lt_of_lt_of_le h25 hRHS)
    have t1 := hcover.trans e1
    have t2 := hsmall.trans e1
    set C : ℝ := (2 : ℝ) ^ ((1 - δ / 2) * M)
      * ∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal with hCdef
    set S : ℝ := (((2 * DjE K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ with hSdef
    set J : ℝ := 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) with hJdef
    set h₂ : ℝ := (1 / 2 : ℝ) ^ k₄ with hh₂def
    clear_value C S J h₂
    linarith only [t1, t2, e2, ehalf]

end Sched

end NormalNumbers.G4
