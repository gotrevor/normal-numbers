/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyE0Down
import NormalNumbers.G4EntropyRate

/-!
# **E1 downward**: the `200/√K` rate survives shrinking the outer scale

`G4EntropyE0Down` ports `entropy_E0` (deficit `4/5`) to every outer scale `X' ∈ [Xlo K, X K]`.
Everything downstream of the entropy input — the capture inequality, the atom deficit, the band
laws — consumes `entropy_E1` (deficit `50√K`), not `entropy_E0`.  This module ports E1.

The port is the same three leaves, because the `X`-sensitive inputs of `entropy_E1` are exactly
the `X`-sensitive inputs of `entropy_E0` at different allowances:

| E1's leaf | its `X`-sensitive inputs | replaced by |
|---|---|---|
| `hbig_small` | `sample_term_le`, `log_Mx_div_le` | `sample_term_le_down`, `log_Mx_div_le_down` |
| `hfar_small` | `hfar_holds` | `hfar_holds_down` |
| `smallPrimeBound_tiny` | `term_a_le`, `term_d_le` | `term_a_le_down`, `term_d_le_down` |

Nothing else in the E1 cone noticed the substitution `X K → X'` — the cover term, the Jackson
term, `PropC`'s combinatorics and the budget arithmetic are all literally `X`-free.

> **`Sched.entropy_E1_down`** — for every `K = 4k₄ ≥ 160000` and every `Xlo K ≤ X' ≤ X K`,
> `m_K·H_K − 50√K·H_K < H₂(Z^{G4}_{K,X'})`.

**What it is for.**  A position cutoff inside band `i` selects the truncated sample `n ≤ X'`
(window starts `2·kIdx(n,α)` increase in `n`), so a *mid-band prefix* of the read is itself a
sample at the smaller outer scale `X'`.  With `entropy_E1_down` that prefix carries its own
certificate, instead of paying the restriction price `|P_K|/a` of
`abs_midRead_freq_sub_le` — which is what limits the current mid-band bound to cutoffs beyond a
`K^{−1/2}` fraction of the band.  The floor is `Xlo K = √(X K)`, and
`G4EntropyScaleGap.Xhi_lt_Xlo_step` shows that floor cannot be lowered to meet the previous rung:
the head of each band stays uncertified.  So this module sharpens mid-band prefix control from a
`K^{−1/2}` fraction to an `X^{−1/2}` fraction, and no further.
-/

open Finset Real MeasureTheory
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The small-prime term at a truncated scale -/

lemma smallPrimeBound_tiny_down {K X' : ℕ} (hK : 100 ≤ K) (hlo : Xlo K ≤ X') :
    smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
        (T K) (R K) (Mc K)
        (apSample (X') (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K)) := by
  have hbig : (2 : ℝ) ^ (2 * (K * (K ^ 2) ^ K))
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
        (T K) (R K) (Mc K)
        (apSample (X') (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
        (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ 3 * Real.exp (-4) + 1 / 32 := by
    unfold smallPrimeBound
    exact budget_terms_le le_rfl (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (main_term_le hK) (term_a_le_down hK hlo)
      (term_b_le hK) (term_c_le hK) (term_d_le_down hK hlo)
  have he4 := exp_neg_four_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hbig, he4]
lemma smallPrime_term_tiny_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlo K ≤ X') :
    (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample (X') (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) / (2 : ℝ) ^ K := by
  have hk : 25 ≤ k₄ := by omega
  have hq := smallPrimeBound_tiny_down hK hlo
  have hΛ := LambdaE_le hK4 hk
  have hq0 : (0 : ℝ) ≤ smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
      (T K) (R K) (Mc K)
      (apSample (X') (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
      (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K) :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hstep : (((2 * DjE K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample (X') (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
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


/-! ### `δbig` and `δfar` at a truncated scale -/

theorem hbig_small_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X') (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K)) * (1 / 2 : ℝ) ^ K / 3
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
  have hs2 := sample_term_le_down hK hlo
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample (X') (gridOf K (N K) (by omega)).P₀
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
          / ((apSample (X') (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ)
        ≤ 2 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K + (1 / 8 : ℝ) ^ K := add_le_add hfac hs2
      _ ≤ 4 * (K : ℝ) ^ 2 * (1 / 8 : ℝ) ^ K := by nlinarith
      _ = (2 * K * a ^ 6) ^ 2 := by rw [h8K]; ring
  have ht3 : (Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K))
        * (1 / 2 : ℝ) ^ K / 3 ≤ 34 * a ^ 4 := by
    have := log_Mx_div_le_down hK hlo hhi
    have hl : 0 ≤ Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hXp : 0 < X' := by have := Xlo_pos K; omega
        have hX1 : (1 : ℝ) ≤ X' := by exact_mod_cast hXp
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

theorem hfar_small_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) (X') (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 2 : ℝ) ^ k₄ * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have h := hfar_holds_down hK hlo hhi
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


/-! ### The assembly -/

set_option maxHeartbeats 2000000 in
theorem entropy_E1_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 160000 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
        - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
      < (NormalNumbers.G4Entropy.jointLaw (gridOf K (N K) (by omega))
          (b₀_lt_of_Xlo_le (show 100 ≤ K by omega) hlo) k₄ (primeLambertAtBase 4)).H₂ := by
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
  set hX := b₀_lt_of_Xlo_le (show 100 ≤ K by omega) hlo with hXdef
  set η : ℝ := (1 / 2 : ℝ) ^ k₄ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; positivity
  set ε : ℝ := 1 / (K : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set hne := NormalNumbers.G4Entropy.apSample_nonempty G hX with hnedef
  set fr := gridFrame 4 (by norm_num) G (X') hne (smallPrimes (R K) G.P₀)
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
    refine entropy_cover_sum_le 4 (by norm_num) G (X') hne _ _ hη hε (DjE K k₄)
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
    refine gridFrame_propD_of_bounds 4 (by norm_num) G (X') (R K) (Y K) hne
      (show 0 < K from hK1) (R_ge_two K) (R_le_Y K)
      (Mx := ((X' + J K * gridDm K (N K) : ℕ) : ℝ)) ?_ ?_
      (Dm := gridDm K (N K)) (gridOf.d_le hK1) hη hε (DjE K k₄) ?_ ?_
    · have : 1 ≤ X' := by have := Xlo_pos K; omega
      exact_mod_cast le_add_right this
    · exact fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    · have h := hbig_small_down hK4 hK100 hlo hhi
      simp only [Nat.cast_ofNat, rowL1_four, rowL2_four, hεdef, hηdef,
        show G.K = K from rfl, show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      ring_nf
      ring_nf at h
      linarith
    · have h := hfar_small_down hK4 hK100 hlo hhi
      simp only [Nat.cast_ofNat, farBound_four, hεdef, hηdef,
        show G.K = K from rfl, show G.N = N K from rfl]
      exact h
  -- (4) `PropC` and the small-prime term
  set δ₃ : ℝ := smallPrimeBound (smallPrimes (R K) G.P₀) (Fintype.card G.Idx) (R K) (Mc K)
    (apSample (X') G.P₀ G.b₀).card (Real.exp 1) (13 / 2)
    (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) with hδ₃def
  have hC : fr.PropC δ₃ :=
    gridFrame_propC_four G (X') hne _ _ hη hε (R := R K)
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
    have h := smallPrime_term_tiny_down hK4 hK100 hlo
    have hcard : Fintype.card G.Idx = T K := gridOf.card_Idx hK1
    rw [hδ₃def, hcard]
    exact h
  -- ### assemble
  have hmη : ((2 : ℝ)⁻¹) ^ k₄ ≤ η := by rw [hηdef]; norm_num
  have hmain := NormalNumbers.G4Entropy.entropy_gt_of_budget G (X') hX (by norm_num)
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
    have hfreq : gridFrame 4 (by norm_num) G (X')
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
