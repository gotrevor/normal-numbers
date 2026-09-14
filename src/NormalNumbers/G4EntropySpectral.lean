/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Tensor
import NormalNumbers.G4EntropyTiling

/-!
# How much of `entropy_E1`'s `√K` deficit is real?

Lap 32 traced the expedition's word-length ceiling `ℓ = o(m_K/δ_K)` back to
`log_det_one_add_tensorGram_le'`, whose `23√K` comes from bounding each
`log(1 + Λ_j) ≤ log 2 + |log Λ_j|` and then applying Cauchy–Schwarz to `∑_j |log Λ_j|`.

The `|·|` is visibly lossy: for `Λ ≪ 1` one has `log(1+Λ) ≈ Λ`, not `|log Λ|`.  This module
carries out the refinement and measures exactly what it buys.

* `log_one_add_le_log_two_add_posPart` — `log(1+Λ) ≤ log 2 + (log Λ)^+`.
* `log_det_one_add_tensorGram_le_pos` — the resulting determinant bound, with the
  fluctuation term **halved** and an explicit mean term `K s^{K−1} log(s+1)`, via
  `(x)^+ = (|x| + x)/2` and the exact first moment `∑_j ∑_i log λ_{j_i} = K s^{K−1} log(s+1)`.
* `log_det_one_add_tensorGram_le_twelve` — at `s = K²`, `K ≥ 4`:
  `log det(1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 12√K)`, against the `23√K` in use.

**The verdict of lap 32 stands, and is now quantitative**: the positive part halves the
*constant* (23 → 12, hence the cover floor `92√K` → `48√K` and `entropy_E1`'s `50√K` → `≈25√K`)
and does **not** touch the order.  The `√K` survives because the log-spectrum is centred: the
mean term is `O(s^K log K/K)`, negligible beside the `√K` fluctuation, so about half the tensor
eigenvalues genuinely exceed `1` by `e^{Θ(√K)}`.  `δ_K ≍ √K` is a wall of this route.

Nothing here re-proves `entropy_E1`, which is frozen; this is the measurement the probe asked
for, kept in its own module.
-/

open Finset Real

namespace NormalNumbers.G4

/-- `log(1 + Λ) ≤ log 2 + (log Λ)^+` for `Λ > 0`: the positive-part sharpening of
`log_one_add_le_log_two_add_abs_log`, exact for `Λ ≤ 1`. -/
theorem log_one_add_le_log_two_add_posPart {Λ : ℝ} (h : 0 < Λ) :
    Real.log (1 + Λ) ≤ Real.log 2 + max (Real.log Λ) 0 := by
  rcases le_or_gt Λ 1 with h1 | h1
  · have := Real.log_le_log (by positivity) (show 1 + Λ ≤ 2 by linarith)
    have : (0 : ℝ) ≤ max (Real.log Λ) 0 := le_max_right _ _
    linarith [Real.log_le_log (by positivity : (0:ℝ) < 1 + Λ) (show 1 + Λ ≤ 2 by linarith)]
  · have hlog : Real.log (1 + Λ) ≤ Real.log 2 + Real.log Λ := by
      have := Real.log_le_log (by positivity) (show 1 + Λ ≤ 2 * Λ by linarith)
      rwa [Real.log_mul (by norm_num) (by linarith)] at this
    have : Real.log Λ ≤ max (Real.log Λ) 0 := le_max_left _ _
    linarith

/-- The exact first moment of the tensor log-spectrum:
`∑_j ∑_i log λ_{j_i} = K s^{K−1} log(s+1)`, written as `K s^K log(s+1)/s`. -/
theorem sum_log_tensorLam {s : ℕ} (hs : 1 ≤ s) (K : ℕ) :
    ∑ j : Fin K → Fin s, Real.log (tensorLam K s j)
      = (K : ℝ) * (s : ℝ) ^ K * (Real.log (s + 1) / s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h := sum_pi_linear (s := s) (fun k => Real.log (lam s k)) K
  rw [sum_log_lam] at h
  have hL : ∑ j : Fin K → Fin s, Real.log (tensorLam K s j)
      = ∑ j : Fin K → Fin s, ∑ i, Real.log (lam s (j i)) :=
    Finset.sum_congr rfl fun j _ => log_tensorLam j
  rw [hL]
  field_simp
  linarith [h]

/-- **The positive-part determinant bound.**  The fluctuation term is halved and an explicit
(small, positive) mean term appears. -/
theorem log_det_one_add_tensorGram_le_pos {s : ℕ} (hs : 1 ≤ s) (K : ℕ) :
    Real.log (1 + tensorGram K s).det
      ≤ (s : ℝ) ^ K * Real.log 2
        + (1 / 2) * ((s : ℝ) ^ K * Real.sqrt ((K : ℝ) * ((∑ k, Real.log (lam s k) ^ 2) / s)
              + (K : ℝ) * (K - 1) * (Real.log (s + 1) / s) ^ 2)
            + (K : ℝ) * (s : ℝ) ^ K * (Real.log (s + 1) / s)) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [det_one_add_tensorGram, Real.log_prod (fun j _ => by linarith [tensorLam_pos (K := K) j])]
  have hstep : ∑ j : Fin K → Fin s, Real.log (1 + tensorLam K s j)
      ≤ (s : ℝ) ^ K * Real.log 2
        + ∑ j : Fin K → Fin s, max (Real.log (tensorLam K s j)) 0 := by
    calc ∑ j : Fin K → Fin s, Real.log (1 + tensorLam K s j)
        ≤ ∑ j : Fin K → Fin s, (Real.log 2 + max (Real.log (tensorLam K s j)) 0) :=
          Finset.sum_le_sum fun j _ => log_one_add_le_log_two_add_posPart (tensorLam_pos j)
      _ = (s : ℝ) ^ K * Real.log 2
            + ∑ j : Fin K → Fin s, max (Real.log (tensorLam K s j)) 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  refine hstep.trans ?_
  -- `(x)^+ = (|x| + x)/2`
  have hmax : ∑ j : Fin K → Fin s, max (Real.log (tensorLam K s j)) 0
      = (1 / 2) * ((∑ j : Fin K → Fin s, |Real.log (tensorLam K s j)|)
          + ∑ j : Fin K → Fin s, Real.log (tensorLam K s j)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases le_or_gt 0 (Real.log (tensorLam K s j)) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h.le, abs_of_neg h]; ring
  rw [hmax, sum_log_tensorLam hs K]
  -- Cauchy–Schwarz on the absolute part, exactly as in `log_det_one_add_tensorGram_le`
  have habs : ∑ j : Fin K → Fin s, |Real.log (tensorLam K s j)|
      ≤ (s : ℝ) ^ K * Real.sqrt ((K : ℝ) * ((∑ k, Real.log (lam s k) ^ 2) / s)
          + (K : ℝ) * (K - 1) * (Real.log (s + 1) / s) ^ 2) := by
    have hL : ∀ j : Fin K → Fin s, Real.log (tensorLam K s j) = ∑ i, Real.log (lam s (j i)) :=
      fun j => log_tensorLam j
    calc ∑ j : Fin K → Fin s, |Real.log (tensorLam K s j)|
        = ∑ j : Fin K → Fin s, |∑ i, Real.log (lam s (j i))| := by
          simp_rw [hL]
      _ ≤ Real.sqrt ((Fintype.card (Fin K → Fin s) : ℝ)
            * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2) :=
          sum_abs_le_sqrt_card_mul_sum_sq _
      _ = Real.sqrt (((s : ℝ) ^ K) ^ 2
            * ((K : ℝ) * ((∑ k, Real.log (lam s k) ^ 2) / s)
              + (K : ℝ) * (K - 1) * (Real.log (s + 1) / s) ^ 2)) := by
          congr 1
          have h := sum_pi_sq (s := s) (fun k => Real.log (lam s k)) K
          rw [sum_log_lam] at h
          simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          push_cast
          have hs2 : (s : ℝ) ^ 2 ≠ 0 := by positivity
          rw [show (s : ℝ) ^ K * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2
              = (s : ℝ) ^ K * ((s : ℝ) ^ 2
                  * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2) / (s : ℝ) ^ 2 by
            field_simp, h]
          field_simp
          ring
      _ = (s : ℝ) ^ K * Real.sqrt ((K : ℝ) * ((∑ k, Real.log (lam s k) ^ 2) / s)
            + (K : ℝ) * (K - 1) * (Real.log (s + 1) / s) ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  linarith

/-- **The measured gain at `s = K²`.**  For `K ≥ 4`,

    `log det(1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 12√K)`,

against the `23√K` that `log_det_one_add_tensorGram_le'` supplies and `entropy_E1` consumes.
The constant nearly halves; the order does not move. -/
theorem log_det_one_add_tensorGram_le_twelve {K : ℕ} (hK : 4 ≤ K) :
    Real.log (1 + tensorGram K (K ^ 2)).det
      ≤ ((K : ℝ) ^ 2) ^ K * (Real.log 2 + 12 * Real.sqrt K) := by
  have hK1 : 1 ≤ K := by omega
  have hK' : (4 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK1
  have h := log_det_one_add_tensorGram_le_pos hs K
  push_cast at h
  refine h.trans ?_
  have hS : (2 : ℝ) ≤ Real.sqrt K := by
    have h1 : Real.sqrt (4 : ℝ) ≤ Real.sqrt K := Real.sqrt_le_sqrt hK'
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h1
  -- the fluctuation, as in `log_det_one_add_tensorGram_le'`
  have hfluc : Real.sqrt ((K : ℝ) * ((∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2)
      + (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2)
      ≤ 23 * Real.sqrt K := by
    have hμ₂ : (∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2 ≤ 520 := by
      rw [div_le_iff₀ (by positivity)]
      have := sum_sq_log_lam_le' hs
      push_cast at this
      linarith
    have hlog : Real.log ((K : ℝ) ^ 2 + 1) ≤ 2 * K := by
      have h1 : Real.log ((K : ℝ) ^ 2 + 1) ≤ Real.log (((K : ℝ) + 1) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at h1
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 1 by positivity)
      push_cast at h1
      linarith
    have hl0 : 0 ≤ Real.log ((K : ℝ) ^ 2 + 1) := Real.log_nonneg (by nlinarith)
    have hμ₁ : (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2 ≤ 4 := by
      have hKK : (K : ℝ) * (K - 1) ≤ (K : ℝ) ^ 2 := by nlinarith
      calc (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2
          ≤ (K : ℝ) ^ 2 * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2 := by gcongr
        _ = (Real.log ((K : ℝ) ^ 2 + 1) / K) ^ 2 := by field_simp
        _ ≤ 4 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
            gcongr
            rw [div_le_iff₀ (by positivity)]; linarith
    have hKpos : (0 : ℝ) < K := by linarith
    have hinner : (K : ℝ) * ((∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2)
        + (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2
        ≤ 529 * (K : ℝ) := by nlinarith
    calc Real.sqrt _ ≤ Real.sqrt (529 * (K : ℝ)) := Real.sqrt_le_sqrt hinner
      _ = 23 * Real.sqrt K := by
          rw [show (529 : ℝ) = 23 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
  -- the mean term is `O(log K / K)` — negligible
  have hmean : (K : ℝ) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ≤ 2 := by
    have hlog : Real.log ((K : ℝ) ^ 2 + 1) ≤ 2 * K := by
      have h1 : Real.log ((K : ℝ) ^ 2 + 1) ≤ Real.log (((K : ℝ) + 1) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at h1
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 1 by positivity)
      push_cast at h1
      linarith
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpow : (0 : ℝ) < ((K : ℝ) ^ 2) ^ K := by positivity
  have hkey : (1 / 2 : ℝ) * (23 * Real.sqrt K + 2) ≤ 12 * Real.sqrt K := by linarith
  calc ((K : ℝ) ^ 2) ^ K * Real.log 2
        + (1 / 2) * (((K : ℝ) ^ 2) ^ K * Real.sqrt ((K : ℝ)
            * ((∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2)
            + (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2)
          + (K : ℝ) * ((K : ℝ) ^ 2) ^ K * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2))
      ≤ ((K : ℝ) ^ 2) ^ K * Real.log 2
        + (1 / 2) * (((K : ℝ) ^ 2) ^ K * (23 * Real.sqrt K) + ((K : ℝ) ^ 2) ^ K * 2) := by
        have h1 : ((K : ℝ) ^ 2) ^ K * Real.sqrt ((K : ℝ)
            * ((∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2)
            + (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2)
            ≤ ((K : ℝ) ^ 2) ^ K * (23 * Real.sqrt K) := by
          exact mul_le_mul_of_nonneg_left hfluc hpow.le
        have h2 : (K : ℝ) * ((K : ℝ) ^ 2) ^ K * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2)
            ≤ ((K : ℝ) ^ 2) ^ K * 2 := by
          have := mul_le_mul_of_nonneg_left hmean hpow.le
          nlinarith [this]
        linarith
    _ ≤ ((K : ℝ) ^ 2) ^ K * (Real.log 2 + 12 * Real.sqrt K) := by nlinarith [hpow, hkey]

end NormalNumbers.G4
