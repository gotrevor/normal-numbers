/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LogTwoSqKicked

/-!
# Lane-2 discharge of the frozen node `LogTwoSqSeries`

Batch-2 target 1 (2026-08-29 operator brief v2).  The one obligation of
this file is `logTwoSqSeries_proved : LogTwoSqSeries`, i.e.

  `log² 2 = Σ_{m≥0} (2·H_m/(m+1)) · 2^{−(m+1)}`

(in the machine's shifted indexing).  Route: `log 2 = Σ_{k≥1} 2^{−k}/k`
(`−log(1−x)` Taylor series at `x = 1/2`), square it; the Cauchy product
of the series with itself has `m`-th coefficient
`Σ_{i+j=m, i,j≥1} 1/(i·j)`, and the partial-fraction identity
`1/(i·j) = (1/(i+j))·(1/i + 1/j)` collapses it to `2·H_{m−1}/m`.
Absolute convergence on the disk makes the Cauchy product legal —
mathlib: `Complex.hasSum_taylorSeries_neg_log` (or the real
`Real.hasSum_log_sub_one`-family; check what exists), plus the
summable-norm Cauchy product API (`HasSum.mul_eq` /
`summable_norm_mul_of_summable_norm` family).  Probe already green:
`experiments/logtwosq_series.py` (identity verified to 70 digits).
-/

namespace NormalNumbers

namespace LogTwoSqSeriesProof

open Finset

/-- The log-2 series term: `f k = 2^{−(k+1)}/(k+1)`, so `Σ f = log 2`. -/
noncomputable def f (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1) / (k + 1)

lemma f_nonneg (k : ℕ) : 0 ≤ f k := by unfold f; positivity

lemma hasSum_f : HasSum f (Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := (1 / 2 : ℝ)) (by rw [abs_of_pos] <;> norm_num)
  have h2 : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rwa [h2, Real.log_inv, neg_neg] at h

lemma summable_norm_f : Summable fun k => ‖f k‖ := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (f_nonneg _)] using hasSum_f.summable

/-- Partial fractions on one Cauchy-product term: with `i = k+1`,
`j = n−k+1`, `i + j = n + 2`, so `1/(i·j) = (1/(n+2))·(1/i + 1/j)`. -/
lemma term_partial_fraction {n k : ℕ} (hk : k ≤ n) :
    (1 / ((k : ℝ) + 1)) * (1 / (((n - k : ℕ) : ℝ) + 1)) =
      (1 / ((n : ℝ) + 2)) * (1 / ((k : ℝ) + 1) + 1 / (((n - k : ℕ) : ℝ) + 1)) := by
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
  rw [hcast]
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) - (k : ℝ) + 1 := by
    have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    linarith
  have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  field_simp
  ring

/-- The Cauchy-product coefficient identity:
`Σ_{k=0}^{n} 1/((k+1)(n−k+1)) = 2·H_{n+1}/(n+2)`. -/
lemma sum_inv_mul_eq (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 / ((k : ℝ) + 1)) * (1 / (((n - k : ℕ) : ℝ) + 1)) =
      2 * harmonicR (n + 1) / ((n : ℝ) + 2) := by
  have hsplit : ∀ k ∈ range (n + 1),
      (1 / ((k : ℝ) + 1)) * (1 / (((n - k : ℕ) : ℝ) + 1)) =
        (1 / ((n : ℝ) + 2)) * (1 / ((k : ℝ) + 1) + 1 / (((n - k : ℕ) : ℝ) + 1)) :=
    fun k hk => term_partial_fraction (Nat.lt_succ_iff.mp (mem_range.mp hk))
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hrefl : ∑ k ∈ range (n + 1), (1 / (((n - k : ℕ) : ℝ) + 1)) =
      ∑ k ∈ range (n + 1), (1 / ((k : ℝ) + 1)) := by
    simpa using Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) (n + 1)
  rw [hrefl]
  have hH : ∑ k ∈ range (n + 1), (1 / ((k : ℝ) + 1)) = harmonicR (n + 1) := rfl
  rw [hH]; ring

/-- The Cauchy product of the log-2 series with itself, coefficientwise
rewritten into the machine's kick terms (index shifted by one). -/
lemma cauchy_term_eq (n : ℕ) :
    ∑ k ∈ range (n + 1), f k * f (n - k) =
      logTwoSqKick (n + 2) / (2 : ℝ) ^ (n + 2) := by
  have hterm : ∀ k ∈ range (n + 1),
      f k * f (n - k) =
        (1 / 2 : ℝ) ^ (n + 2) *
          ((1 / ((k : ℝ) + 1)) * (1 / (((n - k : ℕ) : ℝ) + 1))) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    unfold f
    rw [div_mul_div_comm, ← pow_add]
    have hpow : k + 1 + (n - k + 1) = n + 2 := by omega
    rw [hpow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_inv_mul_eq]
  unfold logTwoSqKick
  have h1 : (n + 2) - 1 = n + 1 := by omega
  have h2 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [h1, h2, div_pow, one_pow]
  ring

/-- The shifted series (the Cauchy product itself) sums to `log² 2`. -/
lemma hasSum_shifted :
    HasSum (fun n : ℕ => logTwoSqKick (n + 2) / (2 : ℝ) ^ (n + 2))
      (Real.log 2 ^ 2) := by
  have h := hasSum_sum_range_mul_of_summable_norm
    (f := f) (g := f) summable_norm_f summable_norm_f
  rw [hasSum_f.tsum_eq, ← sq] at h
  exact funext cauchy_term_eq ▸ h

end LogTwoSqSeriesProof

open LogTwoSqSeriesProof in
/-- **Lane-2 discharge of the frozen node `LogTwoSqSeries`**: the
harmonic-weighted series sums to `log² 2`. -/
theorem logTwoSqSeries_proved : LogTwoSqSeries := by
  unfold LogTwoSqSeries
  have h := (hasSum_nat_add_iff (f := fun m : ℕ =>
    logTwoSqKick (m + 1) / (2 : ℝ) ^ (m + 1)) 1).mp
    (by simpa [add_assoc] using hasSum_shifted)
  have h0 : ∑ i ∈ Finset.range 1,
      logTwoSqKick (i + 1) / (2 : ℝ) ^ (i + 1) = 0 := by
    simp [logTwoSqKick, harmonicR]
  rwa [h0, add_zero] at h

end NormalNumbers
