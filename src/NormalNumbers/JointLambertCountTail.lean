/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertGcdAverage

/-!
# The near and middle tail ranges

§4 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` splits the discrepancy tail
`∑_{m<M} ∑_{j≥k} τ(n_m + j) 2^{-j}` into three ranges.  This module proves the first two,
which are the ones carrying the *new* mathematics:

* **near** `k ≤ j < L`: the CRT still forces `gcd(R+j, A) = 1` (every allocation prime
  exceeds `L`), so the frozen coprime average `sum_tau_progression_le` applies;
* **middle** `L ≤ j < J`: coprimality may fail, and the price is exactly one factor `τ(A)`,
  via `sum_tau_progression_le_noncoprime`.

`near_middle_tail_le` is the combined bound

    ∑_{m<M} ∑_{j ∈ [k, J)} τ(R + j + mA) (1/2)^j ≤ W · (2 (1/2)^k + τ(A) · 2 (1/2)^L),

with `W = 2M(1 + log H) + 2H` the one divisor-average bracket.  The *structural* point of
the small-pool route is visible in this single inequality: the middle range pays `τ(A)` but
is discounted by `(1/2)^L = 2^{-k³}`, while `jointA_tau_le` bounds `τ(A)` by
`(a+1)(c+1)^{k²}`.  The cube beats the square, which is why the pool may be polynomial in
`k` rather than in `log X`.

The far range `j ≥ J` uses a different estimate (`τ(n) ≤ 2√n`) and is not in this file.
-/

namespace NormalNumbers.JointLambert

open Finset NormalNumbers.SwingC2

/-- `∑_{j ∈ [k, J)} (1/2)^j ≤ 2 (1/2)^k`. -/
theorem sum_half_Ico_le (k J : ℕ) :
    (∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j) ≤ 2 * (1 / 2 : ℝ) ^ k := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hrw : ∀ i ∈ range (J - k), (1 / 2 : ℝ) ^ (k + i) = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ i := by
    intro i _; rw [pow_add]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have := sum_geometric_two_le (J - k)
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  calc (1 / 2 : ℝ) ^ k * ∑ i ∈ range (J - k), (1 / 2 : ℝ) ^ i
      ≤ (1 / 2 : ℝ) ^ k * 2 := mul_le_mul_of_nonneg_left this hpos.le
    _ = 2 * (1 / 2 : ℝ) ^ k := by ring

/-- **Near + middle tail** (note §4).  `W = 2M(1 + log H) + 2H` is the divisor-average
bracket; the near range costs `2 (1/2)^k` copies of it and the middle range costs
`τ(A) · 2 (1/2)^L`. -/
theorem near_middle_tail_le {R A M H k L J : ℕ} (hA : 0 < A) (hR : 0 < R) (hH : 1 ≤ H)
    (hkL : k ≤ L) (hLJ : L ≤ J)
    (hbd : ∀ j, j < J → ∀ m, m < M → (R + j) + m * A ≤ H ^ 2)
    (hcop : ∀ j, k ≤ j → j < L → Nat.Coprime (R + j) A) :
    (∑ m ∈ range M, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
      ≤ (2 * M * (1 + Real.log H) + 2 * H)
          * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ L)) := by
  classical
  set W : ℝ := 2 * M * (1 + Real.log H) + 2 * H with hW
  have hlogH : (0 : ℝ) ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hWpos : (0 : ℝ) ≤ W := by rw [hW]; positivity
  -- swap the two sums
  have hswap : (∑ m ∈ range M, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
      = ∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j * ∑ m ∈ range M, (tau (R + j + m * A) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hswap]
  -- the per-`j` divisor average, with the `τ(A)` factor only in the middle range
  have hrow : ∀ j ∈ Ico k J,
      (1 / 2 : ℝ) ^ j * ∑ m ∈ range M, (tau (R + j + m * A) : ℝ)
        ≤ (1 / 2 : ℝ) ^ j * (if j < L then W else (tau A : ℝ) * W) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hRj : 0 < R + j := by omega
    have hbdj : ∀ m, m < M → (R + j) + m * A ≤ H ^ 2 := hbd j hj.2
    have hinner : (∑ m ∈ range M, (tau (R + j + m * A) : ℝ))
        ≤ (if j < L then W else (tau A : ℝ) * W) := by
      have hidx : ∀ m : ℕ, R + j + m * A = (R + j) + m * A := fun m => by ring
      by_cases hjL : j < L
      · simp only [hjL, if_true]
        have := sum_tau_progression_le (u := R + j) (A := A) (H := H) (M := M)
          hRj (hcop j hj.1 hjL) hH hbdj
        simpa [hidx, hW] using this
      · simp only [hjL, if_false]
        have := sum_tau_progression_le_noncoprime (u := R + j) (A := A) (H := H) (M := M)
          hRj hA hH hbdj
        simpa [hidx, hW] using this
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  refine le_trans (Finset.sum_le_sum hrow) ?_
  -- split the range at `L`
  have hsplit : (∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j * (if j < L then W else (tau A : ℝ) * W))
      = (∑ j ∈ Ico k L, (1 / 2 : ℝ) ^ j * W)
        + ∑ j ∈ Ico L J, (1 / 2 : ℝ) ^ j * ((tau A : ℝ) * W) := by
    rw [← Finset.sum_Ico_consecutive _ hkL hLJ]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      simp [hj.2]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      simp [Nat.not_lt.mpr hj.1]
  rw [hsplit, ← Finset.sum_mul, ← Finset.sum_mul]
  have hτ : (0 : ℝ) ≤ (tau A : ℝ) := by positivity
  have h1 : (∑ j ∈ Ico k L, (1 / 2 : ℝ) ^ j) * W ≤ (2 * (1 / 2 : ℝ) ^ k) * W :=
    mul_le_mul_of_nonneg_right (sum_half_Ico_le k L) hWpos
  have h2 : (∑ j ∈ Ico L J, (1 / 2 : ℝ) ^ j) * ((tau A : ℝ) * W)
      ≤ (2 * (1 / 2 : ℝ) ^ L) * ((tau A : ℝ) * W) :=
    mul_le_mul_of_nonneg_right (sum_half_Ico_le L J) (by positivity)
  nlinarith [h1, h2]

/-! ### Permanent boundary controls -/

/-- Empty tail range: `k = J` gives the zero sum, and the bound is nonnegative. -/
example {R A M H k : ℕ} (hA : 0 < A) (hR : 0 < R) (hH : 1 ≤ H) :
    (∑ m ∈ range M, ∑ j ∈ Ico k k, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j) = 0 := by
  simp

/-- Degenerate `M = 0`: no candidate indices, zero tail. -/
example {R A H k J : ℕ} :
    (∑ m ∈ range 0, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j) = 0 := by
  simp

/-- `L = k` collapses the near range: every `j` is paid at `τ(A)`.  This is the control that
the middle-range factor is not silently dropped. -/
example : (2 : ℝ) * (1 / 2 : ℝ) ^ 3 + (tau 12 : ℝ) * (2 * (1 / 2 : ℝ) ^ 3)
    = 2 * (1 / 2 : ℝ) ^ 3 * (1 + (tau 12 : ℝ)) := by ring

/-- `τ(12) = 6`, so the middle-range factor is genuinely larger than `1`. -/
example : tau 12 = 6 := by decide

end NormalNumbers.JointLambert
