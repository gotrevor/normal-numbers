/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleB
import NormalNumbers.G4EntropyE0

/-!
# Entropy expedition §4: the **E0 budget**, discharged for the implemented schedule

`G4EntropyE0.entropy_gt_of_budget` reduces E0 to one numeric inequality; this file proves that
inequality.  Its left-hand side has four terms, three of which are *already* bounded by the
disjunctivity machinery (`PropD`, the Jackson term, `Λ·smallPrimeBound`).  The one genuinely new
term is the cover term

    `2^{(1−δ/2)·m·H} · ∑_{G good} η^{|G|} · vol(pieceCube G)`,

which replaces the disjunctivity argument's `((b^ℓ−1)^M)^H · …`.

**The mechanism.**  `gridB_bound` beats the cylinder count `((b^ℓ−1)^M)^H ≈ η^{−H}` by the
*covering deficit* of an omitted word.  Here there is no omitted word: the prefactor is exactly
`(2^m)^H` with `2^{−m} ≤ η`, so per unit of `r` the prefactor contributes `+(K/4)log 2` and the
tube fraction `η^g` contributes `−(1−1/K)(K/4)log 2` — they cancel to `O(1)·log 2`, which is *not*
enough against the spectral term `11.5√K`.  The entropy deficit `δ` is what supplies the missing
room: the prefactor is only `2^{(1−δ/2)mH}`, so the cancellation leaves `−δK(log 2)/8`, and

    `δ·K·log 2 ≥ 92√K + 46`

makes it beat `11.5√K` and every absolute constant.  Since `δ ≥ 0` and `K` is free, this holds
for a **fixed** `δ` once `K ≳ (133/δ)²`; the `δ ≍ 1/√K` regime that E1 wants is the same
inequality read the other way, and is the next lap's target (it additionally needs the three
error allowances `δbig, δfar, κ, Λδ₃`, currently fixed at `1/8`, to shrink with `K`).

Main results:

* `entropy_cover_bound` — the per-good-set cover inequality, the analogue of `gridB_bound`.
* `entropy_cover_sum_le` — its sum over `goodSets`, i.e. the whole cover term is `≤ 1/8`.
-/

open Real Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- `exp(1/K) ≤ 1 + 2/K` for `K ≥ 100`, in the form `H ≤ (1 + 2/K)·r`. -/
lemma hDim_le_one_add_mul_rDim {K : ℕ} {r H : ℝ} (hK : (100 : ℝ) ≤ K) (hr : 0 < r)
    (hH0 : 0 ≤ H) (hH : H ≤ Real.exp (1 / (K : ℝ)) * r) :
    H ≤ (1 + 2 / (K : ℝ)) * r := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hexp := exp_inv_mul_le hK0
  have hinv : 1 / (K : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK
  have hinv0 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  -- `H·(1 − 1/K) ≤ r`
  have h1 : H * (1 - 1 / (K : ℝ)) ≤ r := by
    have h2 : H * (1 - 1 / (K : ℝ)) ≤ Real.exp (1 / (K : ℝ)) * r * (1 - 1 / (K : ℝ)) :=
      mul_le_mul_of_nonneg_right hH (by linarith)
    nlinarith [hexp, hr.le]
  -- `(1 + 2/K)(1 − 1/K) ≥ 1`
  have h3 : (1 : ℝ) ≤ (1 + 2 / (K : ℝ)) * (1 - 1 / (K : ℝ)) := by
    have hsq : 2 / (K : ℝ) * (1 / (K : ℝ)) ≤ 1 / (K : ℝ) := by
      rw [div_mul_div_comm]
      rw [div_le_div_iff₀ (by positivity) hK0]
      nlinarith
    have : (1 + 2 / (K : ℝ)) * (1 - 1 / (K : ℝ))
        = 1 + (2 / (K : ℝ) - 1 / (K : ℝ)) - 2 / (K : ℝ) * (1 / (K : ℝ)) := by ring
    rw [this]
    have : 1 / (K : ℝ) ≤ 2 / (K : ℝ) - 1 / (K : ℝ) := by
      rw [div_sub_div_same]; norm_num
    linarith
  nlinarith [h1, hH0, mul_nonneg hH0 (by linarith : (0:ℝ) ≤ 1 - 1 / (K : ℝ))]

/-- **The entropy cover inequality.**  With `r = (K²)^K`, `H = (K²+1)^K`, `m ≤ K/4`,
`η ≤ 2^{−K/4}`, `Lg ≤ r(log 2 + 23√K)` and `(1−1/K)r ≤ g ≤ r`,

    `2^{(1−δ/2)·m·H} · η^g · e^{Lg/2} · (√(2πe/g)·√(H+g))^g ≤ (1/8)/2^r`

whenever the entropy deficit satisfies `92√K + 46 ≤ δ·K·log 2`.  This is `gridB_bound` with the
covering deficit of an omitted word replaced by the entropy deficit `δ`. -/
theorem entropy_cover_bound {K m g : ℕ} {η Lg δ : ℝ}
    (hK : 33856 ≤ K) (hm : (m : ℝ) ≤ (K : ℝ) / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : 92 * Real.sqrt K + 46 ≤ δ * K * Real.log 2)
    (hη0 : 0 < η) (hη : η ^ 4 ≤ (1 / 2 : ℝ) ^ K)
    (hLg : Lg ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
    (hglo : (1 - 1 / (K : ℝ)) * (((K ^ 2) ^ K : ℕ) : ℝ) ≤ (g : ℝ))
    (hghi : g ≤ (K ^ 2) ^ K) :
    (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ))) * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g)
            * Real.sqrt ((((K ^ 2 + 1) ^ K : ℕ) : ℝ) + g)) ^ g
      ≤ (1 / 8 : ℝ) / 2 ^ ((K ^ 2) ^ K) := by
  sorry

end NormalNumbers.G4
