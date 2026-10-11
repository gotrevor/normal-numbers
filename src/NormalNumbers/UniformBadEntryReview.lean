/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadNextReview

namespace NormalNumbers.UniformBadThreshold.NextReview

/-- Converting a block inequality with normalized transition weights back to
ordinary descendant counts multiplies the candidate by the binary state weight.
Thus a numerical vector `V` used with transitions `r_child / (lambda * r_parent)`
represents cell weights `r_state * V_state`, not `V_state` alone. -/
theorem normalized_block_weight_transfer {ι : Type*} [Fintype ι]
    (D : ℕ) (g lam r v : ℚ) (R V : ι → ℚ)
    (hlam : 0 < lam) (hr : 0 < r)
    (h : (g / lam) ^ D * v ≤ ∑ i, (R i / (lam ^ D * r)) * V i) :
    g ^ D * (r * v) ≤ ∑ i, R i * V i := by
  have hs : (∑ i, (R i / (lam ^ D * r)) * V i) =
      (∑ i, R i * V i) / (lam ^ D * r) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, le_div_iff₀ (mul_pos (pow_pos hlam D) hr)] at h
  have he : (g / lam) ^ D * v * (lam ^ D * r) = g ^ D * (r * v) := by
    rw [div_pow]
    field_simp
  rwa [he] at h

end NormalNumbers.UniformBadThreshold.NextReview
