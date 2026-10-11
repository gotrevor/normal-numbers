/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Finite accounting controls for gate-5 measurement

This finite model records why restricting tail bases alone does not order
parent-conditioned losses.  It is not a counterexample to the frozen tail
budget or a claim that these toy sets occur in the actual weighted core.
-/
namespace NormalNumbers.UniformBadThreshold.TailProbeReview

/-- Two unit-weight children per surviving parent; charge missing children. -/
def finiteLoss (parents children : Finset ℕ) : ℕ :=
  ∑ p ∈ parents, ∑ j ∈ Finset.range 2,
    if 2 * p + j ∈ children then 0 else 1

/-- Removing additional parents can reduce loss even when children also shrink. -/
theorem additional_deletion_can_reduce_loss :
    (∅ : Finset ℕ) ⊆ {0} ∧ (∅ : Finset ℕ) ⊆ {1} ∧
    finiteLoss ∅ ∅ < finiteLoss {0} {1} := by
  norm_num [finiteLoss, Finset.sum_range_succ]

/-- With the parent retained, removing additional children can increase loss. -/
theorem additional_deletion_can_increase_loss :
    (∅ : Finset ℕ) ⊆ {1} ∧
    finiteLoss {0} {1} < finiteLoss {0} ∅ := by
  norm_num [finiteLoss, Finset.sum_range_succ]

end NormalNumbers.UniformBadThreshold.TailProbeReview
