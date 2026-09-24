import NormalNumbers.SwingC1Decouple

/-!
# PairDecouple — the PROOF direction

The only open input of `conjC1_of_delange_katai_decouple` (C1 swing).  Exactly the hypothesis
`hDc` there.  A sibling worktree (`wip/pd-refute`) attacks the negation.
-/

namespace NormalNumbers.CastingOut

theorem pairDecouple_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b) := by
  sorry

end NormalNumbers.CastingOut
