import NormalNumbers.SwingC1Decouple

/-!
# PairDecouple — the REFUTATION direction

The negation of the C1 swing's only open input (`hDc` in `conjC1_of_delange_katai_decouple`).
A sibling worktree (`wip/pd-prove`) attacks the positive statement.
-/

namespace NormalNumbers.CastingOut

theorem not_pairDecouple_all : ∃ b : ℕ, 3 ≤ b ∧ ∃ m : ℤ, m ≠ 0 ∧ ¬ ((b : ℤ) ∣ m) ∧
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ ¬ PairDecouple b p q (((m : ℤ) : ℝ) / b) := by
  sorry

end NormalNumbers.CastingOut
