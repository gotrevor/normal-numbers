import NormalNumbers.AbelianNormal

/-!
# A binary sequence that is abelian-normal but not normal

Campbell (arXiv:2603.04396) separates abelian normality from normality in base 10 with a cyclic
swap on digit pairs, which needs three digits.  In base 2 the separation first appears at block
length 4 (`rigid_three`, `separation_four`).  This file realizes it by an infinite sequence.

Take a base-16 normal digit sequence `c`, apply `hexSwap` (2 → 3, 5 → 4, B → A, C → D), and read
each hex digit as four bits.  Every contiguous interval inside a block has a Binomial one-count
under the induced block law, so every window's one-count is Binomial (suffix + whole blocks +
prefix, independent in the limit by base-16 normality of `c`).  But `0011` has limiting frequency
`5/64`.  Design note: `DESIGN-2026-09-23-binary-abelian-nonnormal.md`; exact probe:
`probes/abelian_hex_construction.py`.
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

/-- The hex substitution `2 → 3, 5 → 4, B → A, C → D`. -/
def hexSwap (d : ℕ) : ℕ :=
  if d = 2 then 3 else if d = 5 then 4 else if d = 11 then 10 else if d = 12 then 13 else d

/-- Binary reading of the swapped hex digits of `c`: bit `n` is bit `3 - n % 4` (most significant
first) of `hexSwap (c (n / 4))`. -/
def xiBits (c : ℕ → ℕ) (n : ℕ) : ℕ := hexSwap (c (n / 4)) / 2 ^ (3 - n % 4) % 2

/-- The construction is abelian-normal in base two. -/
theorem isAbelianNormalTwo_xiBits (c : ℕ → ℕ) (hc16 : ∀ m, c m < 16)
    (hc : IsNormalSequence 16 c) : IsAbelianNormalTwo (xiBits c) := by
  sorry

/-- The construction is not normal in base two: `0011` has limiting frequency `5/64`. -/
theorem not_isNormalSequence_xiBits (c : ℕ → ℕ) (hc16 : ∀ m, c m < 16)
    (hc : IsNormalSequence 16 c) : ¬ IsNormalSequence 2 (xiBits c) := by
  sorry

/-- **Separation.**  Some binary sequence is abelian-normal but not normal. -/
theorem exists_abelianNormal_not_normal :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ IsAbelianNormalTwo s ∧ ¬ IsNormalSequence 2 s := by
  sorry

end NormalNumbers.Abelian
