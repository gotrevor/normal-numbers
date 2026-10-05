/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterConjectures
import NormalNumbers.WallRational

/-!
# A normal number in the ℚ-span of `√2, √3`?

The question (Trevor, 2026-10-05): *either `√2`, or `√3`, or `c₁√2 + c₂√3` for some rationals
`c₁, c₂` is normal.*  Since `c₂ = 0` and `c₁ = 0` are allowed, the disjunction is just
`QSpanNormal b √2 √3` (`sqrt_disjunction_iff`).  By Wall (`isNormal_rat_mul_add`) it is a
one-parameter question: `√3`, or `√2 + c√3` for one rational `c` (`qSpanNormal_iff_line`).

**How hard.**  Every nonzero element of the span is an algebraic irrational, so a proof would
exhibit the first algebraic irrational known to be normal (the Borel conjecture
`MasterConjectures.BorelConjecture` gives it at once, `qSpanNormal_of_borel`).  And unlike the
six-fold adder disjunction (`Adder.adder_sixfold_disjunction_universal`, true for every pair not
both rational), no pair-universal mechanism exists: a pair of sparse Liouville-type numbers,
ℚ-independent with `1`, has no normal number in its span (`exists_pair_qSpan_not_normal`,
frozen).  So a mechanism must use something `√2, √3` have and that pair lacks, such as
algebraicity.

The quantifier swap is where the difficulty sits: `∀ w, ∃ m, w occurs infinitely often in m·α`
holds for every irrational (Mahler 1973, Berend–Boshernitzan 1994, `MahlerMultiplier.lean`);
`∃ c, ∀ w` is the open statement.
-/

namespace NormalNumbers.QSpan

open MasterConjectures

/-- Some nonzero rational combination `c₁x + c₂y` is normal in base `b`. -/
def QSpanNormal (b : ℕ) (x y : ℝ) : Prop :=
  ∃ c₁ c₂ : ℚ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ IsNormal b ((c₁ : ℝ) * x + c₂ * y)

/-- Trevor's disjunction is exactly `QSpanNormal`. -/
theorem sqrt_disjunction_iff (b : ℕ) :
    (IsNormal b (Real.sqrt 2) ∨ IsNormal b (Real.sqrt 3) ∨ QSpanNormal b (Real.sqrt 2) (Real.sqrt 3))
      ↔ QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) := by
  constructor
  · rintro (h | h | h)
    · exact ⟨1, 0, Or.inl one_ne_zero, by simpa using h⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- **Wall reduction.**  The span question is the line `x + c·y` plus the point `y`. -/
theorem qSpanNormal_iff_line (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) :
    QSpanNormal b x y ↔ IsNormal b y ∨ ∃ c : ℚ, IsNormal b (x + c * y) := by
  constructor
  · rintro ⟨c₁, c₂, hne, h⟩
    by_cases h1 : c₁ = 0
    · left
      have h2 : c₂ ≠ 0 := hne.resolve_left (not_not.2 h1)
      subst h1
      have := isNormal_rat_mul_add b hb _ (c₂⁻¹) 0 (inv_ne_zero h2) h
      convert this using 1
      push_cast
      field_simp
      ring
    · right
      refine ⟨c₂ / c₁, ?_⟩
      have := isNormal_rat_mul_add b hb _ (c₁⁻¹) 0 (inv_ne_zero h1) h
      convert this using 1
      push_cast
      field_simp
      ring
  · rintro (h | ⟨c, h⟩)
    · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
    · exact ⟨1, c, Or.inl one_ne_zero, by simpa using h⟩

/-- The Borel conjecture settles it (via `√2` alone). -/
theorem qSpanNormal_of_borel (hB : BorelConjecture) (b : ℕ) (hb : 2 ≤ b) :
    QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) :=
  ⟨1, 0, Or.inl one_ne_zero, by simpa using hB _ irrational_sqrt_two isAlgebraic_sqrt_two b hb⟩

/-- **Open node: a normal number on the line `√2 + c√3`, or `√3`.**  Believed (~99%, it follows
from Borel); no mechanism (0% for a proof here).  Crux-linked to
`exists_pair_qSpan_not_normal`: a proof must use something the Liouville pair lacks. -/
theorem qSpanNormal_sqrt_two_sqrt_three (b : ℕ) (hb : 2 ≤ b) :
    QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) := by
  sorry

/-- **Sibling: a ℚ-independent pair whose ℚ-span holds no normal number.**  Confidence 90%.

English construction.  `x = Σ_k b^{−n_k}`, `y = Σ_k b^{−m_k}` with `n_k = (2k)!`,
`m_k = (2k+1)!`; disjoint supersparse supports make `1, x, y` ℚ-independent.  For
`z = (a x + a' y)/q` with integers `a, a'` and `q ≥ 1`, between consecutive support points
`N < N'` the digits of `z` from about `N + O(log q)` to `N'` are those of a rational with
denominator `q`: periodic with period at most `q`.  As `N'/N → ∞`, at time `N'` almost all of
the prefix is periodic, so a length-`n` block with `bⁿ > q` and none of the `≤ q` periodic
blocks has frequency tending to `0` along `N'`.  So `z` is not normal. -/
theorem exists_pair_qSpan_not_normal (b : ℕ) (hb : 2 ≤ b) :
    ∃ x y : ℝ, (∀ c₀ c₁ c₂ : ℚ, (c₁ : ℝ) * x + c₂ * y = c₀ → c₁ = 0 ∧ c₂ = 0) ∧
      ¬ QSpanNormal b x y := by
  sorry

end NormalNumbers.QSpan
