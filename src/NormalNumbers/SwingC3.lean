import NormalNumbers.CastingOut

/-!
# Swing at C3: `G4` is rich (every word at positive lower density)

`ConjC3` (frozen in `CastingOut.lean`).  Intermediate rung: positive UPPER density, `IsRichUpper`.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Every word occurs at a set of positions of positive UPPER density. -/
noncomputable def IsRichUpper (b : ℕ) (x : ℝ) : Prop :=
  open Classical in
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∃ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ)

theorem isRichUpper_of_isRich (b : ℕ) (x : ℝ) (h : IsRich b x) : IsRichUpper b x := by
  sorry

/-- Rung: `G4_b` is upper-rich. -/
theorem isRichUpper_primeLambertAtBase (b : ℕ) (hb : 3 ≤ b) :
    IsRichUpper b (primeLambertAtBase b) := by
  sorry

theorem conjC3 : ConjC3 := by
  sorry

end NormalNumbers.CastingOut
