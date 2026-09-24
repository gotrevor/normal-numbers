import NormalNumbers.CastingOut

/-!
# Swing at C1 (natural density)

`ConjC1` (frozen in `CastingOut.lean`): for `b ≥ 3` and every `L`, the length-`L` window digit
sums of `G4_b` mod `b − 1` follow `normalCastLaw`.  Expected to be Elliott-hard.  The swing
succeeds if it isolates the EXACT arithmetic input as a named hypothesis `H` and proves
`conjC1_of_H : H → ConjC1`, or if it refutes a candidate `H`.
-/

namespace NormalNumbers.CastingOut

theorem conjC1 : ConjC1 := by
  sorry

end NormalNumbers.CastingOut
