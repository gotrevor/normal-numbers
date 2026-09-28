import ErdosProblems.Erdos67b.ElliottComplete

/-!
# Bet: Tao's general two-point log-Elliott theorem (2026-09-24)

The dependency `lean-proofs-latest` (Boris Alexeev's `plby/lean-proofs`, Erdős 67b) proves only the unit-circle,
completely multiplicative, shift specialisation `Erdos67b.unitCircleLogElliott`.  It STATES the
general form, Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
correlations*, Forum Math. Pi 4 (2016), Theorem 1.3, as `Erdos67b.NonasymptoticLogElliott`
(any two affine forms with `a₁b₂ − a₂b₁ ≠ 0`, `1`-bounded multiplicative `g₁, g₂`, non-pretentious
hypothesis on `g₁` only).  This file carries the ratified headline.
See `KICKOFF-2026-09-24-elliott-general.md`.
-/

namespace NormalNumbers.ElliottGeneral

/-- **THE BET (ratified).**  Tao 2016, Theorem 1.3, in plby's finitary formulation. -/
theorem nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott := by
  sorry

end NormalNumbers.ElliottGeneral
