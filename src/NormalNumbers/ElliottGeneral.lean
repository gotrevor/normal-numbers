import NormalNumbers.ElliottDilatedSlice

/-!
# Bet: Tao's general two-point log-Elliott theorem (2026-09-24)

The dependency `lean-proofs-latest` (Boris Alexeev's `plby/lean-proofs`, Erdős 67b) proves only the unit-circle,
completely multiplicative, shift specialisation `Erdos67b.unitCircleLogElliott`.  It STATES the
general form, Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
correlations*, Forum Math. Pi 4 (2016), Theorem 1.3, as `Erdos67b.NonasymptoticLogElliott`
(any two affine forms with `a₁b₂ − a₂b₁ ≠ 0`, `1`-bounded multiplicative `g₁, g₂`, non-pretentious
hypothesis on `g₁` only).  This file carries the ratified headline.
See `KICKOFF-2026-09-24-elliott-general.md`.

The headline is now assembled from the ladder in `NormalNumbers.ElliottLadder`:

* `NormalNumbers.ElliottLadder.affineCM_of_dilatedCM` — **proved**: Tao's full affine generality is
  free once the common-dilation case is known, for completely multiplicative unimodular functions.
* `NormalNumbers.ElliottDilatedSlice.dilatedCMLogElliott` — the crux; its analytic content is
  **proved** (`NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott` and its mirror), and its common
  dilation is reduced, by an exact identity, to the multiples-of-`a` slice rung
  `DilatedSliceCMLogElliott`, which is the one remaining analytic obligation on this branch.
* `NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM` — open, the passage from `1`-bounded
  multiplicative to completely multiplicative unimodular.
-/

namespace NormalNumbers.ElliottGeneral

/-- **THE BET (ratified).**  Tao 2016, Theorem 1.3, in plby's finitary formulation. -/
theorem nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott :=
  ElliottLadder.nonasymptotic_of_affineCM
    (ElliottLadder.affineCM_of_dilatedCM ElliottDilatedSlice.dilatedCMLogElliott)

end NormalNumbers.ElliottGeneral
