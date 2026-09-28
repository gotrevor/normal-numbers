import NormalNumbers.ElliottLeafTwo

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
* `NormalNumbers.ElliottDilatedRung.dilatedCMLogElliott` — the crux, on the **live** route: the
  `a`-dilated prime graph, every rung of which is a proved axiom-clean statement in `src/`.  Its
  arbitrary integer shifts are reduced, at cost `3k` for a constant `k`, to the natural-shift
  shape the graph stack produces (`dilatedCM_of_natShift`, proved), leaving the two analytic
  leaves `dilatedNatShiftCMLogElliott` and its mirror.  The earlier *dilation-slice* route
  (`NormalNumbers.ElliottDilatedSlice`) is refuted; its free reductions stay proved there, but the
  headline no longer depends on it.
* `NormalNumbers.ElliottLeafTwo.nonasymptotic_of_affineCM` — the passage from `1`-bounded
  multiplicative to completely multiplicative unimodular.  The assembly itself is **proved** (a
  dichotomy on the Euler defect of `g₁` at the thin scale); it rests on two disclosed halves,
  `exists_caseA_thin_threshold` and `exists_caseB_threshold`, plus the uniform squarefull tail
  `exists_squarefull_tail`.
-/

namespace NormalNumbers.ElliottGeneral

/-- **THE BET (ratified), in its honest form.**  Tao 2016, Theorem 1.3, in plby's finitary
formulation, for merely (i.e. coprime-)multiplicative `g₁, g₂` — what the paper actually claims.
The dependency's `Erdos67b.IsMultiplicativeOnPositiveInt` has no coprimality hypothesis, so it is
*complete* multiplicativity; this statement closes that fidelity gap. -/
theorem nonasymptoticLogElliottMult :
    ElliottMultStatement.NonasymptoticLogElliottMult :=
  ElliottLeafTwo.nonasymptotic_mult_of_affineCM
    (ElliottLadder.affineCM_of_dilatedCM ElliottDilatedRung.dilatedCMLogElliott)

/-- **THE BET (ratified).**  Tao 2016, Theorem 1.3, in plby's finitary formulation. -/
theorem nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott :=
  nonasymptoticLogElliottMult.toCompletelyMultiplicative

end NormalNumbers.ElliottGeneral
