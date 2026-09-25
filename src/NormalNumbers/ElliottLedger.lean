import NormalNumbers.ElliottSliceCapModerate
import NormalNumbers.ElliottPrimeDensityAP
import NormalNumbers.ElliottZetaTheta

/-!
# THE LEDGER: `TwoPointElliottLog` from ONE cited classical axiom

This file states the endpoint DIRECTION set for the campaign.  Every input of
`ElliottTwoPointLog.TwoPointElliottLog` is now a machine-checked theorem **except one**:

| input | status |
| --- | --- |
| `ElliottCharRigidity.CharacterClusterRigidity` | proved (lap 91) from `PrimeDensityAP` |
| `ElliottCharRigidity.PrimeDensityAP A` | **PROVED** (lap 118, `ElliottPrimeDensityAP.exists_primeDensityAP`) |
| `ElliottArchBands.ShiftedMertensSmall K₀` | **PROVED** (lap 112, `ElliottSliceCap.exists_shiftedMertensSmall`) |
| `ElliottArchBands.ArchCorrModerate9 K₁` | **PROVED** (lap 117, `ElliottSliceCapModerate.exists_archCorrModerate9`) |
| `ElliottArchBands.ArchCorrNearMaxHeight A (1−(1−ν)/9) η₂ K₂` | 🟠 **CITED — Vinogradov–Korobov** |

**The remaining axiom is real, not an artefact.**  At near-maximal height `|v| ≍ X` the trivial
bound `|ζ(1+it)| ≪ log t` gives `log log|v| ≍ log log X` — exactly no proportional saving — and
beating it needs `|ζ(1+it)| ≪ (log t)^{2/3}`, i.e. Vinogradov's mean value theorem.  See
`ElliottArchBands` §"negative results" for the sub-routes refuted while establishing this.

**What this does NOT close.**  `TwoPointElliottLog` is the **logarithmic** average.
`CastingOut.TwoPointElliott` — what the repo's normality route actually consumes — is the
**natural** average, and the passage between them is a separate, known-open, Chowla-strength
problem.  Nothing in `src/` currently consumes `TwoPointElliottLog`.
-/

namespace NormalNumbers.ElliottLedger

open NormalNumbers.ElliottArchBands

noncomputable section

/-- **THE LEDGER IS ONE.**  `TwoPointElliottLog b p q t` follows from the single cited classical
input `ArchCorrNearMaxHeight` (Vinogradov–Korobov, near-maximal height only).  Every other
hypothesis of `twoPointElliottLog_of_three_bands` has been discharged into a theorem. -/
theorem twoPointElliottLog_of_nearMaxHeight {b p q : ℕ} {t : ℝ} {K₂ ν η₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂) (hη₂1 : η₂ ≤ 1)
    (hmax : ∀ A : ℕ, ArchCorrNearMaxHeight A (1 - (1 - ν) / 9) η₂ K₂) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t :=
  NormalNumbers.ElliottSliceCapModerate.twoPointElliottLog_of_density_and_nearMax
    hp hq hpq hu hν hν1 hη₂ hη₂1
    (fun A => NormalNumbers.ElliottPrimeDensityAP.exists_primeDensityAP A) hmax

/-- **THE CAMPAIGN, IN ONE STATEMENT.**  `TwoPointElliottLog b p q t` follows from a single
standard analytic fact about the Riemann zeta function:

> `ZetaLogDerivExponent θ` for some `θ < 1` — i.e. `‖ζ'/ζ(s)‖ ≪ (log(|Im s|+16))^θ` on
> `1 ≤ Re s ≤ 3`, `|Im s| ≥ 1`.

Nothing else is assumed.  `PrimeDensityAP`, `CharacterClusterRigidity`, `ShiftedMertensSmall`,
`ArchCorrModerate` and `ArchCorrNearMaxHeight` are all discharged inside this call.

**Where the repo stands against that threshold.**  `zetaLogDerivExponent_nine` proves the case
`θ = 9`, from `PNTPort.ZetaZeroFree9` — *proved, in this repo, no axioms*.  Vinogradov–Korobov is
the case `θ = 2/3`.  So the entire remaining debt of this campaign is the single quantitative gap

> `9`  ⟶  `< 1`

in the zero-free-region exponent, a statement a reader can check against the literature at a glance
and which any future strengthening of `src/PNTPort/ZetaBounds.lean` discharges automatically.  That
is a strictly better place to stand than a bespoke `Prop` about `archCorr`.

**Still true, and still to be said.**  `TwoPointElliottLog` is the **logarithmic** average;
`CastingOut.TwoPointElliott`, which the repo's normality route consumes, is the **natural**
average, and the passage is a separate known-open Chowla-strength problem.  This does not close
the normality route. -/
theorem twoPointElliottLog_of_zetaExponent {b p q : ℕ} {t : ℝ} {θ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : NormalNumbers.ElliottZetaTheta.ZetaLogDerivExponent θ) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t := by
  obtain ⟨K, hK⟩ := NormalNumbers.ElliottZetaTheta.archCorrNearMaxHeight_of_exponent hθ0 h
  refine twoPointElliottLog_of_nearMaxHeight (ν := 1/2) (η₂ := 1 - θ) (K₂ := K)
    hp hq hpq hu (by norm_num) (by norm_num) (by linarith) (by linarith) ?_
  intro A
  exact hK A (1 - (1 - 1/2) / 9) (by norm_num)

end

end NormalNumbers.ElliottLedger
