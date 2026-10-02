/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-TD: the crux reduced to ONE named hypothesis

This completes the directive's move (a).  `VandeheyS7Decomp` built the block decomposition, the
tick-to-every-time interpolation and the residual `BlockAverageBound`; here they are assembled
against the actual definition `VandeheyS7Reduce.OrbitWordBound`, so the §7 front reads

    GaussACRigidity (cited)  +  ImageTight  +  TransducerData  ⟹  both frozen targets.

`TransducerData q r₀ C` bundles, for each CF-normal `x` and each word `w`, exactly what the Raney
transducer is supposed to provide: a clock `N`, the pulled-back block sets `S`, the coupling, the
clock's regularity, and the block average at level `C·γ(I_w)`.  `orbitWordBound_of_transducerData`
turns that into the crux.

**What this buys.**  The three pieces of `TransducerData` are of completely different difficulty,
and naming them separately is the point:
* `BlockCoupling` — bookkeeping about the Raney machine, no mathematics;
* clock regularity `N(n+1)/N n → 1` — by S7-RD/S7-LAG equivalent to a Cesàro bound on `log aₙ`,
  which CF-normality does **not** supply, so it is a real but *finite* debt;
* `BlockAverageBound` — directive fact (α), and by S7-ST/S7-DC the same statement as
  equidistribution in the second archimedean place of `ℚ(φ)`.  This is the wall, and it is now the
  ONLY wall on the front.

So nothing else on the §7 route is open.  Everything that is not (α) is either proved or reduced to
these two named, finite obligations.

Guard rules.  Degenerate: `w = []` forces `γ(I_w) = 1` and the bound is vacuous; a clock with a
silent input step is excluded by `BlockCoupling.strictMono`, deliberately — see the S7-BD docstring.
Content locator: with `N = id` the hypothesis `BlockAverageBound` *is* the lap-30 one-step statement,
so this theorem adds no mathematics and is not meant to.
-/
import NormalNumbers.VandeheyS7Decouple
import NormalNumbers.VandeheyS7Chain

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **What the Raney transducer must supply.**  For every CF-normal `x` and every admissible word
`w`: a clock, the pulled-back block sets, the coupling, clock regularity, and the block average at
level `C·γ(I_w)`. -/
def TransducerData (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    ∃ (N : ℕ → ℕ) (S : ℕ → ℕ → Set ℝ),
      BlockCoupling (cfCylinder w) (Int.fract x) (Int.fract (q * x + r₀)) N S ∧
      Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1) ∧
      BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x) N S

/-- **S7-TD.**  The transducer data gives the crux. -/
theorem orbitWordBound_of_transducerData {q r₀ C : ℝ} (hC : 0 ≤ C)
    (h : TransducerData q r₀ C) : OrbitWordBound q r₀ C := by
  intro x hx w hw ε hε
  obtain ⟨N, S, hcouple, hratio, hBA⟩ := h x hx w hw
  have hB : 0 ≤ C * (gaussMeasure (cfCylinder w)).toReal :=
    mul_nonneg hC ENNReal.toReal_nonneg
  exact freq_le_of_blockAverage hcouple hratio hB hBA ε hε

/-! ## The front, end to end -/

/-- **`x ↦ φ·x`, from the three named hypotheses.**  `GaussACRigidity` is cited (standing rule 3),
`ImageTight` is the counting-side obligation, and `TransducerData` carries the crux. -/
theorem vandeheyS7_mul_phi_of_transducerData {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (Real.goldenRatio * x + 0)))
    (hTD : TransducerData Real.goldenRatio 0 C) : vandeheyS7_mul_phi :=
  vandeheyS7_mul_phi_of_orbitWordBound hC hrig htight
    (orbitWordBound_of_transducerData hC hTD)

/-- **`x ↦ x + φ`, likewise.** -/
theorem vandeheyS7_add_phi_of_transducerData {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (1 * x + Real.goldenRatio)))
    (hTD : TransducerData 1 Real.goldenRatio C) : vandeheyS7_add_phi :=
  vandeheyS7_add_phi_of_orbitWordBound hC hrig htight
    (orbitWordBound_of_transducerData hC hTD)

section Audit

#print axioms orbitWordBound_of_transducerData
#print axioms vandeheyS7_mul_phi_of_transducerData
#print axioms vandeheyS7_add_phi_of_transducerData

end Audit

end NormalNumbers.VandeheyS7
