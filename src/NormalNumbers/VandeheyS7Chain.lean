/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-E: the §7 chain end to end, on its two remaining obligations

Laps 43–45 removed the threshold parameter from the crux and minimised the second hypothesis.
This module assembles the result into the two frozen §7 targets, so the audit surface shows
exactly what Vandehey §7 Problem 1 now rests on:

    vandeheyS7_mul_phi  ⇐  GaussACRigidity (C / log 2)     -- cited, standing rule 3
                        +  OrbitWordBound φ 0 C            -- THE CRUX (fact (γ))
                        +  ImageTight on the image         -- the second obligation

and likewise `vandeheyS7_add_phi` with `OrbitWordBound 1 φ C`.  Leg 1
(`AffineImageIrrational`) is discharged for both instances (`VandeheyS7Golden`, lap 30), the
threshold is free (`orbitCellBound_of_orbitWordBound`, lap 43), and tightness is exactly the part
of a Lévy bound that CF-normality supplies (`imageTight_of_isCFNormal`, lap 45) — the latter for
the INPUT, which is why the image's tightness remains a named hypothesis here rather than a
theorem.

Compare the state at lap 30: three hypotheses, one of them carrying a threshold parameter `T`
and a Lévy constant `Λ`.  Both parameters are now gone.
-/
import NormalNumbers.VandeheyS7Tight2
import NormalNumbers.VandeheyS7Golden

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-- **`x ↦ φ·x`, on two obligations.** -/
theorem vandeheyS7_mul_phi_of_orbitWordBound {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (Real.goldenRatio * x + 0)))
    (hword : OrbitWordBound Real.goldenRatio 0 C) : vandeheyS7_mul_phi :=
  vandeheyS7_mul_phi_of_orbitCellBound hC hrig
    (orbitCellBound_of_orbitWordBound hC affineImageIrrational_goldenRatio htight hword)

/-- **`x ↦ x + φ`, likewise.** -/
theorem vandeheyS7_add_phi_of_orbitWordBound {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (1 * x + Real.goldenRatio)))
    (hword : OrbitWordBound 1 Real.goldenRatio C) : vandeheyS7_add_phi :=
  vandeheyS7_add_phi_of_orbitCellBound hC hrig
    (orbitCellBound_of_orbitWordBound hC affineImageIrrational_add_goldenRatio htight hword)

/-- **The second obligation, discharged whenever the image is already known normal.**  This is
not circular reasoning in the chain — it is the statement that `ImageTight` is *strictly* weaker
than the conclusion, so it is a legitimate intermediate target rather than a restatement. -/
theorem imageTight_of_image_isCFNormal {q r₀ : ℝ} (hirr : AffineImageIrrational q r₀)
    {x : ℝ} (hx : IsCFNormal (Int.fract x)) (h : IsCFNormal (Int.fract (q * x + r₀))) :
    ImageTight (Int.fract (q * x + r₀)) := by
  obtain ⟨hyirr, hymem⟩ := irrational_fract_mem (hirr x hx)
  exact imageTight_of_isCFNormal hyirr hymem h

section Audit

#print axioms vandeheyS7_mul_phi_of_orbitWordBound
#print axioms vandeheyS7_add_phi_of_orbitWordBound

end Audit

end NormalNumbers.VandeheyS7
