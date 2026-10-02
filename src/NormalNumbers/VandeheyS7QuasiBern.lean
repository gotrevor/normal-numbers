/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7WindowHit
import NormalNumbers.CFGammaMixing

/-!
# S7-QB: quasi-Bernoulli for ARBITRARY targets, and the interval form the crux needs

Lap 50's `gaussMeasure_append_le` is the quasi-Bernoulli bound for *cylinder* targets, proved
from `volume_cylinder_append_le`.  The crux's targets are not cylinders: at a window `v` the
approximate-window route produces the interval `F(v)⁻¹(I_w)`.  This module upgrades the bound to
an arbitrary measurable target, using the repo's correlation-decay theorem
(`gaussMeasure_cylinder_mixing`) at gap `g = 0`:

    γ(I_v ∩ T^{−|v|}A)  ≤  (1 + 8 log 2) · γ(I_v) · γ(A)      (`gaussMeasure_inter_preimage_le`)

and specialises it to intervals (`gaussMeasure_inter_preimage_Ioo_le`), where the Gauss mass is
replaced by the length:

    γ(I_v ∩ T^{−|v|}(a,b))  ≤  ((1 + 8 log 2)/log 2) · (b − a) · γ(I_v) .

That is exactly the per-window mass input of the window-hit theorem, for the interval targets the
transducer produces, with an absolute constant and no cover argument.

## Guard rule

Content locator: at `A = cfCylinder u` this recovers lap 50's append bound up to the constant, so
the new content is the arbitrariness of `A`.  Degenerate case: `A = Set.Ioo 0 1` makes both sides
`γ(I_v)` up to the constant, so the inequality is not vacuous.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

open scoped ENNReal

/-- **Quasi-Bernoulli, arbitrary target.**  Conditioned on a cylinder, the future is comparable
to the unconditioned Gauss measure, with an absolute constant. -/
theorem gaussMeasure_inter_preimage_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0:ℝ) 1) :
    (gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' A)).toReal ≤
      (1 + 8 * Real.log 2) * ((gaussMeasure (cfCylinder v)).toReal *
        (gaussMeasure A).toReal) := by
  have hmix := gaussMeasure_cylinder_mixing v hpos 0 hA hA1
  simp only [pow_zero, one_mul, Nat.add_zero] at hmix
  have habs := (abs_le.1 hmix).2
  have hvolA : (volume A).toReal ≤ 2 * Real.log 2 * (gaussMeasure A).toReal := by
    refine volume_toReal_le A hA hA1 ?_
    refine ne_top_of_le_ne_top ?_ (measure_mono hA1)
    rw [Real.volume_Ioo]; simp
  have hg0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hA0 : (0:ℝ) ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_right hvolA hg0]

/-- The interval form: the conditional mass of an interval is at most a constant times its
length. -/
theorem gaussMeasure_inter_preimage_Ioo_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (Set.Ioo a b))).toReal ≤
      (1 + 8 * Real.log 2) / Real.log 2 * ((b - a) *
        (gaussMeasure (cfCylinder v)).toReal) := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0:ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
  have h := gaussMeasure_inter_preimage_le v hpos measurableSet_Ioo hsub
  have hIoo : (gaussMeasure (Set.Ioo a b)).toReal ≤ (b - a) / Real.log 2 := by
    have := gaussMeasure_Ioo_toReal_le ha hab hb
    simpa [div_eq_inv_mul, mul_comm] using this
  have hg0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hc : (0:ℝ) ≤ 1 + 8 * Real.log 2 := by positivity
  have hstep : (1 + 8 * Real.log 2) * ((gaussMeasure (cfCylinder v)).toReal *
      (gaussMeasure (Set.Ioo a b)).toReal)
      ≤ (1 + 8 * Real.log 2) * ((gaussMeasure (cfCylinder v)).toReal * ((b - a) / Real.log 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIoo hg0) hc
  refine h.trans (hstep.trans (le_of_eq ?_))
  field_simp
  try ring

section Audit

#print axioms gaussMeasure_inter_preimage_le
#print axioms gaussMeasure_inter_preimage_Ioo_le

end Audit

end NormalNumbers.VandeheyS7
