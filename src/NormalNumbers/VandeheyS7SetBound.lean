/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SB: the front, in the `y`-frame and at SET level

S7-SO showed the §7 front is a statement about the OUTPUT orbit alone, and S7-MR showed that a
cylinder-level (or interval-level) bound is the wrong currency once a modulus is in play: a
modulus is not subadditive, so covering arguments cannot upgrade it, and the CF Bernoulli measure
on digits `{1,2}` is a singular measure satisfying a cylinder-level bound.  Lap 80's next action
#1 is therefore to restate the front for **arbitrary measurable targets**.  That is this module.

    OrbitSetBound q r₀ C  :=  ∀ CF-normal x, ∀ measurable E ⊆ (0,1),
        limsup_p  #{ i < p : Gⁱ(fract (q x + r₀)) ∈ E } / p  ≤  C · γ E .

Three facts pin its place in the chain:

* `orbitWordBound_of_orbitSetBound` — it implies the crux `OrbitWordBound` outright (take
  `E = I_w`), so nothing is lost by moving to the set level.
* `orbitACBound_of_orbitSetBound` — it implies the interval form `OrbitACBound` with constant
  `C / log 2`, via the Gauss/Lebesgue density window, so the cited `GaussACRigidity` still
  applies.  Set level is genuinely the STRONGER statement, and the hypothesis chain is unchanged.
* `freq_le_of_gaussMeasure_zero` — and here is what the set level buys that the cylinder level
  cannot: on a `γ`-null target the visit frequency is eventually below every `ε`.  This is the
  absolute-continuity step, and at set level it is FREE (the bound is linear in `γ E`, so no
  covering and no subadditivity of a modulus is needed).  S7-MR's counterexample is exactly the
  statement that this line has no cylinder-level analogue.

So the AC step is not a further hypothesis; it is a corollary of stating the front at set level.
What remains open is `OrbitSetBound` itself — which, by S7-SK, is a Birkhoff-average statement
for the fixed observables of the skew product `pairStep`.

## Guard rule

Content locator: `orbitACBound_of_orbitSetBound` passes through
`gaussMeasure_Ioo_toReal_le` (the Gauss density is at most `1/log 2`); if the density window were
the other way round the constant would be `2 log 2 · C` instead and the statement would be weaker.
Degenerate case: `E = ∅` makes both sides of `freq_le_of_gaussMeasure_zero` zero, and `E = (0,1)`
makes `OrbitSetBound` say `1 ≤ C`, so `C ≥ 1` is forced — the bound is never vacuous.
-/
import NormalNumbers.VandeheyS7Orbit
import NormalNumbers.VandeheyS7Reduce
import NormalNumbers.VandeheyS7Cell

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The front, at set level.**  The image orbit's visit frequency to *every* measurable subset
of `(0,1)` is eventually at most `C` times its Gauss measure. -/
def OrbitSetBound (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioo (0:ℝ) 1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop,
      blockCount E p (Int.fract (q * x + r₀)) / p ≤ C * (gaussMeasure E).toReal + ε

/-- Set level implies the word-level crux: cylinders are measurable subsets of `(0,1)`. -/
theorem orbitWordBound_of_orbitSetBound {q r₀ C : ℝ} (h : OrbitSetBound q r₀ C) :
    OrbitWordBound q r₀ C := by
  intro x hx w _ ε hε
  exact h x hx (cfCylinder w) (measurableSet_cfCylinder w) (cfCylinder_subset_Ioo w) ε hε

/-- Set level implies the interval form, with constant `C / log 2`. -/
theorem orbitACBound_of_orbitSetBound {q r₀ C : ℝ} (hC : 0 ≤ C) (h : OrbitSetBound q r₀ C) :
    OrbitACBound q r₀ (C / Real.log 2) := by
  intro x hx a b ha hab hb ε hε
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0:ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
  refine (h x hx (Set.Ioo a b) measurableSet_Ioo hsub ε hε).mono fun p hp => ?_
  refine hp.trans ?_
  have hmass := gaussMeasure_Ioo_toReal_le ha hab hb
  have hmul : C * (gaussMeasure (Set.Ioo a b)).toReal ≤ C * ((b - a) / Real.log 2) :=
    mul_le_mul_of_nonneg_left hmass hC
  have hrw : C * ((b - a) / Real.log 2) = C / Real.log 2 * (b - a) := by
    field_simp
  linarith [hrw ▸ hmul]

/-- **What the set level buys.**  On a `γ`-null target the visit frequency is eventually below
every `ε`: the absolute-continuity step, free of any covering argument. -/
theorem freq_le_of_gaussMeasure_zero {q r₀ C : ℝ} (hC : 0 ≤ C) (h : OrbitSetBound q r₀ C)
    {x : ℝ} (hx : IsCFNormal (Int.fract x)) {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Ioo (0:ℝ) 1) (hnull : gaussMeasure E = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, blockCount E p (Int.fract (q * x + r₀)) / p ≤ ε := by
  refine (h x hx E hE hEsub ε hε).mono fun p hp => ?_
  rwa [hnull, ENNReal.toReal_zero, mul_zero, zero_add] at hp

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.orbitWordBound_of_orbitSetBound
#print axioms NormalNumbers.VandeheyS7.orbitACBound_of_orbitSetBound
#print axioms NormalNumbers.VandeheyS7.freq_le_of_gaussMeasure_zero

end Audit
