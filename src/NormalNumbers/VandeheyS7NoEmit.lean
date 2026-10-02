/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-NE: `MobState` is NOT closed under emission — the sign convention is the obstruction

Trying to instantiate S7-PN's `StatePin` runs into a wall one line deep.  The emission step asks,
given the post-read state `t` whose image lies inside the cylinder `I_a`, for a state `u` with

    readState a ∘ u = t          (as matrices; `cylState [a] = readState a`)

and the arithmetic of that equation is forced:  `comp` with `readState a = [[0,1],[1,a]]` gives
`u.c = t.a`, `u.d = t.b`, and `u.a = t.c − a·t.a`.  So **`u.a ≥ 0` is the requirement
`a·t.a ≤ t.c`**, which the cylinder condition does not supply.

`emitWitness = [[1,1],[0,2]]`, i.e. `t ↦ (t+1)/2`, is a `MobState` whose image of `(0,1)` is
exactly `(1/2, 1) = I₁` — strictly inside the open cylinder, so this is not a boundary artefact —
and `t.c = 0 < 1 = 1·t.a`.  Hence `not_exists_emit` : no `MobState` emits its digit.

## What is actually going on

A `MobState` has a nondecreasing numerator *and* a nondecreasing denominator.  The maps of `(0,1)`
into `(0,1)` it can express are therefore a proper subclass, and it is **not** the class of
orientation-reversing maps that is missing (`[[0,1],[1,1]] : t ↦ 1/(t+1)` reverses and is a
`MobState`): what is missing is exactly `t.a < 0`, the maps whose numerator decreases.  The
emission `u : t ↦ (1−t)/(1+t)` for the witness above is such a map — reduced, real, and outside the
type.

So `StatePin.reduced` (a `MapsTo` condition) is satisfiable, but the *type* of the state family is
too narrow for the recursion that S7-PN pins.  Any instantiation lap must first widen `MobState`
to allow a negative `a` with the positivity of `mob` on `[0,1]` carried as a field — the
width/distortion/pullback machinery of S7-PB only ever uses monotonicity of `mob` on `[0,1]` and
positivity of the denominator, both of which survive that widening.

The positive half is `exists_emit_of_le` : when `a·t.a ≤ t.c` and `a·t.b ≤ t.d` the emission does
exist, with the explicit witness `[[t.c − a·t.a, t.d − a·t.b],[t.a, t.b]]`.  That is the transducer
step, available whenever the sign condition holds.
-/
import NormalNumbers.VandeheyS7Pin

namespace NormalNumbers.VandeheyS7

namespace MobState

/-! ## The emission step, when the signs allow it -/

/-- **The emission step.**  Given the sign conditions, `t` factors through reading the digit `a`. -/
theorem exists_emit_of_le (t : MobState) {a : ℝ} (ha : 0 < a) (hb : 0 < t.b)
    (h1 : a * t.a ≤ t.c) (h2 : a * t.b ≤ t.d) :
    ∃ u : MobState, (readState a ha).comp u = t := by
  refine ⟨⟨t.c - a * t.a, t.d - a * t.b, t.a, t.b, by linarith, by linarith, t.ha, hb, ?_⟩, ?_⟩
  · show (t.c - a * t.a) * t.b - (t.d - a * t.b) * t.a ≠ 0
    have : (t.c - a * t.a) * t.b - (t.d - a * t.b) * t.a = -(t.a * t.d - t.b * t.c) := by ring
    rw [this]
    intro h
    exact t.hdet (by linarith)
  · refine ext_entries ?_ ?_ ?_ ?_
    · show (0:ℝ) * (t.c - a * t.a) + 1 * t.a = t.a; ring
    · show (0:ℝ) * (t.d - a * t.b) + 1 * t.b = t.b; ring
    · show (1:ℝ) * (t.c - a * t.a) + a * t.a = t.c; ring
    · show (1:ℝ) * (t.d - a * t.b) + a * t.b = t.d; ring

/-! ## The obstruction -/

/-- `t ↦ (t+1)/2`: a `MobState` whose image of `(0,1)` is exactly the cylinder `I₁ = (1/2,1)`. -/
noncomputable def emitWitness : MobState :=
  ⟨1, 1, 0, 2, zero_le_one, zero_le_one, le_refl 0, two_pos, by norm_num⟩

@[simp] lemma emitWitness_mob (z : ℝ) : emitWitness.mob z = (z + 1) / 2 := by
  show ((1:ℝ) * z + 1) / (0 * z + 2) = (z + 1) / 2
  ring_nf

/-- The witness lands strictly inside the open cylinder `I₁`, so the emission hypothesis holds. -/
theorem emitWitness_mapsTo :
    Set.MapsTo emitWitness.mob (Set.Ioo (0:ℝ) 1) (Set.Ioo (1/2 : ℝ) 1) := by
  intro z hz
  rw [emitWitness_mob]
  constructor <;> [linarith [hz.1]; linarith [hz.2]]

/-- **S7-NE.**  No `MobState` emits the digit `1` from `emitWitness`: the forced entry
`u.a = t.c − 1·t.a = −1` is negative, and `MobState` demands `0 ≤ a`. -/
theorem not_exists_emit :
    ¬ ∃ u : MobState, (readState 1 one_pos).comp u = emitWitness := by
  rintro ⟨u, hu⟩
  have hc : u.c = 1 := by
    have := congrArg MobState.a hu
    simpa [comp, readState, emitWitness] using this
  have hac : u.a + u.c = 0 := by
    have := congrArg MobState.c hu
    simpa [comp, readState, emitWitness] using this
  have : u.a = -1 := by linarith
  have := u.ha
  linarith

/-- The emission that `MobState` cannot hold: `u : t ↦ (1−t)/(1+t)`, a genuine reduced map of
`(0,1)` onto `(0,1)`.  It is the *numerator* that decreases, not the map's orientation — a
`MobState` may reverse orientation (`readState`) but never have `a < 0`. -/
theorem emitWitness_factors (z : ℝ) (hz : z ∈ Set.Ioo (0:ℝ) 1) :
    emitWitness.mob z = 1 / ((1 - z) / (1 + z) + 1) ∧ (1 - z) / (1 + z) ∈ Set.Ioo (0:ℝ) 1 := by
  have h1 : (0:ℝ) < 1 + z := by linarith [hz.1]
  constructor
  · rw [emitWitness_mob]
    rw [div_add' _ _ _ h1.ne']
    rw [one_div_div]
    ring_nf
  · constructor
    · exact div_pos (by linarith [hz.2]) h1
    · rw [div_lt_one h1]; linarith [hz.1]

end MobState

section Audit

#print axioms MobState.exists_emit_of_le
#print axioms MobState.not_exists_emit
#print axioms MobState.emitWitness_factors

end Audit

end NormalNumbers.VandeheyS7
