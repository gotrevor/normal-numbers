/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RC: the read as a composition, so the lag chains along the orbit

S7-RD priced a read of the input digit `a` two-sidedly, but stated it through `readWidth s a =
|s.mob (1/a) − s.mob (1/(a+1))|` — a formula, not a state.  `deficit_telescope_le` needs the price
as a statement about the *next state*, so that the estimate can be chained.  This module supplies
the missing link.

`readState a` is the digit map `t ↦ 1/(a + t)` as a `MobState` (`a,b,c,d = 0,1,1,a`, determinant
`−1`), and `width_comp_readState` says

    (s.comp (readState a)).width = s.readWidth a,

so S7-RD's two-sided bound and `deficit_read_le` transfer verbatim to `s.comp (readState a)`:
`deficit_comp_readState_le`.  With `MobState.comp` already a cocycle (`VandeheyS7Cocycle`), the lag
estimate is now chainable along the actual input orbit, which is what
`deficit_telescope_le`'s `hstep` hypothesis asks for.

Note the orientation: `readState a` reverses the interval (`mob 0 = 1/a > 1/(a+1) = mob 1`), which
is why `width` — defined as an absolute value — is the right invariant to state this in, and why
`readWidth` was defined with the endpoints in that order.

Degenerate case: `a` must be positive for `readState` to be a state at all (`hd : 0 < d`), matching
`1 ≤ a` in every S7-RD statement.
-/
import NormalNumbers.VandeheyS7Audit
import NormalNumbers.VandeheyS7Cocycle

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- The input-digit map `t ↦ 1/(a + t)`, as a state. -/
noncomputable def readState (a : ℝ) (ha : 0 < a) : MobState where
  a := 0
  b := 1
  c := 1
  d := a
  ha := le_refl 0
  hb := zero_le_one
  hc := zero_le_one
  hd := ha
  hdet := by
    show (0:ℝ) * a - 1 * 1 ≠ 0
    norm_num

@[simp] lemma readState_mob (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (readState a ha).mob t = 1 / (t + a) := by
  show ((0:ℝ) * t + 1) / (1 * t + a) = 1 / (t + a)
  ring_nf

/-- **The link.**  Composing with the digit map produces exactly the post-read width. -/
theorem width_comp_readState (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readState a (lt_of_lt_of_le zero_lt_one ha))).width = s.readWidth a := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have h1 : (s.comp (readState a ha0)).mob 1 = s.mob (1 / (1 + a)) := by
    rw [mob_comp s _ zero_le_one, readState_mob]
  have h0 : (s.comp (readState a ha0)).mob 0 = s.mob (1 / a) := by
    rw [mob_comp s _ (le_refl 0), readState_mob]
    norm_num
  rw [width, h1, h0, readWidth, abs_sub_comm]
  congr 2
  ring

/-- S7-RD's upper bound, as a statement about the next state. -/
theorem width_comp_readState_le (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readState a (lt_of_lt_of_le zero_lt_one ha))).width
      ≤ s.distortion * s.width / (a * (a + 1)) := by
  rw [width_comp_readState s ha]; exact s.readWidth_le ha

/-- S7-RD's lower bound, likewise — so the chain is two-sided and loses nothing. -/
theorem le_width_comp_readState (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    s.width / (s.distortion * (a * (a + 1)))
      ≤ (s.comp (readState a (lt_of_lt_of_le zero_lt_one ha))).width := by
  rw [width_comp_readState s ha]; exact s.readWidth_ge ha

/-- **The chainable lag step.**  This is exactly the shape of `deficit_telescope_le`'s `hstep`,
with `ξ = log (a(a+1)) + log distortion` and no emission gain yet. -/
theorem deficit_comp_readState_le (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readState a (lt_of_lt_of_le zero_lt_one ha))).deficit
      ≤ s.deficit + Real.log (a * (a + 1)) + Real.log s.distortion := by
  have h := s.deficit_read_le ha
  rw [deficit, width_comp_readState s ha]
  exact h

section Audit

#print axioms MobState.width_comp_readState
#print axioms MobState.width_comp_readState_le
#print axioms MobState.le_width_comp_readState
#print axioms MobState.deficit_comp_readState_le

end Audit

end MobState

end NormalNumbers.VandeheyS7
