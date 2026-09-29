/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Convergent

/-!
# The window lemma, assembled

Four laps of structure meet here.

* Reading an input digit lands the state in `c ≤ d`, so its distortion is `≤ 2`
  (`VandeheyS7Branch.distortion_runWord_le_two`) — free, from any initial state, over any ring.
* A burst of emissions is ONE pullback, and `VandeheyS7Burst.distortion_pullback` computes its
  cost exactly: `distortion · (β − M 1)/(β − M 0)`, with `β = P/Q` the previous convergent of the
  emitted word.
* `VandeheyS7Convergent.conv_far_le_two_near` bounds that cost by `2`, for every emitted word of
  every length — the burst length cancels out of the estimate.

This file puts the three together.  `windowBound` : a state of distortion `≤ 2` whose image
endpoints sit in the emitted word's cylinder has post-burst distortion `≤ 4`.

## The only hypothesis left

`TriggerGap s w` — the emission trigger, in the only form the estimate uses: the two image
endpoints' distances to `β` lie between the cylinder's near and far distances.  That is exactly
"the image interval lies in the cylinder of the emitted word", which is what emission *means*;
turning the machine's operational trigger into this inequality is the remaining bookkeeping, and
it involves no estimate.

## Guard rule

Content locator: `triggerGap_endpoints` — the cylinder's own endpoints satisfy `TriggerGap`, so
the hypothesis is not empty.  Degenerate case: `conv_near_ne_zero` shows the near distance is
never `0`, so the ratio in `windowBound` is never `0/0`; this is the only place the continuant
determinant is used, and it is used only as a nonzero.
-/

namespace NormalNumbers.VandeheyS7

open Conv

/-! ## The two distances -/

/-- The near endpoint of the cylinder of `w`: `(p + p')/(q + q')`. -/
noncomputable def cylNear (w : List ℕ) : ℝ :=
  (((of w).p : ℝ) + (of w).p') / (((of w).q : ℝ) + (of w).q')

/-- The far endpoint of the cylinder of `w`: `p/q`. -/
noncomputable def cylFar (w : List ℕ) : ℝ := ((of w).p : ℝ) / (of w).q

/-- The previous convergent, `β = p'/q'`. -/
noncomputable def cylBeta (w : List ℕ) : ℝ := ((of w).p' : ℝ) / (of w).q'

/-- The near distance is `Δ / ((q + q') q')`, hence nonzero: the ONLY use of the continuant
determinant, and only as a nonzero. -/
theorem conv_near_ne_zero (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cylNear w - cylBeta w ≠ 0 := by
  obtain ⟨-, -, -, hq, -, hdet⟩ := good_of w hpos
  have hq1 : (1 : ℝ) ≤ ((of w).q : ℝ) := by exact_mod_cast hq
  have hq'1 : (1 : ℝ) ≤ ((of w).q' : ℝ) := by exact_mod_cast one_le_q'_of w hw hpos
  have hΔ : ((of w).p * (of w).q' - (of w).p' * (of w).q) ≠ 0 := by
    intro h; rw [h] at hdet; norm_num at hdet
  have hΔR : (((of w).p : ℝ) * (of w).q' - ((of w).p' : ℝ) * (of w).q) ≠ 0 := by
    exact_mod_cast hΔ
  have hid : cylNear w - cylBeta w
      = (((of w).p : ℝ) * (of w).q' - ((of w).p' : ℝ) * (of w).q)
        / ((((of w).q : ℝ) + (of w).q') * ((of w).q' : ℝ)) := by
    unfold cylNear cylBeta
    field_simp
    ring
  rw [hid]
  exact div_ne_zero hΔR (by positivity)

/-- `far ≤ 2 · near`, restated in the names of this file. -/
theorem cyl_far_le_two_near (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    |cylFar w - cylBeta w| ≤ 2 * |cylNear w - cylBeta w| :=
  conv_far_le_two_near w hw hpos

/-! ## The trigger -/

/-- **The emission trigger, in the form the estimate uses.**  Both image endpoints lie in the
cylinder of the emitted word `w`, measured by their distance to `β`. -/
def TriggerGap (s : MobState) (w : List ℕ) : Prop :=
  |cylNear w - cylBeta w| ≤ |s.mob 0 - cylBeta w| ∧
    |s.mob 0 - cylBeta w| ≤ |cylFar w - cylBeta w| ∧
    |cylNear w - cylBeta w| ≤ |s.mob 1 - cylBeta w| ∧
    |s.mob 1 - cylBeta w| ≤ |cylFar w - cylBeta w|

/-- Content locator: the cylinder's own endpoints satisfy the trigger inequalities, so the
hypothesis is not empty. -/
theorem triggerGap_endpoints (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    {s : MobState} (h0 : s.mob 0 = cylNear w) (h1 : s.mob 1 = cylFar w) :
    TriggerGap s w := by
  have hk := conv_ratio_le_two w hpos
  have heq : cylFar w - cylBeta w
      = ((((of w).q : ℝ) + (of w).q') / (of w).q) * (cylNear w - cylBeta w) := by
    unfold cylFar cylBeta cylNear
    exact conv_far_eq w hw hpos
  set k : ℝ := (((of w).q : ℝ) + (of w).q') / (of w).q with hkdef
  have hk1 : 1 ≤ k := hk.2
  have hle : |cylNear w - cylBeta w| ≤ |cylFar w - cylBeta w| := by
    rw [heq, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ k)]
    nlinarith [abs_nonneg (cylNear w - cylBeta w)]
  exact ⟨h0 ▸ le_refl _, h0 ▸ hle, h1 ▸ hle, h1 ▸ le_refl _⟩

/-! ## The window bound -/

/-- **The window lemma.**  A state whose distortion is at most `2` — which reading gives for
free — and whose image endpoints sit in the emitted word's cylinder has post-burst distortion at
most `4`.  The emitted word's length does not appear. -/
theorem windowBound (s : MobState) (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    (hD : s.distortion ≤ 2) (htrig : TriggerGap s w)
    (hQ : ((of w).q' : ℝ) ≠ 0)
    (hden0 : ((of w).p' : ℝ) * s.d - ((of w).q' : ℝ) * s.b ≠ 0)
    (hden1 : ((of w).p' : ℝ) * (s.c + s.d) - ((of w).q' : ℝ) * (s.a + s.b) ≠ 0) :
    |(((of w).p' : ℝ) * (s.c + s.d) - ((of w).q' : ℝ) * (s.a + s.b))
      / (((of w).p' : ℝ) * s.d - ((of w).q' : ℝ) * s.b)| ≤ 4 := by
  obtain ⟨hn0, hf0, hn1, hf1⟩ := htrig
  have hnear : (0 : ℝ) < |cylNear w - cylBeta w| :=
    abs_pos.2 (conv_near_ne_zero w hw hpos)
  have hfar := cyl_far_le_two_near w hw hpos
  have hb0 : (0 : ℝ) < |s.mob 0 - cylBeta w| := lt_of_lt_of_le hnear hn0
  -- the exact pullback identity, then bound the ratio by `far / near ≤ 2`
  have hident := MobState.distortion_pullback s ((of w).p' : ℝ) ((of w).q' : ℝ) hQ hden0 hden1
  rw [hident, abs_mul, abs_of_nonneg s.distortion_pos.le, abs_div]
  have hratio : |cylBeta w - s.mob 1| / |cylBeta w - s.mob 0| ≤ 2 := by
    rw [div_le_iff₀ (by simpa [abs_sub_comm] using hb0)]
    have e1 : |cylBeta w - s.mob 1| = |s.mob 1 - cylBeta w| := abs_sub_comm _ _
    have e0 : |cylBeta w - s.mob 0| = |s.mob 0 - cylBeta w| := abs_sub_comm _ _
    rw [e1, e0]
    linarith
  have hcb : cylBeta w = ((of w).p' : ℝ) / ((of w).q' : ℝ) := rfl
  rw [← hcb]
  nlinarith [s.distortion_pos, abs_nonneg (cylBeta w - s.mob 1),
    abs_nonneg (cylBeta w - s.mob 0),
    div_nonneg (abs_nonneg (cylBeta w - s.mob 1)) (abs_nonneg (cylBeta w - s.mob 0))]

section Audit

#print axioms conv_near_ne_zero
#print axioms windowBound

end Audit

end NormalNumbers.VandeheyS7
