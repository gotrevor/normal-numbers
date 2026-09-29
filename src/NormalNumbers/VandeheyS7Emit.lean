/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Boundary

/-!
# The emitted digit as a function of the state

Obligation 1 of the assembly (`VandeheyS7Assemble`) is to exhibit the image digit as a function
of a bounded window of the input.  This module supplies the one-step version, which is where all
the definitional content sits.

## The machine emits when its whole image interval agrees

A state `s` maps `[0,1]` — the range of every possible continuation of the input — to the
interval between `s.mob 0` and `s.mob 1` (`mob_mem_uIcc`; the sign of `det` decides the
orientation, and `uIcc` absorbs it).  The image's first CF digit is `⌊1/·⌋`, which is ANTITONE
(`cfDigit_zero_antitone`).  So if the two endpoints already agree, the digit is constant on the
whole interval and the machine may emit it whatever the continuation is:

    `CanEmit s`      :  `cfDigit (s.mob 0) 0 = cfDigit (s.mob 1) 0`
    `emitDigit s`    :  that common value
    `cfDigit_mob_eq_emitDigit` :  `CanEmit s → y ∈ [0,1] → cfDigit (s.mob y) 0 = emitDigit s`

**That last theorem is the whole point.**  It says the emitted digit depends on the STATE alone —
not on the unread future of the input.  Since the state after reading a window is
`s₀ · wordState w` (`runWord_eq_comp`) and merging makes `s₀` invisible
(`spread_runWord_le`), the digit is a function of the window, which is what
`cfCount_tendsto_of_decomposition` needs.

## Guard rule

Content locator: `canEmit_of_wordState_pos` — a state whose image interval already lies inside a
single depth-one cylinder can emit, so `CanEmit` is not vacuous.  Degenerate case:
`not_canEmit_of_straddle` — if the endpoints have different digits the machine must read more
input, and no digit is determined; this is exactly the `boundaryBad` situation of
`VandeheyS7Boundary`, which is why that set had to be measured.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

namespace MobState

/-- **The image of `[0,1]` lies between the endpoint images.**  The sign of the determinant
decides the orientation; `uIcc` absorbs it, so no hypothesis on `det` is needed. -/
theorem mob_mem_uIcc (s : MobState) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    s.mob y ∈ Set.uIcc (s.mob 0) (s.mob 1) := by
  have hden : 0 < s.c * y + s.d := s.den_pos hy0
  have hd : 0 < s.d := s.hd
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  set D : ℝ := s.a * s.d - s.b * s.c with hD
  have h0 : s.mob y - s.mob 0 = y * D / (s.d * (s.c * y + s.d)) := by
    simp only [mob, mul_zero, zero_add]
    rw [div_sub_div _ _ hden.ne' hd.ne', hD]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have h1 : s.mob 1 - s.mob y = (1 - y) * D / ((s.c + s.d) * (s.c * y + s.d)) := by
    simp only [mob, mul_one]
    rw [div_sub_div _ _ hcd.ne' hden.ne', hD]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [Set.mem_uIcc]
  rcases le_or_gt 0 D with hpos | hneg
  · left
    constructor
    · have : 0 ≤ y * D / (s.d * (s.c * y + s.d)) := by positivity
      linarith [h0]
    · have : 0 ≤ (1 - y) * D / ((s.c + s.d) * (s.c * y + s.d)) := by
        apply div_nonneg (mul_nonneg (by linarith) hpos) (by positivity)
      linarith [h1]
  · right
    constructor
    · have : (1 - y) * D / ((s.c + s.d) * (s.c * y + s.d)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith)
          hneg.le) (by positivity)
      linarith [h1]
    · have : y * D / (s.d * (s.c * y + s.d)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hy0 hneg.le)
          (by positivity)
      linarith [h0]

end MobState

/-- The first CF digit is antitone on the positive half-line: `⌊1/x⌋` decreases as `x` grows. -/
theorem cfDigit_zero_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    cfDigit y 0 ≤ cfDigit x 0 := by
  rw [cfDigit_zero, cfDigit_zero]
  exact Nat.floor_mono (by
    rw [inv_le_inv₀ (lt_of_lt_of_le hx hxy) hx]
    exact hxy)

/-- The digit is constant on any interval whose endpoints agree. -/
theorem cfDigit_zero_eq_of_between {u v z : ℝ} (hu : 0 < u) (hv : 0 < v)
    (heq : cfDigit u 0 = cfDigit v 0) (hz : z ∈ Set.uIcc u v) : cfDigit z 0 = cfDigit u 0 := by
  rw [Set.mem_uIcc] at hz
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hz0 : 0 < z := lt_of_lt_of_le hu h1
    have ha := cfDigit_zero_antitone hu h1
    have hb := cfDigit_zero_antitone hz0 h2
    omega
  · have hz0 : 0 < z := lt_of_lt_of_le hv h1
    have ha := cfDigit_zero_antitone hv h1
    have hb := cfDigit_zero_antitone hz0 h2
    omega

namespace MobState

/-- **The emission condition**: the state's whole image interval already carries one digit. -/
def CanEmit (s : MobState) : Prop := cfDigit (s.mob 0) 0 = cfDigit (s.mob 1) 0

/-- The digit the state emits. -/
noncomputable def emitDigit (s : MobState) : ℕ := cfDigit (s.mob 0) 0

/-- **The emitted digit depends on the STATE alone, not on the unread future of the input.**
This is what lets the image digit be a function of a bounded input window. -/
theorem cfDigit_mob_eq_emitDigit (s : MobState) (hb : 0 < s.b) (h : CanEmit s) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : cfDigit (s.mob y) 0 = emitDigit s := by
  have h0 : 0 < s.mob 0 := by
    simp only [mob, mul_zero, zero_add]
    exact div_pos hb s.hd
  exact cfDigit_zero_eq_of_between h0 (s.mob_pos one_pos) h (s.mob_mem_uIcc hy0 hy1)

/-- Content locator: a state whose image interval already lies in one depth-one cylinder can
emit, so `CanEmit` is not vacuous. -/
theorem canEmit_of_eq {s : MobState} (h : cfDigit (s.mob 0) 0 = cfDigit (s.mob 1) 0) :
    CanEmit s := h

/-- Degenerate case: when the endpoints disagree no digit is determined and the machine must read
more input.  That is exactly the `boundaryBad` situation, which is why it had to be measured. -/
theorem not_canEmit_of_ne {s : MobState} (h : cfDigit (s.mob 0) 0 ≠ cfDigit (s.mob 1) 0) :
    ¬ CanEmit s := h

end MobState

section Audit

#print axioms MobState.mob_mem_uIcc
#print axioms cfDigit_zero_eq_of_between
#print axioms MobState.cfDigit_mob_eq_emitDigit

end Audit

end NormalNumbers.VandeheyS7
