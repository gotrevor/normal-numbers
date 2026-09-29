/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CR: the conjugate bottom row, and why the two bad regimes are NOT disjoint

Lap 75's S7-TD left exactly one tractable question on the §7 front.  The S7-RD cancellation (which
would make the clock rate unconditional) needs the straddle cap where the state is **narrow**;
S7-DC kills the cap where the conjugate height is **large**.  If those regimes were disjoint the
clock-rate debt would close.  **They are not, and this module proves it.**

Two things are established.

## 1.  The conjugate bottom row is an integer translate of the real one

For the additive instance `Φ = [[1,φ],[0,1]]` the Galois conjugate is `Φ' = [[1,ψ],[0,1]]`, and the
two differ only in the `(1,2)` entry.  Writing the state as `s = O⁻¹ Φ P`, the bottom rows satisfy

    row₂(s') − row₂(s) = (ψ − φ) · (O⁻¹)₂₁ · row₂(P) = −√5 · (O⁻¹)₂₁ · row₂(P).

`addStateBottom_sub` is the algebraic identity and `conjRow_sub_eq` is the `√5` form.  This is the
exact sense in which the second archimedean place is *not* free: the conjugate bottom row is
determined by the real one together with the single integer `(O⁻¹)₂₁` and the input convergent's
bottom row.  It is also the reason the conjugate height grows — `|row₂(P)| ≍ q_in`.

## 2.  Narrow does not imply small conjugate height

`exists_narrow_state_large_conj`: for every `ε > 0` and every `R` there is a genuine `MobState` with
`|det| = 1`-shaped data, `width < ε`, and conjugate entry height `> R` — take `(c, d) = (1, m)` with
`m` large, whose `ℤ[φ]`-conjugate is again `(1, m)`.  A rational state is its own conjugate, so
narrowness buys nothing at the second place.

**Verdict.**  The two bad regimes overlap, so the clock-rate debt does *not* close by disjointness.
The clock rate and fact (α) therefore both sit behind second-place control; the §7 front is one
hypothesis wide and that hypothesis is the wall.  This closes the last non-wall question raised by
S7-TD, negatively, in the kernel.
-/
import NormalNumbers.VandeheyS7Transduce

namespace NormalNumbers.VandeheyS7

open Real

/-- The bottom row of `O⁻¹ · [[1,t],[0,1]] · P`, written out in the entries that matter:
`o21, o22` from `O⁻¹` and the two rows of `P`. -/
def addStateBottom (o21 o22 p11 p12 p21 p22 t : ℝ) : ℝ × ℝ :=
  (o21 * (p11 + t * p21) + o22 * p21, o21 * (p12 + t * p22) + o22 * p22)

/-- **The translate identity.**  Changing the `(1,2)` entry of `Φ` from `u` to `t` moves the state's
bottom row by `(t − u) · o21 · row₂(P)` — and by nothing else. -/
theorem addStateBottom_sub (o21 o22 p11 p12 p21 p22 t u : ℝ) :
    ((addStateBottom o21 o22 p11 p12 p21 p22 t).1
        - (addStateBottom o21 o22 p11 p12 p21 p22 u).1,
      (addStateBottom o21 o22 p11 p12 p21 p22 t).2
        - (addStateBottom o21 o22 p11 p12 p21 p22 u).2)
      = ((t - u) * o21 * p21, (t - u) * o21 * p22) := by
  simp only [addStateBottom, Prod.mk.injEq]
  constructor <;> ring

/-- **The `√5` form.**  For the additive instance the conjugate bottom row differs from the real one
by `−√5 · o21 · row₂(P)`: the second place is pinned to the first by one integer and the input
convergent, which is also why it grows like `q_in`. -/
theorem conjRow_sub_eq (o21 o22 p11 p12 p21 p22 : ℝ) :
    ((addStateBottom o21 o22 p11 p12 p21 p22 goldenConj).1
        - (addStateBottom o21 o22 p11 p12 p21 p22 goldenRatio).1,
      (addStateBottom o21 o22 p11 p12 p21 p22 goldenConj).2
        - (addStateBottom o21 o22 p11 p12 p21 p22 goldenRatio).2)
      = (-Real.sqrt 5 * o21 * p21, -Real.sqrt 5 * o21 * p22) := by
  have h5 : goldenConj - goldenRatio = -Real.sqrt 5 := by
    simp only [goldenRatio, goldenConj]
    ring
  rw [addStateBottom_sub, h5]

/-! ## Narrow does not imply small conjugate height -/

/-- The narrow state with a rational bottom row `(1, m)`: `a = 1, b = 0, c = 1, d = m`. -/
noncomputable def narrowState (m : ℕ) (hm : 1 ≤ m) : MobState where
  a := 1
  b := 0
  c := 1
  d := (m : ℝ)
  ha := zero_le_one
  hb := le_refl 0
  hc := zero_le_one
  hd := by exact_mod_cast hm
  hdet := by
    have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
    intro hc
    nlinarith

lemma narrowState_width (m : ℕ) (hm : 1 ≤ m) :
    (narrowState m hm).width = 1 / (1 + (m : ℝ)) := by
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [MobState.width_eq]
  show |(1:ℝ) * (m : ℝ) - 0 * 1| / (((1:ℝ) + (m : ℝ)) * (m : ℝ)) = _
  rw [show (1:ℝ) * (m : ℝ) - 0 * 1 = (m : ℝ) by ring, abs_of_pos hmR]
  field_simp

/-- **The refutation.**  Narrowness does not buy smallness at the second place: for every `ε > 0`
and every `R` there is a `MobState` of width `< ε` whose bottom-row entries, read as `ℤ[φ]`-numbers,
have conjugates of size `> R`.  A rational state is its own conjugate.

So the regime where the S7-RD cancellation needs the straddle cap (narrow) is *not* disjoint from
the regime where S7-DC kills the cap (large conjugate height), and the clock-rate debt does not
close by disjointness. -/
theorem exists_narrow_state_large_conj {ε R : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (hm : 1 ≤ m), (narrowState m hm).width < ε ∧
      R < |zconj (m : ℤ) 0| ∧ zval (m : ℤ) 0 = (narrowState m hm).d := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max R (1 / ε))
  refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
  · rw [narrowState_width]
    have hkR : 1 / ε < ((k : ℝ) + 1) := by
      have := lt_of_le_of_lt (le_max_right R (1 / ε)) hk
      push_cast at this ⊢
      linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hkR
    push_cast
    nlinarith
  · have hzc : |zconj ((k : ℤ) + 1) 0| = ((k : ℝ) + 1) := by
      have h : zconj ((k : ℤ) + 1) 0 = ((k : ℝ) + 1) := by
        simp only [zconj]; push_cast; ring
      rw [h, abs_of_pos (by positivity)]
    push_cast [hzc]
    have := lt_of_le_of_lt (le_max_left R (1 / ε)) hk
    push_cast at this ⊢
    linarith
  · show zval (((k + 1 : ℕ) : ℤ)) 0 = ((k + 1 : ℕ) : ℝ)
    simp only [zval]; push_cast; ring

section Audit

#print axioms addStateBottom_sub
#print axioms conjRow_sub_eq
#print axioms narrowState_width
#print axioms exists_narrow_state_large_conj

end Audit

end NormalNumbers.VandeheyS7
