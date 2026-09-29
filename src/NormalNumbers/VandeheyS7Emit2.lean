/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-E2: the emission gain in `comp` form — `hstep` is now complete

S7-RC gave the read half of `deficit_telescope_le`'s `hstep`.  This module gives the emission half,
and with it the per-step lag inequality is fully assembled from kernel theorems.

The emission of the output word `w` is *not* a `MobState` composition on the left: the inverse digit
matrix `[[-b,1],[1,0]]` has a negative entry, and `MobState` requires a nonnegative upper row (for
good reason — that is what makes the family closed under `comp`).  The relation to state instead in
the direction that *is* a composition:

    s  =  R_w.comp s'          (`s` before emitting `w`, `s'` after)

where `R_w` is the cylinder map of `w`, a product of `readState`s.  Then the general identity

    (R.comp t).width = |det R| · t.width / (den_R(t.mob 0) · den_R(t.mob 1))     `width_comp_eq`

shows emission **widens**: the pre-emission state is the narrow one, by the factor `den²`.  Since
`den_R ≥ R.d` and for a CF cylinder map `R.d` is the continuant `cfK w ≥ fib(|w|+1)`, the lag drops
by `2 log R.d` per emitted block — `deficit_comp_ge`.  That is exactly the `c · blockLength` term of
`deficit_telescope_le`, and lap 74's `fib_sq_mul_width_le_of_forced` is its `fib` form.

So the two halves now match the abstract hypothesis shape exactly:

| `hstep` term | supplied by |
|---|---|
| `+ ξ n` (read cost) | `deficit_comp_readState_le` (S7-RC) |
| `− c · Lₙ` (emission gain) | `deficit_comp_ge` (here), with `c = 2 log R.d / Lₙ` |

What is *not* supplied, and is the honest remaining gap: identifying `R.d` for the actual emitted
block with `cfK` of the emitted word, which is transducer bookkeeping
(`StateCoupling`), not analysis.  The analysis is done.
-/
import NormalNumbers.VandeheyS7ReadComp

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- A state maps `[0,∞)` into `[0,∞)`: both numerator and denominator are nonnegative. -/
lemma mob_nonneg (s : MobState) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ s.mob x := by
  have hden : 0 < s.c * x + s.d := s.den_pos hx
  have hnum : 0 ≤ s.a * x + s.b := add_nonneg (mul_nonneg s.ha hx) s.hb
  exact div_nonneg hnum hden.le

/-- **The composition width identity.**  Exact, with no inequality: the outer state contracts the
inner state's width by the product of its two denominators. -/
theorem width_comp_eq (R t : MobState) :
    (R.comp t).width
      = |R.a * R.d - R.b * R.c| * t.width
          / ((R.c * t.mob 0 + R.d) * (R.c * t.mob 1 + R.d)) := by
  have h0 : 0 ≤ t.mob 0 := t.mob_nonneg (le_refl 0)
  have h1 : 0 ≤ t.mob 1 := t.mob_nonneg zero_le_one
  have hd0 : 0 < R.c * t.mob 0 + R.d := R.den_pos h0
  have hd1 : 0 < R.c * t.mob 1 + R.d := R.den_pos h1
  rw [width, mob_comp R t zero_le_one, mob_comp R t (le_refl 0), R.mob_sub h0 h1,
    abs_div, abs_of_pos (mul_pos hd1 hd0), abs_mul, width]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Emission **widens**: the pre-emission state is narrower by at least `R.d²`. -/
theorem width_comp_le (R t : MobState) :
    (R.comp t).width ≤ |R.a * R.d - R.b * R.c| * t.width / (R.d * R.d) := by
  have h0 : 0 ≤ t.mob 0 := t.mob_nonneg (le_refl 0)
  have h1 : 0 ≤ t.mob 1 := t.mob_nonneg zero_le_one
  have hd : 0 < R.d := R.hd
  have hlow : R.d * R.d ≤ (R.c * t.mob 0 + R.d) * (R.c * t.mob 1 + R.d) :=
    mul_le_mul (R.le_den h0) (R.le_den h1) hd.le (le_of_lt (R.den_pos h0))
  have hnum : (0:ℝ) ≤ |R.a * R.d - R.b * R.c| * t.width :=
    mul_nonneg (abs_nonneg _) t.width_pos.le
  rw [width_comp_eq R t]
  gcongr

/-- **The emission gain, in `comp` form.**  A unimodular outer state with `d ≥ D > 0` costs the
pre-emission state `2 log D` of extra lag — equivalently, emitting buys `2 log D` back.  This is
`deficit_telescope_le`'s `c · blockLength` term. -/
theorem deficit_comp_ge (R t : MobState) (hdet : |R.a * R.d - R.b * R.c| = 1)
    {D : ℝ} (hD0 : 0 < D) (hD : D ≤ R.d) :
    t.deficit + 2 * Real.log D ≤ (R.comp t).deficit := by
  have hw : 0 < t.width := t.width_pos
  have hcw : 0 < (R.comp t).width := (R.comp t).width_pos
  have hRd : 0 < R.d := R.hd
  have hle : (R.comp t).width ≤ t.width / (D * D) := by
    refine le_trans (width_comp_le R t) ?_
    rw [hdet, one_mul]
    have hsq : D * D ≤ R.d * R.d := by nlinarith [R.hd]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hw.le, hsq]
  have hlog : Real.log ((R.comp t).width) ≤ Real.log (t.width / (D * D)) :=
    Real.log_le_log hcw hle
  have hexp : Real.log (t.width / (D * D)) = Real.log t.width - 2 * Real.log D := by
    rw [Real.log_div hw.ne' (by positivity), Real.log_mul hD0.ne' hD0.ne']
    ring
  rw [hexp] at hlog
  simp only [deficit]
  linarith

/-- The `fib` form, matching lap 74: a block of length `L` whose cylinder map has
`fib (L+1) ≤ R.d` buys `2 log fib (L+1)` of lag. -/
theorem deficit_comp_fib_ge (R t : MobState) (hdet : |R.a * R.d - R.b * R.c| = 1)
    {L : ℕ} (hfib : 0 < Nat.fib (L + 1)) (hD : (Nat.fib (L + 1) : ℝ) ≤ R.d) :
    t.deficit + 2 * Real.log (Nat.fib (L + 1)) ≤ (R.comp t).deficit :=
  deficit_comp_ge R t hdet (by exact_mod_cast hfib) hD

section Audit

#print axioms MobState.mob_nonneg
#print axioms MobState.width_comp_eq
#print axioms MobState.width_comp_le
#print axioms MobState.deficit_comp_ge
#print axioms MobState.deficit_comp_fib_ge

end Audit

end MobState

end NormalNumbers.VandeheyS7
