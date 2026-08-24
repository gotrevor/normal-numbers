/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFWordBridge
import NormalNumbers.Headline

/-!
# B6 / L4 kernel — CF-normality from an orbit-frequency criterion

An `x`-generic interface lemma for the affine-image campaign (`KHINCHIN.md` §B6,
L4).  `IsCFNormal y` (`Headline.lean`) is a *digit-window* frequency statement;
this reduces it to a Gauss-*orbit* frequency statement (Birkhoff form): if every
Gauss iterate of `y` stays in `(0,1)` and the orbit block-count frequency
`blockCount (cfCylinder v) p y / p → γ(I_v)` for every genuine pattern `v`, then
`y` is CF-normal.

The reduction is the `x`-generic bridge `blockCount_sub_countOccurrences_bounds`
(`CFWordBridge`): the orbit count and the digit-window count differ by at most
`|v|` boundary windows, a vanishing fraction.  Because it takes `y` as a free
variable, it applies UNCHANGED to both `xstar` and its affine image
`ψ(xstar) = q·xstar + r` — the shared endgame of L5.  Additive over B5′.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- **CF-normality from orbit frequencies** (`x`-generic).  If the Gauss orbit
of `y` never leaves `(0,1)` and its block-count frequency tends to `γ(I_v)` for
every genuine `v`, then `y` is CF-normal.  The window↔orbit gap is `≤ |v|`
(`blockCount_sub_countOccurrences_bounds`), which `/p → 0`. -/
theorem isCFNormal_of_orbit_freq (y : ℝ)
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1)
    (hfreq : ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Filter.Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ))
        Filter.atTop (nhds (gaussMeasure (cfCylinder v)).toReal)) :
    IsCFNormal y := by
  intro v hne hpos
  set γv := (gaussMeasure (cfCylinder v)).toReal with hγ
  set B : ℕ → ℝ := fun p => blockCount (cfCylinder v) p y with hB
  set A : ℕ → ℕ := fun p => countOccurrences v ((List.range p).map (cfDigit y)) with hA
  show Filter.Tendsto (fun p => (A p : ℝ) / (p : ℝ)) Filter.atTop (nhds γv)
  have hbnds : ∀ p, (A p : ℝ) ≤ B p ∧ B p ≤ (A p : ℝ) + v.length := by
    intro p
    have h := blockCount_sub_countOccurrences_bounds horb v hne 0 p
    simp only [Function.iterate_zero_apply, Nat.zero_add] at h
    exact h
  have hBfreq : Tendsto (fun p => B p / (p : ℝ)) atTop (nhds γv) := hfreq v hne hpos
  have hzero : Tendsto (fun p : ℕ => (v.length : ℝ) / (p : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlow : Tendsto (fun p => B p / (p : ℝ) - (v.length : ℝ) / (p : ℝ))
      atTop (nhds γv) := by simpa using hBfreq.sub hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hBfreq ?_ ?_
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
      rw [← sub_div]
      gcongr
      linarith [(hbnds p).2]
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
      gcongr
      exact (hbnds p).1

/-- **CF-normality from orbit frequencies, irrational form.**  Irrationals in
`(0,1)` automatically have a full Gauss orbit (`irrational_orbit`), so the
`horb` hypothesis of `isCFNormal_of_orbit_freq` is discharged.  This is the
interface the affine-image endgame (L5) uses: the schedule delivers
`ψ(xstar)` irrational in `(0,1)` (obligation A) and its orbit equidistributing
(obligation B), whence `IsCFNormal (ψ xstar)`. -/
theorem isCFNormal_of_irrational_orbit_freq (y : ℝ)
    (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hfreq : ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Filter.Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ))
        Filter.atTop (nhds (gaussMeasure (cfCylinder v)).toReal)) :
    IsCFNormal y :=
  isCFNormal_of_orbit_freq y (fun j => (irrational_orbit y hirr hy j).2) hfreq

end NormalNumbers
