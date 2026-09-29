/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-IN: the `hΦ` hypothesis of the §7 front is a triviality

Lap 76 left `MapState.orbitWordBound_of_runBlockAverage` with three hypotheses, and called the
middle one — "the affine map is a `MapState`" — a five-line instance nobody had written, to be
obtained by absorbing `⌊φ·fract x⌋` into the matrix.  That reading is wrong, and the lap-77 review
says why: `MapState` has REAL entries and asks only `det ≠ 0`, so the *near-constant* map

    Φ_ε : z ↦ v + ε·(z − u),      ε = min v (1−v) / 2

is a legitimate state sending any `u ∈ (0,1)` to any `v ∈ (0,1)`.  No case analysis, no golden
ratio, no absorbed integer part.

* `MapState.exists_mob_eq` — the interpolant.
* `orbitWordBound_of_runBlockAverage_all` — `hΦ` discharged: the §7 front is
  `AffineImageIrrational + BlockAverageBound`, full stop.

Two caveats, both recorded so nobody re-learns them:

1. The interpolant is only legal because of `hdet`; the CONSTANT map (`a = c = 0`, `b = v`,
   `d = 1`) has `det = 0` and is excluded.  That is the guard S7-SA's vacuity lesson bought.
2. Because `hΦ` is free, ALL the content of the front sits in `hBA`, whose `∀ Φ` form therefore
   ranges over degenerate states too.  `orbitWordBound_of_runBlockAverage_one` is the sharpened
   statement that asks for `BlockAverageBound` at ONE `Φ` only; use that one when discharging.
-/
import NormalNumbers.VandeheyS7RunPin

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

/-- **The interpolant.**  Any point of `(0,1)` is sent to any point of `(0,1)` by a legitimate
`MapState` — the near-constant map `z ↦ v + ε(z − u)`. -/
theorem exists_mob_eq {u v : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) (hv : v ∈ Set.Ioo (0:ℝ) 1) :
    ∃ Φ : MapState, Φ.mob u = v := by
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hu0, hu1⟩ := hu
  set ε : ℝ := min v (1 - v) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    have : 0 < min v (1 - v) := lt_min hv0 (by linarith)
    linarith
  have hεv : ε ≤ v / 2 := by
    rw [hε]
    have : min v (1 - v) ≤ v := min_le_left _ _
    linarith
  have hε1v : ε ≤ (1 - v) / 2 := by
    rw [hε]
    have : min v (1 - v) ≤ 1 - v := min_le_right _ _
    linarith
  have hεu0 : 0 ≤ ε * u := mul_nonneg hεpos.le hu0.le
  have hεu1 : ε * u ≤ ε := by nlinarith
  refine ⟨?_, ?_⟩
  · exact
      { a := ε
        b := v - ε * u
        c := 0
        d := 1
        hd := zero_lt_one
        hcd := by norm_num
        hb0 := by linarith
        hbd := by linarith
        hab0 := by linarith
        habcd := by linarith
        hdet := by
          show ε * 1 - (v - ε * u) * 0 ≠ 0
          simpa using hεpos.ne' }
  · show (ε * u + (v - ε * u)) / (0 * u + 1) = v
    rw [zero_mul, zero_add, div_one]
    ring

/-- **The `hΦ` hypothesis, discharged.**  For any `x` whose fractional part and whose affine image
are both irrational, an interpolating `MapState` exists. -/
theorem exists_mapState_affine {q r₀ : ℝ} (hirr : AffineImageIrrational q r₀) (x : ℝ)
    (hx : IsCFNormal (Int.fract x)) :
    ∃ Φ : MapState, Φ.mob (Int.fract x) = Int.fract (q * x + r₀) := by
  have hx0 : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  have hxmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hx0).2
  have hymem : Int.fract (q * x + r₀) ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem (hirr x hx)).2
  exact exists_mob_eq hxmem hymem

/-- **S7-IN.**  The §7 front, with `hΦ` gone: `AffineImageIrrational` plus the block average
bound. -/
theorem orbitWordBound_of_runBlockAverage_all {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀)
    (hBA : ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
      ∀ Φ : MapState, Φ.mob (Int.fract x) = Int.fract (q * x + r₀) →
      BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x)
        (runClock Φ (Int.fract x))
        (fun n j => mapBlockSet (runState Φ (Int.fract x) n) w j)) :
    OrbitWordBound q r₀ C :=
  orbitWordBound_of_runBlockAverage hC hirr (exists_mapState_affine hirr) hBA

/-- **The sharpened front.**  Only ONE `Φ` needs the block average bound.  This is the statement
to discharge; the `∀ Φ` form above is strictly stronger as a hypothesis and therefore weaker as a
theorem. -/
theorem orbitWordBound_of_runBlockAverage_one {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀)
    (hBA : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ∃ Φ : MapState, Φ.mob (Int.fract x) = Int.fract (q * x + r₀) ∧
        ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
          BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x)
            (runClock Φ (Int.fract x))
            (fun n j => mapBlockSet (runState Φ (Int.fract x) n) w j)) :
    OrbitWordBound q r₀ C := by
  intro x hx w hw ε hε
  obtain ⟨Φ, hΦeq, hΦBA⟩ := hBA x hx
  have hx0 : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  have hxirr : Irrational (Int.fract x) := (irrational_fract_mem hx0).1
  have hxmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hx0).2
  have hxo : ∀ k, gaussMap^[k] (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 :=
    fun k => (irrational_orbit _ hxirr hxmem k).2
  have hyirr0 : Irrational (q * x + r₀) := hirr x hx
  have hymem : Int.fract (q * x + r₀) ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hyirr0).2
  have hyirr : Irrational (Int.fract (q * x + r₀)) := (irrational_fract_mem hyirr0).1
  have hy : Φ.mob (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 := by rw [hΦeq]; exact hymem
  have hyi : Irrational (Φ.mob (Int.fract x)) := by rw [hΦeq]; exact hyirr
  have hB : 0 ≤ C * (gaussMeasure (cfCylinder w)).toReal :=
    mul_nonneg hC ENNReal.toReal_nonneg
  have hcoup := runBlockCoupling Φ hxo hy hyi w
  rw [hΦeq] at hcoup
  exact freq_le_of_blockAverage_mono hcoup (runClock_ratio_tendsto Φ hxo hy hyi) hB
    (hΦBA w hw) ε hε

end MapState

section Audit

#print axioms MapState.exists_mob_eq
#print axioms MapState.exists_mapState_affine
#print axioms MapState.orbitWordBound_of_runBlockAverage_all
#print axioms MapState.orbitWordBound_of_runBlockAverage_one

end Audit

end NormalNumbers.VandeheyS7
