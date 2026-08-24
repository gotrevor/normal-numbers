/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFAffine
import NormalNumbers.CFOrbitFreq

/-!
# B6 / L4–L5 — the affine-image witness (interleaved schedule)

Expedition **B6** (`KHINCHIN.md` §B6), the crux.  Target (single affine map):
a real `x` with BOTH `x` and its affine image `ψ(x) = q·x + r` CF-normal.

**Reduction (proved here).**  By `isCFNormal_of_irrational_orbit_freq`
(`CFOrbitFreq`), CF-normality of a real reduces to: irrational in `(0,1)` +
Gauss-orbit equidistribution (`CFOrbitEquidist` below).  So the whole target
follows from ONE existence statement — `exists_interleaved_affine_witness`: a
single `x` for which BOTH `x` and `ψ(x)` are irrational in `(0,1)` with
equidistributing orbits.

**The crux (disclosed `sorry`: `exists_interleaved_affine_witness`).**  This is
the interleaved (diagonal) schedule of `PENDING_WORK.md`: build `x` as a limit
of nested `x`-intervals whose stages ALTERNATE — `x`-stages refine to a good
`x`-cylinder (fixing `x`'s own CF digits, the B5′ mechanism), `ψ`-stages refine
so `ψ(x)` enters a prescribed good `ψ`-cylinder (feasible because
`good_mass_in_affine_preimage` gives positive good `x`-density inside
`ψ⁻¹(good ψ-cylinder)`, and `volume_preimage_affineMap` bounds the pullback bad
zone).  Over infinitely many alternating stages both digit sequences become
CF-normal, giving both orbit equidistributions.  Formalizing it means mirroring
the `CFSchedule`/`CFCorrect` apparatus for two interleaved streams (copy-extend
the frozen modules; never edit them).  Broken into named pieces in
`PENDING_WORK.md`; multi-lap.

Additive only: no edits to any frozen B5′ module.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- Gauss-orbit equidistribution: the orbit block-count frequency of every
genuine CF pattern `v` tends to its Gauss measure.  The `CFOrbitFreq` interface
turns this (plus irrationality) into `IsCFNormal`. -/
def CFOrbitEquidist (y : ℝ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
    Filter.Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ))
      Filter.atTop (nhds (gaussMeasure (cfCylinder v)).toReal)

/-- **THE B6 CRUX (interleaved-schedule witness).**  For any `q > 0`, `r`, there
is a single real `x` such that both `x` and `ψ(x) = q·x + r` are irrational in
`(0,1)` with equidistributing Gauss orbits.  Disclosed `sorry`: this is the
interleaved schedule (module docstring + `PENDING_WORK.md`); the metric
substrate it consumes (L1–L3, the pullback measure, the orbit-frequency
interface) is all proved and axiom-clean. -/
theorem exists_interleaved_affine_witness {q : ℝ} (hq : 0 < q) (r : ℝ) :
    ∃ x : ℝ,
      (Irrational x ∧ x ∈ Set.Ioo (0 : ℝ) 1 ∧ CFOrbitEquidist x) ∧
      (Irrational (affineMap q r x) ∧ affineMap q r x ∈ Set.Ioo (0 : ℝ) 1
        ∧ CFOrbitEquidist (affineMap q r x)) := by
  sorry

/-- **B6 target (single affine map).**  There is a real `x` with both `x` and
its affine image `q·x + r` CF-normal — a constructive data point on Vandehey
(Compositio 2017) §7 problem 1 for `q > 0`.  Reduced to the interleaved-schedule
witness via the orbit-frequency interface. -/
theorem exists_cfNormal_and_affine_cfNormal {q : ℝ} (hq : 0 < q) (r : ℝ) :
    ∃ x : ℝ, IsCFNormal x ∧ IsCFNormal (affineMap q r x) := by
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, ⟨hy1, hy2, hy3⟩⟩ := exists_interleaved_affine_witness hq r
  exact ⟨x, isCFNormal_of_irrational_orbit_freq x hx1 hx2 hx3,
    isCFNormal_of_irrational_orbit_freq (affineMap q r x) hy1 hy2 hy3⟩

end NormalNumbers
