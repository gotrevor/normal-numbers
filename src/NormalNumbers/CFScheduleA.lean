/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFAffine
import NormalNumbers.CFOrbitFreq
import NormalNumbers.CFFreqBlock

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

/-- **Cylinder inside an interval.**  Every nondegenerate subinterval `(a,b)` of
`(0,1)` contains a genuine CF cylinder.  Proof: `goodInInterval a b n 0` has
positive volume once `4/fib(n+1)² < b−a` (`goodInInterval_pos_of_lt`), so it is
nonempty; a point of it lies in `goodExtSet w goodC 0` for some genuine rank-`n`
word `w` with `cfCylinder w ⊆ (a,b)`.  This is the placement primitive the
interval-relativized frequency engine needs (pick a deep reference word inside
the target interval, then run `exists_freq_good_block` on it). -/
theorem exists_cfCylinder_subset_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    ∃ w : List ℕ, w ≠ [] ∧ (∀ c ∈ w, 1 ≤ c) ∧ cfCylinder w ⊆ Set.Ioo a b := by
  have hbma : 0 < b - a := by linarith
  obtain ⟨N, hN⟩ := exists_fib_threshold (4 / (b - a))
  set n := max N 1 with hndef
  have hn1 : 1 ≤ n := le_max_right _ _
  have hnN : N ≤ n := le_max_left _ _
  have hFpos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) ^ 2 := by
    have : 0 < Nat.fib (n + 1) := Nat.fib_pos.2 (by omega)
    positivity
  have hcmp : 4 / (b - a) < (Nat.fib (n + 1) : ℝ) ^ 2 := hN n hnN
  have h4 : 4 < (Nat.fib (n + 1) : ℝ) ^ 2 * (b - a) := by
    rw [div_lt_iff₀ hbma] at hcmp; linarith
  have hfib : 4 / (Nat.fib (n + 1) : ℝ) ^ 2 < b - a := by
    rw [div_lt_iff₀ hFpos]; nlinarith [h4]
  have hpos := goodInInterval_pos_of_lt ha hab hb hn1 hfib 0
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hpos.ne'
  rw [goodInInterval] at hy
  obtain ⟨w, hwmem, -⟩ := Set.mem_iUnion₂.1 hy
  obtain ⟨hwgen, hwsub⟩ := hwmem
  obtain ⟨hwlen, hwpos⟩ := hwgen
  refine ⟨w, ?_, hwpos, hwsub⟩
  intro h; rw [h] at hwlen; simp at hwlen; omega

/-- **Interval-relativized frequency engine.**  Given a nondegenerate
subinterval `(a,b)` of `(0,1)`, a finite family `F`, and `δ > 0`, there is a
genuine "placement" word `w` with `cfCylinder w ⊆ (a,b)` such that beyond a
length threshold every long block `u` appended to `w` can be chosen
frequency-good (matching `γ(I_v)` to within `δ` for all `v ∈ F`) with an
irrational witness point of `cfCylinder (w ++ u)` inside `(a,b)`.  Composes the
placement primitive (`exists_cfCylinder_subset_Ioo`) with the daryCell-free
engine (`exists_freq_good_block`): the placement word is the schedule's per-stage
"filler" (bounded, chosen once to enter `(a,b)`), the block `u` its
frequency-good payload (taken arbitrarily long, so the filler is asymptotically
negligible in the per-stream telescoping). -/
theorem exists_freq_good_block_in_Ioo (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ w : List ℕ, w ≠ [] ∧ (∀ c ∈ w, 1 ≤ c) ∧ cfCylinder w ⊆ Set.Ioo a b ∧
      ∃ N : ℕ, ∀ n, N ≤ n → 0 < n → ∃ u : List ℕ,
        u ≠ [] ∧ u.length = n ∧ (∀ c ∈ u, 1 ≤ c) ∧
        (∀ v ∈ F, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
        (∃ x : ℝ, x ∈ cfCylinder (w ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo a b) := by
  obtain ⟨w, hwne, hwpos, hwsub⟩ := exists_cfCylinder_subset_Ioo ha hab hb
  obtain ⟨N, hN⟩ := exists_freq_good_block w hwne hwpos F hF hFne hδ
  refine ⟨w, hwne, hwpos, hwsub, N, fun n hn hn0 => ?_⟩
  obtain ⟨u, hune, hulen, hupos, hfreq, x, hxu, hxirr⟩ := hN n hn hn0
  exact ⟨u, hune, hulen, hupos, hfreq,
    x, hxu, hxirr, hwsub (cfCylinder_append_subset _ _ hxu)⟩

/-- **Obligation (A), general form.**  A point lying in every member of an
extending chain of genuine CF words is irrational and in `(0,1)`.  The chain
pins a unique point (`eq_of_mem_cfCylinder_chain`), and that point equals the
irrational the limit lemma supplies (`exists_irrational_mem_iInter_cfCylinder`),
so the given point inherits both properties.  Applied to `x`'s own word chain
this gives `Irrational x ∧ x ∈ (0,1)`; applied to the `ψ`-word chain (with
`ψ(x)` in each `ψ`-cylinder, from the interleaved construction) it gives the
`(A)`-side conclusion `Irrational (ψ x) ∧ ψ x ∈ (0,1)`. -/
theorem irrational_mem_Ioo_of_mem_iInter_cfCylinder
    (w : ℕ → List ℕ) (hne : ∀ s, w s ≠ [])
    (hpos : ∀ s, ∀ a ∈ w s, 1 ≤ a)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    {y : ℝ} (hy : ∀ s, y ∈ cfCylinder (w s)) :
    Irrational y ∧ y ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ξ, hξirr, hξmem⟩ :=
    exists_irrational_mem_iInter_cfCylinder w hne hpos hext
  have hyξ : y = ξ := eq_of_mem_cfCylinder_chain hne hpos hext hy hξmem
  subst hyξ
  exact ⟨hξirr, cfCylinder_subset_Ioo _ (hy 0)⟩

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
