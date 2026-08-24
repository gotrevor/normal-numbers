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

/-- Every genuine CF cylinder contains an irrational point (build the trivial
one-extending-chain `w ++ 1ⁿ` and take its limit point). -/
theorem exists_irrational_mem_cfCylinder (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : ∃ x : ℝ, Irrational x ∧ x ∈ cfCylinder w := by
  set c : ℕ → List ℕ := fun s => w ++ List.replicate s 1 with hc
  have hcne : ∀ s, c s ≠ [] := fun s => by simp [hc, hw]
  have hcpos : ∀ s, ∀ a ∈ c s, 1 ≤ a := by
    intro s a ha
    rcases List.mem_append.1 ha with h | h
    · exact hpos a h
    · rw [List.eq_of_mem_replicate h]
  have hext : ∀ s, ∃ u, u ≠ [] ∧ c (s + 1) = c s ++ u := by
    intro s
    exact ⟨[1], by simp, by simp [hc, List.replicate_succ', List.append_assoc]⟩
  obtain ⟨x, hxirr, hxmem⟩ :=
    exists_irrational_mem_iInter_cfCylinder c hcne hcpos hext
  exact ⟨x, hxirr, by have h := hxmem 0; simpa [hc] using h⟩

/-- **A cylinder is an interval, for irrationals.**  A genuine CF cylinder
`cfCylinder w` contains all irrationals of a fixed nondegenerate open interval
`(a,b) ⊆ (0,1)` (its convergent-endpoint interval, clamped to `(0,1)`).  This is
the form the schedule feeds to `exists_freq_good_block_in_Ioo`: refining inside
`cfCylinder w` = refining inside `(a,b)`. -/
theorem exists_Ioo_irrational_subset_cfCylinder (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ cfCylinder w ⊆ Set.Icc a b ∧
      ∀ x ∈ Set.Ioo a b, Irrational x → x ∈ cfCylinder w := by
  obtain ⟨ξ, hξirr, hξmem⟩ := exists_irrational_mem_cfCylinder w hw hpos
  obtain ⟨P, P', -, hIcc, hUIoo⟩ := cfCylinder_endpoints w hw hpos
  set E0 : ℝ := (P : ℝ) / (cfK w : ℝ) with hE0
  set E1 : ℝ := (P' : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) with hE1
  have hE0mem : E0 ∈ Set.range ((↑) : ℚ → ℝ) :=
    ⟨(P : ℚ) / (cfK w : ℚ), by rw [hE0]; push_cast; ring⟩
  have hE1mem : E1 ∈ Set.range ((↑) : ℚ → ℝ) :=
    ⟨(P' : ℚ) / ((cfK w : ℚ) + (cfK w.dropLast : ℚ)), by rw [hE1]; push_cast; ring⟩
  have hne0 : ξ ≠ E0 := fun h => hξirr (by rw [h]; exact hE0mem)
  have hne1 : ξ ≠ E1 := fun h => hξirr (by rw [h]; exact hE1mem)
  have hξIcc : ξ ∈ Set.Icc (min E0 E1) (max E0 E1) := hIcc hξmem
  rw [Set.mem_Icc] at hξIcc
  have hξ01 := hξmem.1
  have hnemin : ξ ≠ min E0 E1 := by
    rcases min_choice E0 E1 with h | h <;> rw [h] <;> [exact hne0; exact hne1]
  have hnemax : ξ ≠ max E0 E1 := by
    rcases max_choice E0 E1 with h | h <;> rw [h] <;> [exact hne0; exact hne1]
  have hminlt : min E0 E1 < ξ := lt_of_le_of_ne hξIcc.1 (Ne.symm hnemin)
  have hltmax : ξ < max E0 E1 := lt_of_le_of_ne hξIcc.2 hnemax
  refine ⟨max (min E0 E1) 0, min (max E0 E1) 1, le_max_right _ _, ?_,
    min_le_right _ _, ?_, ?_⟩
  · have h1 : max (min E0 E1) 0 < ξ := max_lt hminlt hξ01.1
    have h2 : ξ < min (max E0 E1) 1 := lt_min hltmax hξ01.2
    linarith
  · intro x hxc
    have hxIcc := Set.mem_Icc.1 (hIcc hxc)
    have hx01 := Set.mem_Ioo.1 hxc.1
    exact Set.mem_Icc.2 ⟨max_le hxIcc.1 hx01.1.le, le_min hxIcc.2 hx01.2.le⟩
  · intro x hx hirr
    have hxlo : min E0 E1 < x := lt_of_le_of_lt (le_max_left _ _) hx.1
    have hxhi : x < max E0 E1 := lt_of_lt_of_le hx.2 (min_le_left _ _)
    exact hUIoo x (Set.mem_Ioo.2 ⟨hxlo, hxhi⟩) hirr

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

/-- **One schedule stage (single stream).**  Given the current genuine word
`wx`, a pattern family `F`, tolerance `δ > 0`, and a length target `L`, there is
a strict genuine EXTENSION `wx'` of `wx` (i.e. `wx'.take |wx| = wx`, `|wx| <
|wx'|`, `L ≤ |wx'|`) with `cfCylinder wx' ⊆ cfCylinder wx`, split as `wx' = w ++
u` where the tail block `u` is `F`-frequency-good.  This is the atomic refinement
the interleaved schedule performs at each x-stage (and, via the affine image
interval, each ψ-stage): it advances the stream's CF digits by a frequency-good
block while keeping the running cylinder nested and reaching any prescribed
depth.  Composes `exists_Ioo_irrational_subset_cfCylinder` (view `cfCylinder wx`
as an interval) with `exists_freq_good_block_in_Ioo` (freq-good block inside it),
and `take_eq_of_mem_cfCylinder` (shared irrational point ⇒ genuine extension). -/
theorem exists_freq_good_extend_cfCylinder (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) (L : ℕ) :
    ∃ wx' : List ℕ, wx' ≠ [] ∧ (∀ a ∈ wx', 1 ≤ a) ∧
      wx'.take wx.length = wx ∧ wx.length < wx'.length ∧ L ≤ wx'.length ∧
      cfCylinder wx' ⊆ cfCylinder wx ∧
      ∃ w u : List ℕ, wx' = w ++ u ∧
        (∀ v ∈ F, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * u.length|
            < δ * u.length + v.length) := by
  obtain ⟨a, b, ha, hab, hb, -, hIoo⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wx hwx hwxpos
  obtain ⟨w, hwne, hwpos, hwsub, N, hN⟩ :=
    exists_freq_good_block_in_Ioo F hF hFne hδ ha hab hb
  set n := max (max N L) wx.length + 1 with hndef
  have hNn : N ≤ n := by
    rw [hndef]
    exact le_trans (le_trans (le_max_left N L) (le_max_left _ _)) (Nat.le_succ _)
  have hLn : L ≤ n := by
    rw [hndef]
    exact le_trans (le_trans (le_max_right N L) (le_max_left _ _)) (Nat.le_succ _)
  have hnwx : wx.length < n := by
    rw [hndef]; exact Nat.lt_succ_of_le (le_max_right _ _)
  have hn0 : 0 < n := by omega
  obtain ⟨u, hune, hulen, hupos, hfreq, x, hxu, hxirr, hxab⟩ := hN n hNn hn0
  set wx' := w ++ u with hwx'
  have hwx'ne : wx' ≠ [] := by simp [hwx', hune]
  have hwx'pos : ∀ c ∈ wx', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwpos c) (hupos c)
  have hwx'len : wx'.length = w.length + n := by
    rw [hwx', List.length_append, hulen]
  have hgtwx : wx.length < wx'.length := by rw [hwx'len]; omega
  have hgeL : L ≤ wx'.length := by rw [hwx'len]; omega
  have hxwx : x ∈ cfCylinder wx := hIoo x hxab hxirr
  have hxwx' : x ∈ cfCylinder wx' := hxu
  have htake : wx'.take wx.length = wx :=
    take_eq_of_mem_cfCylinder (le_of_lt hgtwx) hxwx hxwx'
  have hsplit : wx' = wx ++ wx'.drop wx.length := by
    conv_lhs => rw [← List.take_append_drop wx.length wx']
    rw [htake]
  have hsub : cfCylinder wx' ⊆ cfCylinder wx := by
    rw [hsplit]; exact cfCylinder_append_subset wx (wx'.drop wx.length)
  refine ⟨wx', hwx'ne, hwx'pos, htake, hgtwx, hgeL, hsub, w, u, hwx', ?_⟩
  intro v hv
  have hf := hfreq v hv
  rwa [hulen]

/-- **ψ-image inclusion (the analytic step of the ψ-stage).**  If the invariant
`cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)` holds, `(a,b)` is an `x`-interval all of
whose irrationals lie in `cfCylinder wx`, and `cfCylinder wz ⊆ [e,f]`, then the
`ψ`-image of `(a,b)` lands in `[e,f]`.  Proof: were some `ψ`-image below `e`
(resp. above `f`), an irrational point of `(a,b)` slightly further out would map
strictly below `e` (above `f`), yet it lies in `cfCylinder wx`, so its image lies
in `cfCylinder wz ⊆ [e,f]` — contradiction.  (Irrational density via
`exists_irrational_btwn`; no `ψ`-irrationality transfer needed.)  Consequence
used by the ψ-stage: since `[e,f]`'s endpoints are the rational convergent
endpoints of `wz`, every IRRATIONAL point of the open image `ψ((a,b))` lands in
`cfCylinder wz`. -/
theorem affine_image_Ioo_subset_Icc {q : ℝ} (hq : 0 < q) (r : ℝ)
    {wx wz : List ℕ} (hinv : cfCylinder wx ⊆ affineMap q r ⁻¹' cfCylinder wz)
    {a b e f : ℝ} (hxint : ∀ x ∈ Set.Ioo a b, Irrational x → x ∈ cfCylinder wx)
    (hzint : cfCylinder wz ⊆ Set.Icc e f) :
    affineMap q r '' Set.Ioo a b ⊆ Set.Icc e f := by
  rw [image_affineMap_Ioo hq]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Set.mem_Ioo.1 hy
  have hax : a < (y - r) / q := (lt_div_iff₀ hq).mpr (by rw [mul_comm]; linarith)
  have hxb : (y - r) / q < b := (div_lt_iff₀ hq).mpr (by rw [mul_comm]; linarith)
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt          -- y < e
    obtain ⟨x', hx'irr, hax', hx'x⟩ := exists_irrational_btwn hax
    have hx'b : x' < b := lt_trans hx'x hxb
    have hψmem : affineMap q r x' ∈ cfCylinder wz :=
      hinv (hxint x' (Set.mem_Ioo.2 ⟨hax', hx'b⟩) hx'irr)
    have hle : e ≤ affineMap q r x' := (hzint hψmem).1
    have hxy : x' * q < y - r := (lt_div_iff₀ hq).mp hx'x
    have hψlt : affineMap q r x' < e := by
      simp only [affineMap]; rw [mul_comm]; linarith
    linarith
  · by_contra hgt
    push_neg at hgt          -- f < y
    obtain ⟨x', hx'irr, hx'lo, hx'hi⟩ := exists_irrational_btwn hxb
    have hax' : a < x' := lt_trans hax hx'lo
    have hψmem : affineMap q r x' ∈ cfCylinder wz :=
      hinv (hxint x' (Set.mem_Ioo.2 ⟨hax', hx'hi⟩) hx'irr)
    have hge : affineMap q r x' ≤ f := (hzint hψmem).2
    have hyx : y - r < x' * q := (div_lt_iff₀ hq).mp hx'lo
    have hψgt : f < affineMap q r x' := by
      simp only [affineMap]; rw [mul_comm]; linarith
    linarith

/-- **Cylinder inside an intersection of two intervals.**  If the open
intersection `(max a c, min b d)` is a nondegenerate subinterval of `(0,1)`, it
contains a genuine CF cylinder, which therefore lies in BOTH `(a,b)` and `(c,d)`.
The ψ-stage uses this to place `x` inside `cfCylinder wx`'s interval AND the
`ψ`-preimage of a good `z`-cylinder simultaneously. -/
theorem exists_cfCylinder_subset_Ioo_inter {a b c d : ℝ}
    (h0 : 0 ≤ max a c) (hlt : max a c < min b d) (h1 : min b d ≤ 1) :
    ∃ w : List ℕ, w ≠ [] ∧ (∀ e ∈ w, 1 ≤ e) ∧
      cfCylinder w ⊆ Set.Ioo a b ∩ Set.Ioo c d := by
  obtain ⟨w, hne, hpos, hsub⟩ := exists_cfCylinder_subset_Ioo h0 hlt h1
  refine ⟨w, hne, hpos, fun x hx => ?_⟩
  have hxm := Set.mem_Ioo.1 (hsub hx)
  exact ⟨Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_left _ _) hxm.1,
      lt_of_lt_of_le hxm.2 (min_le_left _ _)⟩,
    Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_right _ _) hxm.1,
      lt_of_lt_of_le hxm.2 (min_le_right _ _)⟩⟩

/-- **ψ-stage x-selection primitive.**  For `q > 0` and a target `z`-interval
`(c,d)` whose `ψ`-preimage lands in `(0,1)`, there is a genuine `x`-cylinder
inside `ψ⁻¹(c,d)`.  Immediate from `preimage_affineMap_Ioo` (the preimage IS the
open interval `((c−r)/q,(d−r)/q)`) + `exists_cfCylinder_subset_Ioo`.  In the
interleaved schedule's ψ-stage this places `x` so that `ψ(x)` enters a prescribed
good `z`-cylinder: pick the target `(c,d)` to be a good `ψ`-cylinder's interval,
then any point of the returned `x`-cylinder has `ψ`-image in `(c,d)`. -/
theorem exists_cfCylinder_subset_affine_preimage {q : ℝ} (hq : 0 < q) (r c d : ℝ)
    (h0 : 0 ≤ (c - r) / q) (hlt : (c - r) / q < (d - r) / q) (h1 : (d - r) / q ≤ 1) :
    ∃ w : List ℕ, w ≠ [] ∧ (∀ e ∈ w, 1 ≤ e) ∧
      cfCylinder w ⊆ affineMap q r ⁻¹' Set.Ioo c d := by
  rw [preimage_affineMap_Ioo hq]
  exact exists_cfCylinder_subset_Ioo h0 hlt h1

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
