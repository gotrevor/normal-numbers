/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFAffine
import NormalNumbers.CFOrbitFreq
import NormalNumbers.CFFreqBlock
import NormalNumbers.CFChainFreq

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

/-- **Chain cylinders shrink to zero.**  Along a strictly extending genuine word
chain the cylinder volumes tend to `0` (volume `≤ 1/fib(|w_s|+1)²` and `|w_s| ≥
s → ∞`).  Feeds `eq_of_mem_iInter_Icc` at the wz-chain: the enclosing Icc's
(from `cfCylinder_subset_Icc_length`) have diameters `= volume → 0`. -/
theorem cfCylinder_chain_volume_tendsto {w : ℕ → List ℕ}
    (hne : ∀ s, w s ≠ []) (hpos : ∀ s, ∀ a ∈ w s, 1 ≤ a)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) :
    Filter.Tendsto (fun s => (volume (cfCylinder (w s))).toReal)
      Filter.atTop (nhds 0) := by
  have hself : ∀ n : ℕ, n ≤ Nat.fib (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.fib_add_two]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hfk : 1 ≤ Nat.fib k := Nat.fib_pos.mpr hk
        omega
  have hfib_top : Filter.Tendsto (fun s => (Nat.fib (s + 1) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono (fun s => by exact_mod_cast hself s)
      tendsto_natCast_atTop_atTop
  have hg : Filter.Tendsto (fun s => ((Nat.fib (s + 1) : ℝ))⁻¹)
      Filter.atTop (nhds 0) := hfib_top.inv_tendsto_atTop
  refine squeeze_zero (fun s => ENNReal.toReal_nonneg) (fun s => ?_) hg
  have hb := volume_cfCylinder_le_fib (w s) (hne s) (hpos s)
  have h1 : (volume (cfCylinder (w s))).toReal
      ≤ 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2 := by
    calc (volume (cfCylinder (w s))).toReal
        ≤ (ENNReal.ofReal (1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2 :=
          ENNReal.toReal_ofReal (by positivity)
  have hlen : s + 1 ≤ (w s).length + 1 := by
    have := le_length_of_extending w hext s; omega
  have hfibmono : (Nat.fib (s + 1) : ℝ) ≤ (Nat.fib ((w s).length + 1) : ℝ) := by
    exact_mod_cast Nat.fib_mono hlen
  have hpos1 : (0 : ℝ) < (Nat.fib (s + 1) : ℝ) ^ 2 := by
    have : 0 < Nat.fib (s + 1) := Nat.fib_pos.2 (by omega); positivity
  have hfibpos1 : (0 : ℝ) < (Nat.fib (s + 1) : ℝ) := by
    have : 0 < Nat.fib (s + 1) := Nat.fib_pos.2 (by omega); exact_mod_cast this
  have hfibge1 : (1 : ℝ) ≤ (Nat.fib (s + 1) : ℝ) := by
    have : 1 ≤ Nat.fib (s + 1) := Nat.fib_pos.2 (by omega); exact_mod_cast this
  have hmono : 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2
      ≤ ((Nat.fib (s + 1) : ℝ))⁻¹ := by
    rw [← one_div]
    calc 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2
        ≤ 1 / (Nat.fib (s + 1) : ℝ) ^ 2 :=
          one_div_le_one_div_of_le hpos1 (by nlinarith [hfibmono, hpos1])
      _ ≤ 1 / (Nat.fib (s + 1) : ℝ) :=
          one_div_le_one_div_of_le hfibpos1 (by nlinarith [hfibge1])
  exact le_trans h1 hmono

/-- **Squeeze to a point.**  Two reals in every member of a sequence of closed
intervals whose diameters tend to `0` are equal.  The abstract nesting-uniqueness
the schedule uses: at the limit, `ψ(xA)` and the wz-chain's irrational point both
lie in every `wz_t` convergent-endpoint interval (diameters `1/(K(K+K')) → 0`),
so they coincide — hence `ψ(xA)` inherits that point's irrationality and its
membership in every `cfCylinder wz_t`, dodging `ψ`'s non-preservation of
irrationality. -/
theorem eq_of_mem_iInter_Icc {lo hi : ℕ → ℝ}
    (hdiam : Filter.Tendsto (fun s => hi s - lo s) Filter.atTop (nhds 0))
    {y z : ℝ} (hy : ∀ s, y ∈ Set.Icc (lo s) (hi s))
    (hz : ∀ s, z ∈ Set.Icc (lo s) (hi s)) : y = z := by
  have hle : ∀ s, |y - z| ≤ hi s - lo s := by
    intro s
    obtain ⟨hy1, hy2⟩ := hy s
    obtain ⟨hz1, hz2⟩ := hz s
    rw [abs_sub_le_iff]; exact ⟨by linarith, by linarith⟩
  have hz0 : |y - z| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hdiam hle
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz0 (abs_nonneg _)))

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

/-- **ψ-image inclusion, INTERVAL-preimage form (the establishable invariant).**
Same conclusion as `affine_image_Ioo_subset_Icc`, but the hypothesis is the
INTERVAL-preimage invariant `cfCylinder wx ⊆ ψ⁻¹(Icc e f)` — the one the
interleaved schedule can actually MAINTAIN (lap 19 obstruction: the set invariant
`⊆ ψ⁻¹(cfCylinder wz)` is unestablishable because ψ need not preserve
irrationality; `exists_cfCylinder_subset_affine_preimage` only ever delivers
`⊆ ψ⁻¹(Ioo …)`).  Proof is the two `exists_irrational_btwn` contradiction blocks,
now landing an out-of-range image directly in `Icc e f` via `hinv` (no wz
cylinder hop). -/
theorem affine_image_Ioo_subset_Icc_pre {q : ℝ} (hq : 0 < q) (r : ℝ)
    {wx : List ℕ} {a b e f : ℝ}
    (hinv : cfCylinder wx ⊆ affineMap q r ⁻¹' Set.Icc e f)
    (hxint : ∀ x ∈ Set.Ioo a b, Irrational x → x ∈ cfCylinder wx) :
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
    have hle : e ≤ affineMap q r x' :=
      (hinv (hxint x' (Set.mem_Ioo.2 ⟨hax', hx'b⟩) hx'irr)).1
    have hxy : x' * q < y - r := (lt_div_iff₀ hq).mp hx'x
    have hψlt : affineMap q r x' < e := by
      simp only [affineMap]; rw [mul_comm]; linarith
    linarith
  · by_contra hgt
    push_neg at hgt          -- f < y
    obtain ⟨x', hx'irr, hx'lo, hx'hi⟩ := exists_irrational_btwn hxb
    have hax' : a < x' := lt_trans hax hx'lo
    have hge : affineMap q r x' ≤ f :=
      (hinv (hxint x' (Set.mem_Ioo.2 ⟨hax', hx'hi⟩) hx'irr)).2
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

/-- **THE ψ-ROUND STEP (interleaved schedule).**  One joint round maintaining the
interval invariant `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)`.  Given genuine `wx, wz`, the
wz-interval `(e,f)` (`irr(e,f) ⊆ cfCylinder wz`) and the invariant, plus a family
`F`, tolerance `δ`, depth `L`, produce strict freq-good extensions `wz'` (of `wz`)
and `wx'` (of `wx`), a new wz-interval `(e',f')`, and the new invariant
`cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')`.  This is the novel geometric heart of B6: it
threads the affine map through one refinement while keeping BOTH streams' CF
digits advancing by a freq-good block.  Recipe: image bounds via
`affine_image_Ioo_subset_Icc_pre` ⇒ place a good `z`-block in `ψ((a,b))` ⇒ its
interval pulls back to overlap `(a,b)` ⇒ place a good `x`-block in the overlap.
The freq-good blocks (`uz`, `ux`) are exposed for the per-stream telescoping. -/
theorem exists_freq_good_extend_affine {q : ℝ} (hq : 0 < q) (r : ℝ)
    (wx wz : List ℕ) (hwx : wx ≠ []) (hwxpos : ∀ c ∈ wx, 1 ≤ c)
    (hwz : wz ≠ []) (hwzpos : ∀ c ∈ wz, 1 ≤ c)
    {e f : ℝ} (he0 : 0 ≤ e) (hef : e < f) (hf1 : f ≤ 1)
    (hzint : ∀ x ∈ Set.Ioo e f, Irrational x → x ∈ cfCylinder wz)
    (hinv : cfCylinder wx ⊆ affineMap q r ⁻¹' Set.Ioo e f)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) (L : ℕ) :
    ∃ wx' wz' : List ℕ, ∃ e' f' : ℝ,
      (wz' ≠ [] ∧ (∀ c ∈ wz', 1 ≤ c) ∧ wz'.take wz.length = wz ∧
        wz.length < wz'.length ∧ L ≤ wz'.length ∧ cfCylinder wz' ⊆ cfCylinder wz ∧
        ∃ wp u : List ℕ, wz' = wp ++ u ∧ L ≤ u.length ∧
          (∀ v ∈ F, |(countOccurrences v u : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length)) ∧
      (wx' ≠ [] ∧ (∀ c ∈ wx', 1 ≤ c) ∧ wx'.take wx.length = wx ∧
        wx.length < wx'.length ∧ L ≤ wx'.length ∧ cfCylinder wx' ⊆ cfCylinder wx ∧
        ∃ wp u : List ℕ, wx' = wp ++ u ∧ L ≤ u.length ∧
          (∀ v ∈ F, |(countOccurrences v u : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length)) ∧
      (0 ≤ e' ∧ e' < f' ∧ f' ≤ 1 ∧
        (∀ x ∈ Set.Ioo e' f', Irrational x → x ∈ cfCylinder wz')) ∧
      cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
  -- (1) wx-interval (a,b)
  obtain ⟨a, b, ha, hab, hb, hxIcc, hxint⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wx hwx hwxpos
  -- (2) image bounds: ψ((a,b)) = Ioo(qa+r)(qb+r) ⊆ Icc e f
  have hinvIcc : cfCylinder wx ⊆ affineMap q r ⁻¹' Set.Icc e f :=
    fun x hx => Set.Ioo_subset_Icc_self (hinv hx)
  have himg : Set.Ioo (q * a + r) (q * b + r) ⊆ Set.Icc e f := by
    have h := affine_image_Ioo_subset_Icc_pre hq r hinvIcc hxint
    rwa [image_affineMap_Ioo hq] at h
  have huv : q * a + r < q * b + r := by nlinarith
  have hcl : Set.Icc (q * a + r) (q * b + r) ⊆ Set.Icc e f := by
    rw [← closure_Ioo (ne_of_lt huv)]
    exact isClosed_Icc.closure_subset_iff.mpr himg
  obtain ⟨hlo, hhi⟩ := (Set.Icc_subset_Icc_iff huv.le).1 hcl
  -- (3) place a freq-good z-block in J_z = Ioo(qa+r)(qb+r)
  have hJ0 : 0 ≤ q * a + r := le_trans he0 hlo
  have hJ1 : q * b + r ≤ 1 := le_trans hhi hf1
  obtain ⟨wpz, hwpzne, hwpzpos, hwpzsub, Nz, hNz⟩ :=
    exists_freq_good_block_in_Ioo F hF hFne hδ hJ0 huv hJ1
  set nz := max (max Nz L) wz.length + 1 with hnzdef
  have hNznz : Nz ≤ nz := by
    rw [hnzdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hLnz : L ≤ nz := by
    rw [hnzdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hwznz : wz.length < nz := by rw [hnzdef]; exact Nat.lt_succ_of_le (le_max_right _ _)
  obtain ⟨uz, huzne, huzlen, huzpos, huzfreq, pz, hpzmem, hpzirr, hpzab⟩ :=
    hNz nz hNznz (by omega)
  set wz' := wpz ++ uz with hwz'def
  have hwz'ne : wz' ≠ [] := by simp [hwz'def, huzne]
  have hwz'pos : ∀ c ∈ wz', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwpzpos c) (huzpos c)
  have hwz'len : wz'.length = wpz.length + nz := by
    rw [hwz'def, List.length_append, huzlen]
  -- pz ∈ Ioo e f ⇒ pz ∈ cfCylinder wz
  have hpzef : pz ∈ Set.Ioo e f := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hpzab
    exact Set.mem_Ioo.2 ⟨lt_of_le_of_lt hlo h1, lt_of_lt_of_le h2 hhi⟩
  have hpzwz : pz ∈ cfCylinder wz := hzint pz hpzef hpzirr
  have hpzwz' : pz ∈ cfCylinder wz' := hpzmem
  have hzgt : wz.length < wz'.length := by rw [hwz'len]; omega
  have htakez : wz'.take wz.length = wz :=
    take_eq_of_mem_cfCylinder (le_of_lt hzgt) hpzwz hpzwz'
  have hsplitz : wz' = wz ++ wz'.drop wz.length := by
    conv_lhs => rw [← List.take_append_drop wz.length wz']
    rw [htakez]
  have hsubz : cfCylinder wz' ⊆ cfCylinder wz := by
    rw [hsplitz]; exact cfCylinder_append_subset wz (wz'.drop wz.length)
  have hzL : L ≤ wz'.length := by rw [hwz'len]; omega
  -- (4) wz'-interval (e',f')
  obtain ⟨e', f', he'0, he'f', hf'1, hz'Icc, hz'int⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wz' hwz'ne hwz'pos
  -- (5) place a freq-good x-block in (a,b) ∩ ψ⁻¹(Ioo e' f')
  -- base mult facts about the shared point x₀ = (pz - r)/q
  have hax₀ : a * q < pz - r := by nlinarith [(Set.mem_Ioo.1 hpzab).1]
  have hx₀b : pz - r < b * q := by nlinarith [(Set.mem_Ioo.1 hpzab).2]
  have hpzIcc : pz ∈ Set.Icc e' f' := hz'Icc hpzmem
  have he'pz : e' ≤ pz := hpzIcc.1
  have hpzf' : pz ≤ f' := hpzIcc.2
  set a' := (e' - r) / q with ha'def
  set b' := (f' - r) / q with hb'def
  have ha'b : a' < b := (div_lt_iff₀ hq).mpr (by rw [ha'def] at *; nlinarith)
  have hab' : a < b' := (lt_div_iff₀ hq).mpr (by nlinarith)
  have ha'b' : a' < b' := by
    rw [ha'def, hb'def]
    gcongr
  have hmax : max a a' < min b b' :=
    max_lt (lt_min hab hab') (lt_min ha'b ha'b')
  have hm0 : 0 ≤ max a a' := le_trans ha (le_max_left _ _)
  have hm1 : min b b' ≤ 1 := le_trans (min_le_left _ _) hb
  obtain ⟨wpx, hwpxne, hwpxpos, hwpxsub, Nx, hNx⟩ :=
    exists_freq_good_block_in_Ioo F hF hFne hδ hm0 hmax hm1
  set nx := max (max Nx L) wx.length + 1 with hnxdef
  have hNxnx : Nx ≤ nx := by
    rw [hnxdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hLnx : L ≤ nx := by
    rw [hnxdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hwxnx : wx.length < nx := by rw [hnxdef]; exact Nat.lt_succ_of_le (le_max_right _ _)
  obtain ⟨ux, huxne, huxlen, huxpos, huxfreq, px, hpxmem, hpxirr, hpxab⟩ :=
    hNx nx hNxnx (by omega)
  set wx' := wpx ++ ux with hwx'def
  have hwx'ne : wx' ≠ [] := by simp [hwx'def, huxne]
  have hwx'pos : ∀ c ∈ wx', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwpxpos c) (huxpos c)
  have hwx'len : wx'.length = wpx.length + nx := by
    rw [hwx'def, List.length_append, huxlen]
  -- px ∈ Ioo a b ⇒ px ∈ cfCylinder wx
  have hpxab' : px ∈ Set.Ioo a b := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hpxab
    exact Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_left _ _) h1,
      lt_of_lt_of_le h2 (min_le_left _ _)⟩
  have hpxwx : px ∈ cfCylinder wx := hxint px hpxab' hpxirr
  have hpxwx' : px ∈ cfCylinder wx' := hpxmem
  have hxgt : wx.length < wx'.length := by rw [hwx'len]; omega
  have htakex : wx'.take wx.length = wx :=
    take_eq_of_mem_cfCylinder (le_of_lt hxgt) hpxwx hpxwx'
  have hsplitx : wx' = wx ++ wx'.drop wx.length := by
    conv_lhs => rw [← List.take_append_drop wx.length wx']
    rw [htakex]
  have hsubx : cfCylinder wx' ⊆ cfCylinder wx := by
    rw [hsplitx]; exact cfCylinder_append_subset wx (wx'.drop wx.length)
  have hxL : L ≤ wx'.length := by rw [hwx'len]; omega
  -- new invariant: cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')
  have hinv' : cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
    rw [preimage_affineMap_Ioo hq]
    intro x hx
    have hx1 : x ∈ cfCylinder wpx := by
      rw [hwx'def] at hx; exact cfCylinder_append_subset wpx ux hx
    have hx2 := hwpxsub hx1
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hx2
    exact Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_right _ _) h1,
      lt_of_lt_of_le h2 (min_le_right _ _)⟩
  -- assemble
  refine ⟨wx', wz', e', f', ⟨hwz'ne, hwz'pos, htakez, hzgt, hzL, hsubz,
    wpz, uz, hwz'def, ?_, ?_⟩, ⟨hwx'ne, hwx'pos, htakex, hxgt, hxL, hsubx,
    wpx, ux, hwx'def, ?_, ?_⟩, ⟨he'0, he'f', hf'1, hz'int⟩, hinv'⟩
  · rw [huzlen]; omega
  · intro v hv; have := huzfreq v hv; rwa [huzlen]
  · rw [huxlen]; omega
  · intro v hv; have := huxfreq v hv; rwa [huxlen]

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
