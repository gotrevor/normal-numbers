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

open MeasureTheory Filter Asymptotics

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

/-- **L4 route — ψ-pullback Gauss distortion bound (route-decisive first brick).**
For `q > 0` and a measurable `S ⊆ (0,1)`, the affine pullback `ψ⁻¹ = (q·+r)⁻¹`
scales `gaussMeasure` by at most `2/q`:  `γ(ψ⁻¹ S) ≤ (2/q)·γ(S)`.  Assembled from
the upper Gauss/Lebesgue comparison `gaussMeasure_le_volume` (density `≤ (log2)⁻¹`),
the EXACT Lebesgue pullback `volume_preimage_affineMap` (`vol(ψ⁻¹ S)=|q⁻¹|·vol S`),
and the lower comparison `volume_le_ofReal_mul_gaussMeasure` (`vol S ≤ (2 log2)·γ(S)`
on `(0,1)`); the two `log 2` factors cancel.  This is the foundational measure
lemma of the single-stream L4 route (`PENDING_WORK.md` top): an image-space bad set
of small `γ`-mass pulls back to a small `γ`-mass in `x`-space, so `ψ(x)`'s CF
frequency can be controlled STATISTICALLY (via `x` avoiding `ψ⁻¹(z-bad-zones)`)
without nesting a `z`-cylinder — killing the two-stream super-exponential blowup. -/
theorem gaussMeasure_preimage_affineMap_le {q : ℝ} (hq : 0 < q) (r : ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo (0 : ℝ) 1) :
    gaussMeasure (affineMap q r ⁻¹' S)
      ≤ ENNReal.ofReal (2 / q) * gaussMeasure S := by
  have hcont : Continuous (affineMap q r) := by unfold affineMap; fun_prop
  have hmeas : MeasurableSet (affineMap q r ⁻¹' S) := hS.preimage hcont.measurable
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hq0 : q ≠ 0 := ne_of_gt hq
  calc gaussMeasure (affineMap q r ⁻¹' S)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume (affineMap q r ⁻¹' S) :=
        gaussMeasure_le_volume _ hmeas
    _ = ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal |q⁻¹| * volume S) := by
        rw [volume_preimage_affineMap hq0]
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal |q⁻¹| *
          (ENNReal.ofReal (2 * Real.log 2) * gaussMeasure S)) := by
        gcongr
        exact volume_le_ofReal_mul_gaussMeasure _ hS hSsub
    _ = ENNReal.ofReal (2 / q) * gaussMeasure S := by
        have hloginv : (0 : ℝ) ≤ (Real.log 2)⁻¹ :=
          inv_nonneg.mpr (Real.log_nonneg (by norm_num))
        have hconst : ENNReal.ofReal (Real.log 2)⁻¹ * ENNReal.ofReal |q⁻¹| *
            ENNReal.ofReal (2 * Real.log 2) = ENNReal.ofReal (2 / q) := by
          rw [abs_of_pos (inv_pos.mpr hq), ← ENNReal.ofReal_mul hloginv,
            ← ENNReal.ofReal_mul (mul_nonneg hloginv (inv_nonneg.mpr hq.le))]
          congr 1
          field_simp
        rw [← mul_assoc, ← mul_assoc, hconst]

/-- **Multi-scale aggregate bad-zone measure bound.**  The union of the CF
discrepancy bad zones over a finite family `F` of patterns AND a finite set `NS`
of scales (all `≥ n₁`) has `γ`-measure `≤ |NS| · (S/(δ²·n₁)) · γ(I_w)`, where `S`
is the pattern constant.  Summing `gaussMeasure_aggregate_cfBadZone_le` over the
scales (each `≤` the `n₁` term since `n ≥ n₁`).  This is the enabling measure
bound for uniformly-prefix-good steer blocks: `Σ 1/nⱼ` over quadratically-spaced
scales stays bounded (`≤ |NS|/n₁`), so avoiding bad zones at ALL scales
simultaneously costs bounded measure. -/
theorem gaussMeasure_multiscale_cfBadZone_le
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (NS : Finset ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁)
    (hNS : ∀ n ∈ NS, n₁ ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone w v n δ)).toReal
      ≤ (NS.card : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
          * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
          * (gaussMeasure (cfCylinder w)).toReal)) := by
  set A₁ : ℝ := ∑ v ∈ F, 7 * ((8 * v.length + 80)
      * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
      * (gaussMeasure (cfCylinder w)).toReal with hA₁
  have hstep : (gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone w v n δ)).toReal
      ≤ ∑ n ∈ NS, (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal := by
    calc (gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone w v n δ)).toReal
        ≤ (∑ n ∈ NS, gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal := by
          refine ENNReal.toReal_mono ?_ (measure_biUnion_finset_le NS _)
          exact (ENNReal.sum_lt_top.2 (fun n _ => measure_lt_top _ _)).ne
      _ = ∑ n ∈ NS, (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal :=
          ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)
  have hterm : ∀ n ∈ NS, (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal ≤ A₁ := by
    intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le hn₁ (hNS n hn)
    have hagg := gaussMeasure_aggregate_cfBadZone_le w hposw F hF n hn0 hδ
    refine le_trans hagg ?_
    rw [hA₁]
    refine Finset.sum_le_sum fun v hv => ?_
    have hγv : (0 : ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have hγw : (0 : ℝ) ≤ (gaussMeasure (cfCylinder w)).toReal := ENNReal.toReal_nonneg
    have hpref : (0 : ℝ) ≤ 8 * v.length + 80 := by positivity
    have hden : (0 : ℝ) < δ ^ 2 * n := by
      have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
      positivity
    have hden1 : (0 : ℝ) < δ ^ 2 * n₁ := by
      have : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
      positivity
    have hle : ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n))
        ≤ ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁)) := by
      apply div_le_div_of_nonneg_left ?_ hden1
      · gcongr
        · exact_mod_cast (hNS n hn)
      all_goals positivity
    gcongr
  calc (gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone w v n δ)).toReal
      ≤ ∑ n ∈ NS, (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal := hstep
    _ ≤ ∑ _n ∈ NS, A₁ := Finset.sum_le_sum hterm
    _ = (NS.card : ℝ) * A₁ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **L4 route — brick 2a: ψ-pullback of a z-cylinder-based multiscale bad zone.**
The `ψ`-preimage of the union of `z`-CF discrepancy bad zones (base `z`-cylinder
`wz`, family `F`, scales `NS`) has `γ`-measure at most `2/q` times the multiscale
bound for `wz`.  Combines brick 1 (`gaussMeasure_preimage_affineMap_le`) with the
`z`-space multiscale bound (`gaussMeasure_multiscale_cfBadZone_le`).  This is the
object the single-stream L4 selection avoids: `x` such that `ψ(x)` has good
`z`-frequency at every scale in `NS` `⟺` `x ∉ ψ⁻¹(z-bad-zones)`.  The bound is
ABSOLUTE (`·γ(cfCylinder wz)`, not relative to `cfCylinder wx`); the alignment
brick (2b) supplies `γ(cfCylinder wz) ≤ C·γ(cfCylinder wx)` so this becomes a small
fraction of the current `x`-cylinder — NO exponential `1/ρ` blowup (that was the
two-stream defect). -/
theorem gaussMeasure_preimage_multiscale_cfBadZone_le {q : ℝ} (hq : 0 < q) (r : ℝ)
    (wz : List ℕ) (hposwz : ∀ a ∈ wz, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (NS : Finset ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁)
    (hNS : ∀ n ∈ NS, n₁ ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone wz v n δ)).toReal
      ≤ (2 / q) * ((NS.card : ℝ) * (∑ v ∈ F, 7 * ((8 * v.length + 80) *
          (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁)) *
          (gaussMeasure (cfCylinder wz)).toReal)) := by
  set B : Set ℝ := ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone wz v n δ with hBdef
  have hpre : (⋃ n ∈ NS, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone wz v n δ)
      = affineMap q r ⁻¹' B := by
    rw [hBdef]; simp only [Set.preimage_iUnion]
  have hBmeas : MeasurableSet B := by
    rw [hBdef]
    exact MeasurableSet.biUnion NS.countable_toSet fun n _ =>
      Finset.measurableSet_biUnion F fun v _ => measurableSet_cfBadZone wz v n δ
  have hBsub : B ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [hBdef]
    refine Set.iUnion₂_subset fun n _ => Set.iUnion₂_subset fun v _ => ?_
    exact Set.inter_subset_left.trans (cfCylinder_subset_Ioo wz)
  have hfin : gaussMeasure B ≠ ⊤ := measure_ne_top _ _
  have h1 : gaussMeasure (affineMap q r ⁻¹' B) ≤ ENNReal.ofReal (2 / q) * gaussMeasure B :=
    gaussMeasure_preimage_affineMap_le hq r B hBmeas hBsub
  have h1r : (gaussMeasure (affineMap q r ⁻¹' B)).toReal
      ≤ (2 / q) * (gaussMeasure B).toReal := by
    calc (gaussMeasure (affineMap q r ⁻¹' B)).toReal
        ≤ (ENNReal.ofReal (2 / q) * gaussMeasure B).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
      _ = (2 / q) * (gaussMeasure B).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h2 : (gaussMeasure B).toReal
      ≤ (NS.card : ℝ) * (∑ v ∈ F, 7 * ((8 * v.length + 80) *
          (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁)) *
          (gaussMeasure (cfCylinder wz)).toReal) :=
    gaussMeasure_multiscale_cfBadZone_le wz hposwz F hF NS hn₁ hNS hδ
  rw [hpre]
  exact h1r.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- **Brick 2b-ii — two-scale split (pointwise).**  Route-B analytic heart.  On a
genuine depth-`d` cylinder `w'` (`d = |w'| < N`), an ABSOLUTE-scale (`base []`)
`v`-bad point at scale `N` is, under its Gauss shift by `d`, a `v`-bad point at
scale `N−d` with the prefix eating only `d/N` of the slack: the tail deviation is
`≥ δ − d/N`.  Pure Birkhoff additivity (`birkhoffSum_add`) — the length-`N` count
is the length-`d` seam count `∈ [0,d]` plus the shifted length-`(N−d)` count, so
the seam contributes `≤ d/N` to the length-`N` average.  No orbit-length
bookkeeping; the only geometric input is `gaussMap^[d] x ∈ (0,1)` (holds off a
null set — supplied by irrationality downstream). -/
theorem cfBadZone_nil_shift_mem_cfBadZone
    (v w' : List ℕ) (N : ℕ) (δ : ℝ) (hdN : w'.length < N)
    {x : ℝ} (hx : x ∈ cfBadZone [] v N δ) (hxc : x ∈ cfCylinder w')
    (horb : gaussMap^[w'.length] x ∈ Set.Ioo (0 : ℝ) 1) :
    x ∈ cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ)) := by
  set d : ℕ := w'.length with hd
  set A : Set ℝ := cfCylinder v with hA
  set γv : ℝ := (gaussMeasure A).toReal with hγ
  -- unpack the base-`[]` bad-zone membership
  simp only [cfBadZone, List.length_nil, Function.iterate_zero, Set.preimage_id,
    Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  obtain ⟨-, hxIoo, hdev⟩ := hx
  -- the two-scale Birkhoff split of the length-`N` count
  have hNsum : d + (N - d) = N := Nat.add_sub_cancel' (le_of_lt hdN)
  set P : ℝ := blockCount A d x with hP
  set T : ℝ := blockCount A (N - d) (gaussMap^[d] x) with hT
  have hsplit : blockCount A N x = P + T := by
    have h := birkhoffSum_add gaussMap (blockIndic A) d (N - d) x
    rw [hNsum] at h
    rw [hP, hT]; exact h
  -- seam bounds: `0 ≤ P ≤ d` and `0 ≤ γv ≤ 1`
  have hind0 : ∀ y : ℝ, 0 ≤ blockIndic A y := by
    intro y; unfold blockIndic
    exact Set.indicator_nonneg (fun _ _ => by norm_num) y
  have hind1 : ∀ y : ℝ, blockIndic A y ≤ 1 := by
    intro y; unfold blockIndic
    by_cases h : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hP0 : 0 ≤ P := by
    rw [hP, blockCount_apply]; exact Finset.sum_nonneg fun k _ => hind0 _
  have hPd : P ≤ (d : ℝ) := by
    rw [hP, blockCount_apply]
    calc ∑ k ∈ Finset.range d, blockIndic A (gaussMap^[k] x)
        ≤ ∑ _k ∈ Finset.range d, (1 : ℝ) := Finset.sum_le_sum fun k _ => hind1 _
      _ = (d : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hγ0 : 0 ≤ γv := ENNReal.toReal_nonneg
  have hγ1 : γv ≤ 1 := by
    rw [hγ]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by simpa using prob_le_one (μ := gaussMeasure) (s := A))
  -- casts and positivity of the two scales
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNd : ((N - d : ℕ) : ℝ) = (N : ℝ) - (d : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hdN)]
  have hNdpos : (0 : ℝ) < (N : ℝ) - (d : ℝ) := by
    rw [← hNd]; exact_mod_cast Nat.sub_pos_of_lt hdN
  -- the identity linking the two averages
  set a : ℝ := T / ((N : ℝ) - (d : ℝ)) - γv with ha
  have hE : blockCount A N x / (N : ℝ) - γv
      = (P / (N : ℝ) - ((d : ℝ) / (N : ℝ)) * γv)
        + (((N : ℝ) - (d : ℝ)) / (N : ℝ)) * a := by
    rw [hsplit, ha]
    field_simp
    ring
  -- triangle-inequality bound on the seam contribution
  have hseam : |P / (N : ℝ) - ((d : ℝ) / (N : ℝ)) * γv| ≤ (d : ℝ) / (N : ℝ) := by
    have heq : P / (N : ℝ) - ((d : ℝ) / (N : ℝ)) * γv = (P - (d : ℝ) * γv) / (N : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    gcongr
    rw [abs_le]
    constructor <;> nlinarith [hP0, hPd, hγ0, hγ1]
  have hcoef : (((N : ℝ) - (d : ℝ)) / (N : ℝ)) ≤ 1 := by
    rw [div_le_one hNpos]; linarith
  have hcoef0 : 0 ≤ ((N : ℝ) - (d : ℝ)) / (N : ℝ) := by positivity
  -- conclude: tail deviation `≥ δ − d/N`
  have hbig : δ ≤ (d : ℝ) / (N : ℝ) + |a| := by
    calc δ ≤ |blockCount A N x / (N : ℝ) - γv| := hdev
      _ = |(P / (N : ℝ) - ((d : ℝ) / (N : ℝ)) * γv)
            + (((N : ℝ) - (d : ℝ)) / (N : ℝ)) * a| := by rw [hE]
      _ ≤ |P / (N : ℝ) - ((d : ℝ) / (N : ℝ)) * γv|
            + |(((N : ℝ) - (d : ℝ)) / (N : ℝ)) * a| := abs_add_le _ _
      _ ≤ (d : ℝ) / (N : ℝ) + |a| := by
          have : |(((N : ℝ) - (d : ℝ)) / (N : ℝ)) * a| ≤ |a| := by
            rw [abs_mul, abs_of_nonneg hcoef0]
            exact mul_le_of_le_one_left (abs_nonneg _) hcoef
          linarith [hseam]
  -- repackage into the target bad zone at scale `N−d`
  refine ⟨hxc, ?_⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ← hd]
  refine ⟨horb, ?_⟩
  have hgoal : δ - (d : ℝ) / (N : ℝ)
      ≤ |blockCount A (N - d) (gaussMap^[d] x) / ((N - d : ℕ) : ℝ) - γv| := by
    rw [hNd, ← hT, ← ha]; linarith [hbig]
  simpa [hA, hγ, hd] using hgoal

/-- **Brick 2b-ii — two-scale split (measure).**  The `γ`-mass of a base-`[]`
`v`-bad zone at scale `N` intersected with a genuine depth-`d` cylinder `w'`
(`d < N`) is bounded by the `γ`-mass of the base-`w'` `v`-bad zone at scale `N−d`
with slack shaved to `δ − d/N`.  Off the (`γ`-null) rationals the pointwise split
`cfBadZone_nil_shift_mem_cfBadZone` applies, using `irrational_orbit` to supply
`gaussMap^[d] x ∈ (0,1)`. -/
theorem gaussMeasure_cfBadZone_nil_inter_cylinder_le
    (v w' : List ℕ) (N : ℕ) (δ : ℝ) (hdN : w'.length < N) :
    gaussMeasure (cfBadZone [] v N δ ∩ cfCylinder w')
      ≤ gaussMeasure (cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ))) := by
  -- `γ`-null rationals
  have hrat0 : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
    have hac : gaussMeasure ≪ volume.restrict (Set.Ioo (0 : ℝ) 1) := by
      rw [gaussMeasure]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    apply hac
    rw [Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null Set.inter_subset_left ((Set.countable_range _).measure_zero _)
  -- a.e. inclusion: irrational bad points shift into the base-`w'` bad zone
  have hsub : cfBadZone [] v N δ ∩ cfCylinder w'
      ⊆ cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ))
        ∪ Set.range ((↑) : ℚ → ℝ) := by
    rintro x ⟨hxbad, hxc⟩
    by_cases hirr : Irrational x
    · left
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo w' hxc
      have horb := (irrational_orbit x hirr hx01 w'.length).2
      exact cfBadZone_nil_shift_mem_cfBadZone v w' N δ hdN hxbad hxc horb
    · right
      rw [Irrational, not_not] at hirr
      exact hirr
  calc gaussMeasure (cfBadZone [] v N δ ∩ cfCylinder w')
      ≤ gaussMeasure (cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ))
          ∪ Set.range ((↑) : ℚ → ℝ)) := measure_mono hsub
    _ ≤ gaussMeasure (cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ)))
          + gaussMeasure (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
    _ = gaussMeasure (cfBadZone w' v (N - w'.length) (δ - (w'.length : ℝ) / (N : ℝ))) := by
        rw [hrat0, add_zero]

/-- `coveredByCyl a b n` is measurable: a countable biUnion of measurable
cylinders. -/
theorem measurableSet_coveredByCyl (a b : ℝ) (n : ℕ) :
    MeasurableSet (coveredByCyl a b n) := by
  rw [coveredByCyl]
  exact MeasurableSet.biUnion
    (Set.Countable.mono (Set.sep_subset _ _)
      (Set.Countable.mono (Set.subset_univ _) Set.countable_univ))
    (fun w _ => measurableSet_cfCylinder w)

/-- **Brick 2b-i (γ-residual, route-B covering).**  The `γ`-mass of the part of
`(a,b)` NOT covered by depth-`n` cylinders fully inside `(a,b)` is `≤
(log 2)⁻¹·4/fib(n+1)²` — the boundary-strip residual, `→ 0` as `n → ∞`.  Pure
`gaussMeasure ≤ (log 2)⁻¹·volume` pushforward of the Lebesgue covering lemma
`volume_interval_sdiff_covered_le` (`CFIntervalGood`); the hard geometry (`≤2`
straddlers, each within `1/fib(n+1)²` of an endpoint) is already discharged
there.  This is the residual term of the 2b-iii assembly. -/
theorem gaussMeasure_interval_sdiff_covered_le (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℕ) :
    gaussMeasure (Set.Ioo a b \ coveredByCyl a b n)
      ≤ ENNReal.ofReal ((Real.log 2)⁻¹ * (4 / (Nat.fib (n + 1) : ℝ) ^ 2)) := by
  have hmeas : MeasurableSet (Set.Ioo a b \ coveredByCyl a b n) :=
    measurableSet_Ioo.diff (measurableSet_coveredByCyl a b n)
  calc gaussMeasure (Set.Ioo a b \ coveredByCyl a b n)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume (Set.Ioo a b \ coveredByCyl a b n) :=
        gaussMeasure_le_volume _ hmeas
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
        gcongr
        exact volume_interval_sdiff_covered_le a b ha hab hb n
    _ = ENNReal.ofReal ((Real.log 2)⁻¹ * (4 / (Nat.fib (n + 1) : ℝ) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-- **Brick 2b-iii per-cylinder term (2b-ii ∘ Chebyshev).**  On a genuine depth-`d`
cylinder `w'` (`d < N`, slack `δ' := δ − d/N > 0`), the base-`[]` `v`-bad mass at
scale `N` inside `w'` is a fixed FRACTION of `γ(cfCylinder w')` — the fraction
`7·(8|v|+80)·γ(v)/(δ'²(N−d))` is INDEPENDENT of `w'`, so it factors out of the sum
over interior cylinders in 2b-iii.  Composes `gaussMeasure_cfBadZone_nil_inter_cylinder_le`
(2b-ii) with `chebyshev_blockCount_brick` at base `w'`, scale `N−d`, slack `δ'`. -/
theorem gaussMeasure_cfBadZone_nil_inter_cylinder_frac_le
    (v w' : List ℕ) (N : ℕ) (δ : ℝ)
    (hposw' : ∀ a ∈ w', 1 ≤ a) (hposv : ∀ a ∈ v, 1 ≤ a)
    (hdN : w'.length < N) (hδ' : 0 < δ - (w'.length : ℝ) / (N : ℝ)) :
    gaussMeasure (cfBadZone [] v N δ ∩ cfCylinder w')
      ≤ ENNReal.ofReal (7 * ((8 * v.length + 80)
          * (gaussMeasure (cfCylinder v)).toReal
          / ((δ - (w'.length : ℝ) / (N : ℝ)) ^ 2 * ((N - w'.length : ℕ) : ℝ)))
          * (gaussMeasure (cfCylinder w')).toReal) := by
  set δ' : ℝ := δ - (w'.length : ℝ) / (N : ℝ) with hδ'def
  have hstep := gaussMeasure_cfBadZone_nil_inter_cylinder_le v w' N δ hdN
  have hcheb := chebyshev_blockCount_brick w' v hposw' hposv (N - w'.length)
    (by omega) hδ'
  have hfin : gaussMeasure (cfBadZone w' v (N - w'.length) δ') ≠ ⊤ := measure_ne_top _ _
  refine hstep.trans ?_
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hcheb

/-- **Brick 2b-iii — route-B assembly (single scale/family element).**  The whole
route-B bound in one lemma, for a single `v` and single absolute scale `N`: the
`γ`-mass of the base-`[]` `v`-bad zone at scale `N` inside an interval `(a,b)` is a
FRACTION of `γ(a,b)` plus a boundary residual.  Cover `(a,b)` by depth-`d`
cylinders (`d < N`): the interior (fully-contained) cylinders carry a `frac·γ`
each (`gaussMeasure_cfBadZone_nil_inter_cylinder_frac_le`, `frac` uniform since all
have length `d`), summed over the DISJOINT cover (`measure_biUnion`) to `frac·γ(a,b)`;
the uncovered boundary strip carries `≤ (log 2)⁻¹·4/fib(d+1)²`
(`gaussMeasure_interval_sdiff_covered_le`).  In the route-B regime `N ≳ 2d` the
fraction is `≈ (8|v|+80)γ(v)/(δ²N)` and the residual `< γ(a,b)`.  This is the
route-decisive B6 bound; 2b-iii proper aggregates it over `v ∈ F` and `N ∈ NS`
(finite sums on top). -/
theorem gaussMeasure_interval_inter_cfBadZone_nil_le
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (v : List ℕ) (hposv : ∀ x ∈ v, 1 ≤ x) (N d : ℕ) (δ : ℝ)
    (hdN : d < N) (hδ' : 0 < δ - (d : ℝ) / (N : ℝ)) :
    gaussMeasure (Set.Ioo a b ∩ cfBadZone [] v N δ)
      ≤ ENNReal.ofReal (7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
            / ((δ - (d : ℝ) / (N : ℝ)) ^ 2 * ((N - d : ℕ) : ℝ))))
          * gaussMeasure (Set.Ioo a b)
        + ENNReal.ofReal ((Real.log 2)⁻¹ * (4 / (Nat.fib (d + 1) : ℝ) ^ 2)) := by
  set B : Set ℝ := cfBadZone [] v N δ with hB
  set frac : ℝ := 7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
      / ((δ - (d : ℝ) / (N : ℝ)) ^ 2 * ((N - d : ℕ) : ℝ))) with hfrac
  have hfrac0 : 0 ≤ frac := by rw [hfrac]; positivity
  set S : Set (List ℕ) := {w ∈ genWords d | cfCylinder w ⊆ Set.Ioo a b} with hSdef
  have hmemS : ∀ w : List ℕ, w ∈ S ↔
      (w.length = d ∧ (∀ a ∈ w, 1 ≤ a)) ∧ cfCylinder w ⊆ Set.Ioo a b := by
    intro w; rw [hSdef]; simp only [genWords, Set.mem_setOf_eq]
  have hScount : S.Countable := Set.Countable.mono (Set.sep_subset _ _)
    (Set.Countable.mono (Set.subset_univ _) Set.countable_univ)
  have hSdisj : S.PairwiseDisjoint (fun w => cfCylinder w) := by
    intro w hw w' hw' hne
    exact cfCylinder_disjoint (by rw [((hmemS w).1 hw).1.1, ((hmemS w').1 hw').1.1]) hne
  have hcov_eq : coveredByCyl a b d = ⋃ w ∈ S, cfCylinder w := rfl
  have hcovsub : coveredByCyl a b d ⊆ Set.Ioo a b := by
    rw [hcov_eq]; exact Set.iUnion₂_subset fun w hw => ((hmemS w).1 hw).2
  have hcovmeas : gaussMeasure (coveredByCyl a b d)
      = ∑' w : S, gaussMeasure (cfCylinder (w : List ℕ)) := by
    rw [hcov_eq]
    exact measure_biUnion hScount hSdisj (fun w _ => measurableSet_cfCylinder w)
  -- interior bound
  have hint : gaussMeasure (coveredByCyl a b d ∩ B)
      ≤ ENNReal.ofReal frac * gaussMeasure (Set.Ioo a b) := by
    have hdist : coveredByCyl a b d ∩ B = ⋃ w ∈ S, (cfCylinder w ∩ B) := by
      rw [hcov_eq, Set.iUnion₂_inter]
    rw [hdist]
    calc gaussMeasure (⋃ w ∈ S, (cfCylinder w ∩ B))
        ≤ ∑' w : S, gaussMeasure (cfCylinder (w : List ℕ) ∩ B) :=
          measure_biUnion_le gaussMeasure hScount _
      _ ≤ ∑' w : S, ENNReal.ofReal frac * gaussMeasure (cfCylinder (w : List ℕ)) := by
          apply ENNReal.tsum_le_tsum
          intro w
          obtain ⟨⟨hwlen, hwpos⟩, -⟩ := (hmemS (w : List ℕ)).1 w.2
          have hd' : (w : List ℕ).length < N := by rw [hwlen]; exact hdN
          have hδ'w : 0 < δ - ((w : List ℕ).length : ℝ) / (N : ℝ) := by rw [hwlen]; exact hδ'
          have hfr := gaussMeasure_cfBadZone_nil_inter_cylinder_frac_le v (w : List ℕ) N δ
            hwpos hposv hd' hδ'w
          rw [Set.inter_comm (cfCylinder (w : List ℕ)) B]
          rw [hwlen, ← hfrac, ← hB,
            ENNReal.ofReal_mul hfrac0,
            ENNReal.ofReal_toReal (measure_ne_top gaussMeasure (cfCylinder (w : List ℕ)))]
            at hfr
          exact hfr
      _ = ENNReal.ofReal frac * ∑' w : S, gaussMeasure (cfCylinder (w : List ℕ)) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal frac * gaussMeasure (coveredByCyl a b d) := by rw [hcovmeas]
      _ ≤ ENNReal.ofReal frac * gaussMeasure (Set.Ioo a b) := by
          gcongr
  -- combine with residual
  have hsplit : Set.Ioo a b ∩ B
      ⊆ (coveredByCyl a b d ∩ B) ∪ (Set.Ioo a b \ coveredByCyl a b d) := by
    rintro x ⟨hxJ, hxB⟩
    by_cases hc : x ∈ coveredByCyl a b d
    · exact Or.inl ⟨hc, hxB⟩
    · exact Or.inr ⟨hxJ, hc⟩
  have hres := gaussMeasure_interval_sdiff_covered_le a b ha hab hb d
  calc gaussMeasure (Set.Ioo a b ∩ B)
      ≤ gaussMeasure ((coveredByCyl a b d ∩ B) ∪ (Set.Ioo a b \ coveredByCyl a b d)) :=
        measure_mono hsplit
    _ ≤ gaussMeasure (coveredByCyl a b d ∩ B)
          + gaussMeasure (Set.Ioo a b \ coveredByCyl a b d) := measure_union_le _ _
    _ ≤ ENNReal.ofReal frac * gaussMeasure (Set.Ioo a b)
          + ENNReal.ofReal ((Real.log 2)⁻¹ * (4 / (Nat.fib (d + 1) : ℝ) ^ 2)) := by
        gcongr

/-- **Brick 2b-iii — route-B assembly (aggregate over `F` and `NS`).**  Finite
double-subadditivity on top of the single scale/family lemma: the `γ`-mass of the
base-`[]` bad zone over ALL `v ∈ F` and ALL absolute scales `n ∈ NS`, inside an
interval `(a,b)`, is bounded by the double sum of the per-`(n,v)` (fraction·γ +
residual) bounds.  Covering depth `d` fixed (`d < n` for every `n ∈ NS`).  This is
the full route-B interval bound the ψ-pullback bridge to brick 3 consumes. -/
theorem gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (F : Finset (List ℕ)) (hposF : ∀ v ∈ F, ∀ x ∈ v, 1 ≤ x)
    (NS : Finset ℕ) (d : ℕ) (δ : ℝ)
    (hdN : ∀ n ∈ NS, d < n) (hδ' : ∀ n ∈ NS, 0 < δ - (d : ℝ) / (n : ℝ)) :
    gaussMeasure (Set.Ioo a b ∩ ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone [] v n δ)
      ≤ ∑ n ∈ NS, ∑ v ∈ F,
          (ENNReal.ofReal (7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
                / ((δ - (d : ℝ) / (n : ℝ)) ^ 2 * ((n - d : ℕ) : ℝ))))
              * gaussMeasure (Set.Ioo a b)
            + ENNReal.ofReal ((Real.log 2)⁻¹ * (4 / (Nat.fib (d + 1) : ℝ) ^ 2))) := by
  have hrw : Set.Ioo a b ∩ ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone [] v n δ
      = ⋃ n ∈ NS, ⋃ v ∈ F, (Set.Ioo a b ∩ cfBadZone [] v n δ) := by
    simp only [Set.inter_iUnion]
  rw [hrw]
  calc gaussMeasure (⋃ n ∈ NS, ⋃ v ∈ F, (Set.Ioo a b ∩ cfBadZone [] v n δ))
      ≤ ∑ n ∈ NS, gaussMeasure (⋃ v ∈ F, (Set.Ioo a b ∩ cfBadZone [] v n δ)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ NS, ∑ v ∈ F, gaussMeasure (Set.Ioo a b ∩ cfBadZone [] v n δ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact measure_biUnion_finset_le _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun v hv => ?_
        exact gaussMeasure_interval_inter_cfBadZone_nil_le a b ha hab hb v (hposF v hv)
          n d δ (hdN n hn) (hδ' n hn)

/-- **ψ-pullback bridge (route B).**  Pull the route-B image-space bound back into
`x`-space over a target interval: `γ((c,d) ∩ ψ⁻¹ S) ≤ (2/q)·γ(ψ((c,d)) ∩ S)`, where
`ψ((c,d)) = (qc+r, qd+r)`.  Uses the affine bijection identity `(c,d) ∩ ψ⁻¹ S =
ψ⁻¹(S ∩ ψ((c,d)))` (`preimage_image_eq` for injective `ψ`) then brick 1
(`gaussMeasure_preimage_affineMap_le`).  This is what turns the route-B interval
bound `gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le` (applied with `J =
ψ((c,d))`) into the `z`-bad mass a `wz=[]` variant of brick 3 consumes. -/
theorem gaussMeasure_interval_inter_preimage_affineMap_le {q : ℝ} (hq : 0 < q) (r : ℝ)
    (c d : ℝ) (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo (0 : ℝ) 1) :
    gaussMeasure (Set.Ioo c d ∩ affineMap q r ⁻¹' S)
      ≤ ENNReal.ofReal (2 / q) * gaussMeasure (S ∩ Set.Ioo (q * c + r) (q * d + r)) := by
  have hinj : Function.Injective (affineMap q r) := fun x y h => by
    simp only [affineMap] at h; exact mul_left_cancel₀ (ne_of_gt hq) (by linarith)
  have hkey : Set.Ioo c d ∩ affineMap q r ⁻¹' S
      = affineMap q r ⁻¹' (S ∩ Set.Ioo (q * c + r) (q * d + r)) := by
    rw [Set.preimage_inter, ← image_affineMap_Ioo hq, Set.preimage_image_eq _ hinj,
      Set.inter_comm]
  rw [hkey]
  have hsub' : S ∩ Set.Ioo (q * c + r) (q * d + r) ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.inter_subset_left.trans hSsub
  have hmeas' : MeasurableSet (S ∩ Set.Ioo (q * c + r) (q * d + r)) :=
    hS.inter measurableSet_Ioo
  exact gaussMeasure_preimage_affineMap_le hq r _ hmeas' hsub'

/-- **Steerable-good measure core (B6 crux).**  For a genuine base word `wx`, a
finite family `F`, tolerance `δ > 0`, and a target subinterval `(c,d) ⊆
cfCylinder wx` of positive `γ`-measure, beyond a length threshold `N` every
`n ≥ N` admits an IRRATIONAL point `x ∈ (c,d)` avoiding ALL of `wx`'s CF
`n`-step discrepancy bad zones for `F`.  Its length-`n` orbit block from `wx` is
therefore `δ`-frequency-good FOR EVERY `v ∈ F` — AND the point already lies in
the target `(c,d)`, so the freq-good digits THEMSELVES steer into the target: no
uncontrolled navigation filler.  This is the route-decisive crux ingredient (the
interleaved schedule's ψ-stage): the aggregate bad-zone mass is `O(1/n)·γ(I_wx)`
(`gaussMeasure_aggregate_cfBadZone_le`) while `γ(c,d)` is a fixed positive
fraction, so for `n` large the good mass FILLS `(c,d)`. -/
theorem exists_irrational_notMem_cfBadZone_in_Ioo (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ : ℝ} (hδ : 0 < δ) {c d : ℝ}
    (hpos : 0 < (gaussMeasure (Set.Ioo c d)).toReal) :
    ∃ N : ℕ, ∀ n, N ≤ n → 0 < n → ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧
      x ∉ ⋃ v ∈ F, cfBadZone wx v n δ := by
  -- aggregate bad-zone measure bound: `≤ S / n · 1`, with `S` an explicit constant
  set S : ℝ := ∑ v ∈ F, 7 * ((8 * v.length + 80)
      * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2))
      * (gaussMeasure (cfCylinder wx)).toReal with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun v _ => ?_
    have h1 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have h2 : (0:ℝ) ≤ (gaussMeasure (cfCylinder wx)).toReal := ENNReal.toReal_nonneg
    have : (0:ℝ) ≤ (8 * v.length + 80) := by positivity
    positivity
  -- pick N large enough that `S / N < γ(c,d)`
  obtain ⟨N, hN⟩ := exists_nat_gt (S / (gaussMeasure (Set.Ioo c d)).toReal)
  refine ⟨max N 1, fun n hn hn0 => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  -- the bad zone measure (toReal) is `≤ S / n`
  have hbad := gaussMeasure_aggregate_cfBadZone_le wx hwxpos F hF n hn0 hδ
  have hSn : (∑ v ∈ F, 7 * ((8 * v.length + 80)
      * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n))
      * (gaussMeasure (cfCylinder wx)).toReal) = S / n := by
    rw [hS, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hne : (δ:ℝ) ^ 2 * n ≠ 0 := by positivity
    have hne2 : (δ:ℝ) ^ 2 ≠ 0 := by positivity
    have hnn : (n:ℝ) ≠ 0 := hnR.ne'
    field_simp
  rw [hSn] at hbad
  -- `S / n ≤ S / N < γ(c,d)`
  have hglt : S / (n:ℝ) < (gaussMeasure (Set.Ioo c d)).toReal := by
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast hnN
    have hNpos : (0:ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h] at hN; simp only [Nat.cast_zero] at hN
        have : 0 ≤ S / (gaussMeasure (Set.Ioo c d)).toReal := div_nonneg hS0 hpos.le
        linarith
      · exact_mod_cast h
    have hmono : S / (n:ℝ) ≤ S / N := by
      apply div_le_div_of_nonneg_left hS0 hNpos hNn
    have hNlt : S / (N:ℝ) < (gaussMeasure (Set.Ioo c d)).toReal := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hpos] at hN
      linarith [hN]
    linarith
  -- so `γ(⋃ bad) < γ(c,d)` as `ENNReal`
  set A : Set ℝ := Set.Ioo c d with hA
  set B : Set ℝ := ⋃ v ∈ F, cfBadZone wx v n δ with hB
  have hBfin : gaussMeasure B ≠ ⊤ := measure_ne_top _ _
  have hAfin : gaussMeasure A ≠ ⊤ := measure_ne_top _ _
  have hBltA : gaussMeasure B < gaussMeasure A := by
    rw [← ENNReal.toReal_lt_toReal hBfin hAfin]
    exact lt_of_le_of_lt hbad hglt
  -- hence `γ(A \ B) > 0`
  have hAsub : gaussMeasure A ≤ gaussMeasure (A \ B) + gaussMeasure B := by
    have hcov : A ⊆ (A \ B) ∪ B := fun x hx => by
      by_cases h : x ∈ B
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    exact (measure_mono hcov).trans (measure_union_le _ _)
  have hABpos : 0 < gaussMeasure (A \ B) := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, zero_add] at hAsub
    exact absurd (lt_of_lt_of_le hBltA hAsub) (lt_irrefl _)
  -- remove the (null) rationals and extract an irrational point
  have hac : gaussMeasure ≪ (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hQnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
    apply hac
    rw [Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null Set.inter_subset_left
      ((Set.countable_range _).measure_zero volume)
  have hposdiff : 0 < gaussMeasure ((A \ B) \ Set.range ((↑) : ℚ → ℝ)) := by
    have heq : gaussMeasure ((A \ B) \ Set.range ((↑) : ℚ → ℝ)) = gaussMeasure (A \ B) :=
      measure_sdiff_null (s := A \ B) hQnull
    rw [heq]; exact hABpos
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hposdiff.ne'
  obtain ⟨⟨hxA, hxB⟩, hxQ⟩ := hx
  exact ⟨x, hxQ, hxA, hxB⟩

/-- **Abstract irrational-selection core.**  Any set `B'` of Gauss measure
strictly below that of `Ioo c d` misses an irrational point of `Ioo c d`.  The
measure-theoretic heart shared by the bad-zone selection lemmas, factored out so
the cfK-steer graft can pass `B' = (bad zones) ∪ (cfK-large extensions)` and get a
point that is BOTH freq-good AND cfK-controlled in one shot — it only needs to
prove `gaussMeasure (bad ∪ cfKbad) < gaussMeasure (Ioo c d)`, which
`frac_mass_bad_extensions` (+ the volume↔Gauss bridge) supplies. -/
theorem exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt {c d : ℝ} (B' : Set ℝ)
    (hlt : gaussMeasure B' < gaussMeasure (Set.Ioo c d)) :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧ x ∉ B' := by
  set A : Set ℝ := Set.Ioo c d with hA
  have hAsub : gaussMeasure A ≤ gaussMeasure (A \ B') + gaussMeasure B' := by
    have hcov : A ⊆ (A \ B') ∪ B' := fun x hx => by
      by_cases h : x ∈ B'
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    exact (measure_mono hcov).trans (measure_union_le _ _)
  have hABpos : 0 < gaussMeasure (A \ B') := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, zero_add] at hAsub
    exact absurd (lt_of_lt_of_le hlt hAsub) (lt_irrefl _)
  have hac : gaussMeasure ≪ (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hQnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
    apply hac
    rw [Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null Set.inter_subset_left
      ((Set.countable_range _).measure_zero volume)
  have hposdiff : 0 < gaussMeasure ((A \ B') \ Set.range ((↑) : ℚ → ℝ)) := by
    have heq : gaussMeasure ((A \ B') \ Set.range ((↑) : ℚ → ℝ)) = gaussMeasure (A \ B') :=
      measure_sdiff_null (s := A \ B') hQnull
    rw [heq]; exact hABpos
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hposdiff.ne'
  obtain ⟨⟨hxA, hxB⟩, hxQ⟩ := hx
  exact ⟨x, hxQ, hxA, hxB⟩

/-- **Multi-scale measure core.**  Given the aggregate multi-scale bad-zone
measure bound is below `γ(c,d)` (the caller supplies this, having chosen `n₁`
large relative to `|NS|`), there is an irrational point of `(c,d)` avoiding EVERY
CF bad zone `cfBadZone wx v n δ` for `v∈F` and `n∈NS` SIMULTANEOUSLY.  This is the
uniform-goodness engine: with quadratically-spaced `NS` the point's digit block is
freq-good at every prefix scale in `NS`. -/
theorem exists_irrational_notMem_multiscale_cfBadZone_in_Ioo
    (wx : List ℕ) (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ : ℝ} (hδ : 0 < δ) {c d : ℝ}
    (hpos : 0 < (gaussMeasure (Set.Ioo c d)).toReal)
    (NS : Finset ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁) (hNS : ∀ n ∈ NS, n₁ ≤ n)
    (hbound : (NS.card : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal))
        < (gaussMeasure (Set.Ioo c d)).toReal) :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧
      x ∉ ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone wx v n δ := by
  have hbad := gaussMeasure_multiscale_cfBadZone_le wx hwxpos F hF NS hn₁ hNS hδ
  set A : Set ℝ := Set.Ioo c d with hA
  set B : Set ℝ := ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone wx v n δ with hB
  have hBfin : gaussMeasure B ≠ ⊤ := measure_ne_top _ _
  have hAfin : gaussMeasure A ≠ ⊤ := measure_ne_top _ _
  have hBltA : gaussMeasure B < gaussMeasure A := by
    rw [← ENNReal.toReal_lt_toReal hBfin hAfin]
    exact lt_of_le_of_lt hbad hbound
  have hAsub : gaussMeasure A ≤ gaussMeasure (A \ B) + gaussMeasure B := by
    have hcov : A ⊆ (A \ B) ∪ B := fun x hx => by
      by_cases h : x ∈ B
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    exact (measure_mono hcov).trans (measure_union_le _ _)
  have hABpos : 0 < gaussMeasure (A \ B) := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, zero_add] at hAsub
    exact absurd (lt_of_lt_of_le hBltA hAsub) (lt_irrefl _)
  have hac : gaussMeasure ≪ (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hQnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
    apply hac
    rw [Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null Set.inter_subset_left
      ((Set.countable_range _).measure_zero volume)
  have hposdiff : 0 < gaussMeasure ((A \ B) \ Set.range ((↑) : ℚ → ℝ)) := by
    have heq : gaussMeasure ((A \ B) \ Set.range ((↑) : ℚ → ℝ)) = gaussMeasure (A \ B) :=
      measure_sdiff_null (s := A \ B) hQnull
    rw [heq]; exact hABpos
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hposdiff.ne'
  obtain ⟨⟨hxA, hxB⟩, hxQ⟩ := hx
  exact ⟨x, hxQ, hxA, hxB⟩

/-- **L4 route — brick 3: combined single-stream selection.**  Selects ONE
irrational `x ∈ (c,d)` that SIMULTANEOUSLY avoids (i) the `x`-CF bad zones (base
`wx`, scales `NSx`) — so `x` itself is freq-good — AND (ii) the ψ-pullback of the
`z`-CF bad zones (base `wz`, scales `NSz`) — so `ψ(x)` is freq-good at `z`-scales
past `|wz|`.  The caller supplies ONE measure hypothesis `hbound`: the `x`-bad
multiscale mass PLUS `(2/q)·`(the `z`-bad multiscale mass for `wz`) stays below
`γ(c,d)`.  This is the single-stream heart of L4: no two-stream alternation, target
is the full `x`-interval `(c,d)`.  The `z`-bad term carries the factor
`γ(cfCylinder wz)` (via brick 2a `gaussMeasure_preimage_multiscale_cfBadZone_le`);
the alignment brick 2b bounds `γ(cfCylinder wz) ≤ C·γ(c,d)` so `hbound` holds once
`n₁z ≳ C` (polynomial, NO exponential `1/ρ` blowup). -/
theorem exists_irrational_notMem_xbad_psi_zbad_in_Ioo {q : ℝ} (hq : 0 < q) (r : ℝ)
    (wx : List ℕ) (hwxpos : ∀ a ∈ wx, 1 ≤ a)
    (wz : List ℕ) (hwzpos : ∀ a ∈ wz, 1 ≤ a)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    {c d : ℝ} (hpos : 0 < (gaussMeasure (Set.Ioo c d)).toReal)
    (NSx : Finset ℕ) {n₁x : ℕ} (hn₁x : 0 < n₁x) (hNSx : ∀ n ∈ NSx, n₁x ≤ n)
    (NSz : Finset ℕ) {n₁z : ℕ} (hn₁z : 0 < n₁z) (hNSz : ∀ n ∈ NSz, n₁z ≤ n)
    (hbound : (NSx.card : ℝ) * (∑ v ∈ F, 7 * ((8 * v.length + 80)
          * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁x))
          * (gaussMeasure (cfCylinder wx)).toReal)
        + (2 / q) * ((NSz.card : ℝ) * (∑ v ∈ F, 7 * ((8 * v.length + 80)
          * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁z))
          * (gaussMeasure (cfCylinder wz)).toReal))
        < (gaussMeasure (Set.Ioo c d)).toReal) :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧
      x ∉ (⋃ n ∈ NSx, ⋃ v ∈ F, cfBadZone wx v n δ) ∧
      x ∉ (⋃ n ∈ NSz, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone wz v n δ) := by
  set A : Set ℝ := Set.Ioo c d with hA
  set Bx : Set ℝ := ⋃ n ∈ NSx, ⋃ v ∈ F, cfBadZone wx v n δ with hBx
  set Bz : Set ℝ := ⋃ n ∈ NSz, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone wz v n δ with hBz
  have hxbad := gaussMeasure_multiscale_cfBadZone_le wx hwxpos F hF NSx hn₁x hNSx hδ
  have hzbad := gaussMeasure_preimage_multiscale_cfBadZone_le hq r wz hwzpos F hF NSz hn₁z hNSz hδ
  -- combined bad set and its real-valued mass bound
  set B : Set ℝ := Bx ∪ Bz with hBdef
  have hBr : (gaussMeasure B).toReal
      ≤ (gaussMeasure Bx).toReal + (gaussMeasure Bz).toReal := by
    calc (gaussMeasure B).toReal
        ≤ (gaussMeasure Bx + gaussMeasure Bz).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
            (measure_union_le _ _)
      _ = (gaussMeasure Bx).toReal + (gaussMeasure Bz).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hBltA : gaussMeasure B < gaussMeasure A := by
    rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    calc (gaussMeasure B).toReal
        ≤ (gaussMeasure Bx).toReal + (gaussMeasure Bz).toReal := hBr
      _ ≤ _ := by
          refine add_le_add hxbad ?_
          exact hzbad
      _ < (gaussMeasure A).toReal := hbound
  obtain ⟨x, hxirr, hxA, hxB⟩ := exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt B hBltA
  rw [hBdef, Set.mem_union, not_or] at hxB
  exact ⟨x, hxirr, hxA, hxB.1, hxB.2⟩

/-- **L4 route — brick 3′ (route-B, `wz = []`): combined single-stream selection
via the ψ-pullback bridge.**  Like `exists_irrational_notMem_xbad_psi_zbad_in_Ioo`
but the `z`-bad zones use ABSOLUTE scales (base `[]`), and the measure hypothesis
`hbound` bounds the `z`-term by the ψ-image interval mass `γ(ψ((c,d)) ∩ zBadUnion)`
(supplied by `gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le`) rather than a
`z`-cylinder mass.  The pullback factor `2/q` comes from
`gaussMeasure_interval_inter_preimage_affineMap_le`.  This is the selection heart
of route B: `x ∈ (c,d)` freq-good AND `ψ(x)` freq-good at every absolute `z`-scale
in `NSz` — with LINEAR (not two-stream super-exponential) mass budget. -/
theorem exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo {q : ℝ} (hq : 0 < q) (r : ℝ)
    (wx : List ℕ) (F : Finset (List ℕ)) {δ : ℝ}
    {c d : ℝ}
    (NSx : Finset ℕ) (NSz : Finset ℕ)
    (hbound : gaussMeasure (⋃ n ∈ NSx, ⋃ v ∈ F, cfBadZone wx v n δ)
        + ENNReal.ofReal (2 / q)
          * gaussMeasure (Set.Ioo (q * c + r) (q * d + r)
              ∩ ⋃ n ∈ NSz, ⋃ v ∈ F, cfBadZone [] v n δ)
        < gaussMeasure (Set.Ioo c d)) :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧
      x ∉ (⋃ n ∈ NSx, ⋃ v ∈ F, cfBadZone wx v n δ) ∧
      x ∉ (⋃ n ∈ NSz, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone [] v n δ) := by
  set Bx : Set ℝ := ⋃ n ∈ NSx, ⋃ v ∈ F, cfBadZone wx v n δ with hBx
  set U : Set ℝ := ⋃ n ∈ NSz, ⋃ v ∈ F, cfBadZone [] v n δ with hU
  set Bz : Set ℝ := ⋃ n ∈ NSz, ⋃ v ∈ F, affineMap q r ⁻¹' cfBadZone [] v n δ with hBz
  -- `Bz` is the affine pullback of the whole absolute-scale bad union `U`
  have hBzeq : Bz = affineMap q r ⁻¹' U := by
    rw [hBz, hU]; simp only [Set.preimage_iUnion]
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact MeasurableSet.biUnion NSz.countable_toSet fun n _ =>
      Finset.measurableSet_biUnion F fun v _ => measurableSet_cfBadZone [] v n δ
  have hUsub : U ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [hU]
    refine Set.iUnion₂_subset fun n _ => Set.iUnion₂_subset fun v _ => ?_
    exact Set.inter_subset_left.trans (cfCylinder_subset_Ioo [])
  -- combined bad set restricted to the target interval
  set B' : Set ℝ := Set.Ioo c d ∩ (Bx ∪ Bz) with hB'
  have hlt : gaussMeasure B' < gaussMeasure (Set.Ioo c d) := by
    refine lt_of_le_of_lt ?_ hbound
    calc gaussMeasure B'
        ≤ gaussMeasure (Set.Ioo c d ∩ Bx) + gaussMeasure (Set.Ioo c d ∩ Bz) := by
          rw [hB', Set.inter_union_distrib_left]; exact measure_union_le _ _
      _ ≤ gaussMeasure Bx
            + ENNReal.ofReal (2 / q) * gaussMeasure (Set.Ioo (q * c + r) (q * d + r) ∩ U) := by
          gcongr ?_ + ?_
          · exact measure_mono Set.inter_subset_right
          · rw [hBzeq, Set.inter_comm (Set.Ioo (q * c + r) (q * d + r)) U]
            exact gaussMeasure_interval_inter_preimage_affineMap_le hq r c d U hUmeas hUsub
  obtain ⟨x, hxirr, hxA, hxB⟩ := exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt B' hlt
  rw [hB'] at hxB
  have hxBx : x ∉ Bx := fun h => hxB ⟨hxA, Or.inl h⟩
  have hxBz : x ∉ Bz := fun h => hxB ⟨hxA, Or.inr h⟩
  exact ⟨x, hxirr, hxA, hxBx, hxBz⟩

/-- **Brick 5 core — scale-coverage ⇒ convergence (route-B z-side engine).**  A
purely quantitative packaging: if `f n` is within `δ s` of the target `L`
whenever `n` lies in stage `s`'s controlled scale set `S s` (`havoid`), and the
stages COVER all large `n` with arbitrarily small tolerance (`hcover`: for every
`ε` there is a threshold past which every `n` sits in SOME stage with `δ s < ε`),
then `f n → L`.  This is exactly how `ψ(xA)`'s window frequency equidistributes in
route B: the digit stream of `ψ(xA)` is NOT built blockwise (so the telescoping
`chain_orbit_equidist_uniform` does not apply), but every stage forces `ψ(x) ∉
cfBadZone [] v n δ_s` for `n` in that stage's z-range, i.e. `|blockCount v n
(ψxA)/n − γv| < δ_s`, and the ranges cover all large `n` with `δ_s → 0`.  Pure
`Metric.tendsto_atTop`. -/
theorem tendsto_of_scale_coverage {L : ℝ} {f : ℕ → ℝ}
    (δ : ℕ → ℝ) (S : ℕ → Set ℕ)
    (havoid : ∀ s, ∀ n ∈ S s, |f n - L| < δ s)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ s, δ s < ε ∧ n ∈ S s) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hcover ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨s, hδs, hnS⟩ := hn₀ n hn
  rw [Real.dist_eq]
  exact lt_trans (havoid s n hnS) hδs

/-- **Digit-agreement transfer for `blockCount` (brick-4 z-transfer core).**  Two
full-orbit reals that agree on their first `m` CF digits have EQUAL `v`-block count
at every scale `n` with `n + |v| ≤ m`: the length-`n` orbit count of `cfCylinder v`
reads only digits `< n + |v|`.  This is the mechanism by which point-avoidance of an
ABSOLUTE-scale z-bad zone transfers to the chain LIMIT: once the `x`-cylinder is deep
enough that `ψ(cfCylinder wx')` fixes `ψ(x)`'s first `m` z-digits, `ψ(xA)` inherits the
selected point's `z`-frequency at all scales `≤ m − |v|`. -/
theorem blockCount_eq_of_cfDigit_agree {z z' : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] z ∈ Set.Ioo (0 : ℝ) 1)
    (horb' : ∀ j : ℕ, gaussMap^[j] z' ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (n m : ℕ) (hm : n + v.length ≤ m)
    (hagree : ∀ i < m, cfDigit z i = cfDigit z' i) :
    blockCount (cfCylinder v) n z = blockCount (cfCylinder v) n z' := by
  have hz := blockCount_eq_card_matches horb v 0 n
  have hz' := blockCount_eq_card_matches horb' v 0 n
  simp only [Function.iterate_zero_apply] at hz hz'
  rw [hz, hz']
  have hfilter : (Finset.range n).filter (fun j => MatchesAt (cfDigit z) v (0 + j))
      = (Finset.range n).filter (fun j => MatchesAt (cfDigit z') v (0 + j)) := by
    apply Finset.filter_congr
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Nat.zero_add, eq_iff_iff]
    constructor
    · intro hM i hi
      rw [← hagree (j + i) (by omega)]; exact hM i hi
    · intro hM i hi
      rw [hagree (j + i) (by omega)]; exact hM i hi
  rw [hfilter]

/-- **Local CF-digit stability around an irrational (brick-4 geometric core).**
Around an irrational `y ∈ (0,1)` there is an open neighbourhood on which the first
`m` CF digits are CONSTANT (equal to `y`'s): `y` sits strictly inside its own
depth-`m` cylinder (a rational-endpoint interval), so a small enough ball lands in
the cylinder's irrational interior.  With `ψ` Lipschitz this is what lets a deep
enough `x`-cylinder pin `ψ(x)`'s first `m` z-digits for ALL its points, so the
brick-3′ point's z-frequency transfers to the chain limit `ψ(xA)`
(`blockCount_eq_of_cfDigit_agree`). -/
theorem exists_nhds_cfDigit_eq {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hyirr : Irrational y) (m : ℕ) :
    ∃ ε > 0, ∀ x ∈ Set.Ioo (y - ε) (y + ε), Irrational x → x ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ i < m, cfDigit x i = cfDigit y i := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact ⟨1, one_pos, fun x _ _ _ i hi => absurd hi (by omega)⟩
  set w : List ℕ := (List.range m).map (cfDigit y) with hwdef
  have hwlen : w.length = m := by simp [hwdef]
  have hwne : w ≠ [] := by rw [← List.length_pos_iff_ne_nil, hwlen]; omega
  have hwpos : ∀ a ∈ w, 1 ≤ a := by
    intro a ha; rw [hwdef, List.mem_map] at ha; obtain ⟨i, _, rfl⟩ := ha
    exact one_le_cfDigit y hyirr hy i
  have hwgetD : ∀ i, i < m → w.getD i 0 = cfDigit y i := by
    intro i hi
    rw [hwdef, List.getD_eq_getElem _ _ (by simpa [hwlen] using hi)]
    simp [hwdef]
  have hywmem : y ∈ cfCylinder w := by
    refine ⟨hy, fun i hi => ?_⟩
    rw [hwlen] at hi; rw [hwgetD i hi]
  set E0 : ℝ := ((cfVal w : ℚ) : ℝ) with hE0
  set E1 : ℝ := ((cfVal (bumpLast w) : ℚ) : ℝ) with hE1
  have hyIcc : y ∈ Set.Icc (min E0 E1) (max E0 E1) := cfCylinder_subset_uIcc w hwne hwpos hywmem
  have hirrE0 : y ≠ E0 := fun h => hyirr ⟨cfVal w, h.symm⟩
  have hirrE1 : y ≠ E1 := fun h => hyirr ⟨cfVal (bumpLast w), h.symm⟩
  have hlo : min E0 E1 < y := lt_of_le_of_ne hyIcc.1 fun h => by
    rcases min_choice E0 E1 with h' | h' <;> rw [h'] at h
    · exact hirrE0 h.symm
    · exact hirrE1 h.symm
  have hhi : y < max E0 E1 := lt_of_le_of_ne hyIcc.2 fun h => by
    rcases max_choice E0 E1 with h' | h' <;> rw [h'] at h
    · exact hirrE0 h
    · exact hirrE1 h
  refine ⟨min (y - min E0 E1) (max E0 E1 - y), by positivity, ?_⟩
  intro x hx hxirr _ i hi
  have hxuIoo : x ∈ Set.uIoo E0 E1 := by
    show x ∈ Set.Ioo (min E0 E1) (max E0 E1)
    obtain ⟨hx1, hx2⟩ := hx
    have hleL : min (y - min E0 E1) (max E0 E1 - y) ≤ y - min E0 E1 := min_le_left _ _
    have hleR : min (y - min E0 E1) (max E0 E1 - y) ≤ max E0 E1 - y := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  have hxw : x ∈ cfCylinder w := uIoo_subset_cfCylinder w hwne hwpos x hxuIoo hxirr
  have := hxw.2 i (by rw [hwlen]; exact hi)
  rw [hwgetD i hi] at this
  exact this

/-- **ψ-transfer of CF-digit agreement (brick-4 bridge).**  If `ψ = affineMap q r`
(`q>0`) maps `x₀` to an irrational point of `(0,1)`, then for any digit-depth `m`
there is a ball around `x₀` on which every point whose ψ-image is irrational-in-(0,1)
has ψ-image agreeing with `ψ x₀` on its first `m` CF digits.  `ψ` is `q`-Lipschitz,
so shrinking the `exists_nhds_cfDigit_eq` z-neighbourhood by `1/q` pulls it back to an
x-ball.  Composed with `blockCount_eq_of_cfDigit_agree` this transfers the selected
point's z-frequency to any nearby point — in particular to the chain limit `xA` once
the `x`-cylinder is refined below this ball. -/
theorem exists_ball_cfDigit_psi_eq (q r : ℝ) (hq : 0 < q)
    {x₀ : ℝ} (hx₀ : affineMap q r x₀ ∈ Set.Ioo (0:ℝ) 1)
    (hx₀irr : Irrational (affineMap q r x₀)) (m : ℕ) :
    ∃ ε > 0, ∀ x : ℝ, |x - x₀| < ε → Irrational (affineMap q r x) →
      affineMap q r x ∈ Set.Ioo (0:ℝ) 1 →
      ∀ i < m, cfDigit (affineMap q r x) i = cfDigit (affineMap q r x₀) i := by
  obtain ⟨εz, hεz, hnhds⟩ := exists_nhds_cfDigit_eq hx₀ hx₀irr m
  refine ⟨εz / q, by positivity, ?_⟩
  intro x hx hxirr hxIoo i hi
  refine hnhds (affineMap q r x) ?_ hxirr hxIoo i hi
  have hqx : q * |x - x₀| < εz := by
    rw [lt_div_iff₀ hq] at hx; nlinarith [hx]
  simp only [affineMap_apply, Set.mem_Ioo]
  constructor <;>
    nlinarith [le_abs_self (x - x₀), neg_abs_le (x - x₀), hqx, hq.le]

/-- **A deep CF-cylinder of an irrational point fits any ball around it (brick-4
refine step).**  Given a genuine word `wx` and an irrational `p ∈ cfCylinder wx`, for
every `ε > 0` there is a strict genuine EXTENSION `wx'` of `wx` (namely `p`'s own
depth-`K` CF word for `K` large) with `p ∈ cfCylinder wx'` and `cfCylinder wx' ⊆
Ioo (p-ε) (p+ε)` — cylinder diameters shrink to `0` (`cfCylinder_subset_Icc_length` +
`volume_cfCylinder_le_fib`).  This is exactly the "refine the `x`-cylinder below the
`exists_ball_cfDigit_psi_eq` ball" move: after refining, every point of `cfCylinder wx'`
maps under `ψ` to within the ball, so shares `ψ(p)`'s first `m` z-digits. -/
theorem exists_cfCylinder_prefix_subset_ball {wx : List ℕ} (hwxne : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) {p : ℝ} (hp : p ∈ cfCylinder wx) (hpirr : Irrational p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ wx' : List ℕ, wx' ≠ [] ∧ (∀ a ∈ wx', 1 ≤ a) ∧ wx'.take wx.length = wx ∧
      wx.length < wx'.length ∧ p ∈ cfCylinder wx' ∧
      cfCylinder wx' ⊆ Set.Ioo (p - ε) (p + ε) := by
  have hp01 : p ∈ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo wx hp
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set K := max (max (wx.length + 1) (n + 1)) 5 with hKdef
  have hKwx : wx.length < K := by omega
  have hK5 : 5 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  set wx' : List ℕ := (List.range K).map (cfDigit p) with hwx'def
  have hwx'len : wx'.length = K := by simp [hwx'def]
  have hwx'ne : wx' ≠ [] := by rw [← List.length_pos_iff_ne_nil, hwx'len]; omega
  have hwx'pos : ∀ a ∈ wx', 1 ≤ a := by
    intro a ha; rw [hwx'def, List.mem_map] at ha; obtain ⟨i, _, rfl⟩ := ha
    exact one_le_cfDigit p hpirr hp01 i
  have hwx'getD : ∀ i, i < K → wx'.getD i 0 = cfDigit p i := by
    intro i hi
    rw [hwx'def, List.getD_eq_getElem _ _ (by simpa [hwx'len] using hi)]
    simp
  have hpmem' : p ∈ cfCylinder wx' := by
    refine ⟨hp01, fun i hi => ?_⟩
    rw [hwx'len] at hi; rw [hwx'getD i hi]
  have htake : wx'.take wx.length = wx :=
    take_eq_of_mem_cfCylinder (by rw [hwx'len]; omega) hp hpmem'
  have hlt : wx.length < wx'.length := by rw [hwx'len]; exact hKwx
  refine ⟨wx', hwx'ne, hwx'pos, htake, hlt, hpmem', ?_⟩
  -- diameter of cfCylinder wx' is < ε, and p is inside it
  obtain ⟨a, c, hIcc, hac⟩ := cfCylinder_subset_Icc_length wx' hwx'ne hwx'pos
  have hvol := volume_cfCylinder_le_fib wx' hwx'ne hwx'pos
  have hfibge : (K : ℝ) ≤ (Nat.fib (wx'.length + 1) : ℝ) := by
    have h1 : wx'.length + 1 ≤ Nat.fib (wx'.length + 1) :=
      Nat.le_fib_self (by rw [hwx'len]; omega)
    exact_mod_cast le_trans (by rw [hwx'len]; omega : K ≤ wx'.length + 1) h1
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdiam : c - a < ε := by
    rw [hac]
    have hle : (volume (cfCylinder wx')).toReal
        ≤ 1 / (Nat.fib (wx'.length + 1) : ℝ) ^ 2 := by
      rw [← ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 / (Nat.fib (wx'.length + 1) : ℝ) ^ 2 by positivity)]
      exact ENNReal.toReal_mono (by simp) hvol
    have hKR : (n : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ K)
    have hK5R : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
    have hfibsq : ((n : ℝ) + 1) ≤ (Nat.fib (wx'.length + 1) : ℝ) ^ 2 := by
      nlinarith [hfibge, hKR, hK5R]
    have hmono : 1 / (Nat.fib (wx'.length + 1) : ℝ) ^ 2 ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hnR hfibsq
    have hlast : 1 / ((n : ℝ) + 1) < ε := by have := hn; push_cast at this; linarith
    linarith
  intro z hz
  have hzIcc := hIcc hz
  have hpIcc := hIcc hpmem'
  rw [Set.mem_Icc] at hzIcc hpIcc
  exact ⟨by linarith [hzIcc.1, hpIcc.2], by linarith [hzIcc.2, hpIcc.1]⟩

/-- **Co-membership in a CF-cylinder pins the leading CF digits.**  Two points of the
same cylinder `cfCylinder w` agree on their first `|w|` CF digits (both spell `w`).
The cylinder-based counterpart of `exists_ball_cfDigit_psi_eq`: when the invariant places
`ψ(cfCylinder wx)` inside a common depth-`m` z-cylinder, `ψ(xA)` and the selected point's
image agree on their first `m` z-digits with no metric ball. -/
theorem cfDigit_eq_of_mem_cfCylinder {w : List ℕ} {x y : ℝ}
    (hx : x ∈ cfCylinder w) (hy : y ∈ cfCylinder w) :
    ∀ i < w.length, cfDigit x i = cfDigit y i := by
  intro i hi
  rw [hx.2 i hi, hy.2 i hi]

/-- **Tail cylinders of a chain enter any ball around the limit (brick 4a).**  If `xA`
lies in every cylinder of a genuine extending chain `w`, then for every `ε>0` all
sufficiently deep cylinders `cfCylinder (w s)` sit inside `Ioo (xA-ε) (xA+ε)` — their
diameters `≤ 1/fib(|w s|+1)²` shrink to `0` (`cfCylinder_subset_Icc_length` +
`volume_cfCylinder_le_fib`).  This is the z-transfer clock: composed with
`exists_ball_cfDigit_psi_eq` at `x₀:=xA`, for large `s` every point of `cfCylinder (w s)`
maps under `ψ` to within the digit-pinning ball around `ψ(xA)`. -/
theorem exists_tail_cfCylinder_subset_ball {w : ℕ → List ℕ}
    (hne : ∀ s, w s ≠ []) (hpos : ∀ s, ∀ a ∈ w s, 1 ≤ a)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    {xA : ℝ} (hxA : ∀ s, xA ∈ cfCylinder (w s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℕ, ∀ s, S ≤ s → cfCylinder (w s) ⊆ Set.Ioo (xA - ε) (xA + ε) := by
  have hlen : ∀ s, s ≤ (w s).length := by
    intro s; induction s with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        obtain ⟨u, hu, heq⟩ := hext k
        rw [heq, List.length_append]
        have : 0 < u.length := List.length_pos_iff.mpr hu
        omega
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨max (N + 1) 5, fun s hs => ?_⟩
  have hs5 : 5 ≤ s := le_trans (le_max_right _ _) hs
  have hsN : N + 1 ≤ s := le_trans (le_max_left _ _) hs
  obtain ⟨a, c, hIcc, hac⟩ := cfCylinder_subset_Icc_length (w s) (hne s) (hpos s)
  have hfibge : (s : ℝ) + 1 ≤ (Nat.fib ((w s).length + 1) : ℝ) := by
    have h1 : (w s).length + 1 ≤ Nat.fib ((w s).length + 1) := Nat.le_fib_self (by have := hlen s; omega)
    have h2 : s + 1 ≤ (w s).length + 1 := by have := hlen s; omega
    exact_mod_cast le_trans h2 h1
  have hsR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hdiam : c - a < ε := by
    rw [hac]
    have hle : (volume (cfCylinder (w s))).toReal
        ≤ 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2 := by
      rw [← ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2 by positivity)]
      exact ENNReal.toReal_mono (by simp) (volume_cfCylinder_le_fib (w s) (hne s) (hpos s))
    have hsNR : (N : ℝ) + 1 ≤ (s : ℝ) + 1 := by exact_mod_cast (by omega : N + 1 ≤ s + 1)
    have hfibsq : ((N : ℝ) + 1) ≤ (Nat.fib ((w s).length + 1) : ℝ) ^ 2 := by
      nlinarith [hfibge, hsNR]
    have hmono : 1 / (Nat.fib ((w s).length + 1) : ℝ) ^ 2 ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hsR hfibsq
    have hlast : 1 / ((N : ℝ) + 1) < ε := by have := hN; push_cast at this; linarith
    linarith
  intro z hz
  have hzIcc := hIcc hz
  have hxAIcc := hIcc (hxA s)
  rw [Set.mem_Icc] at hzIcc hxAIcc
  exact ⟨by linarith [hzIcc.1, hxAIcc.2], by linarith [hzIcc.2, hxAIcc.1]⟩

/-- **Absolute-scale bad-zone avoidance transfers along CF-digit agreement.**  If two
full-orbit reals `z, z'` agree on their first `m` CF digits with `n + |v| ≤ m`, then
avoidance of the ABSOLUTE-scale bad zone `cfBadZone [] v n δ` transfers from `z'` to `z`
(the membership reads only `blockCount (cfCylinder v) n`, which
`blockCount_eq_of_cfDigit_agree` pins to be equal).  This is the final z-transfer step:
the brick-3′ point `z' = ψ(p)` avoids the stage's z-bad zone, and once the `x`-cylinder is
refined below `exists_ball_cfDigit_psi_eq`'s ball the chain limit `z = ψ(xA)` agrees with
it on the first `m` z-digits, hence inherits the avoidance. -/
theorem notMem_cfBadZone_nil_of_cfDigit_agree {z z' : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] z ∈ Set.Ioo (0 : ℝ) 1)
    (horb' : ∀ j : ℕ, gaussMap^[j] z' ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (n m : ℕ) (δ : ℝ) (hm : n + v.length ≤ m)
    (hagree : ∀ i < m, cfDigit z i = cfDigit z' i)
    (hz' : z' ∉ cfBadZone [] v n δ) : z ∉ cfBadZone [] v n δ := by
  intro hz
  apply hz'
  have hbc : blockCount (cfCylinder v) n z = blockCount (cfCylinder v) n z' :=
    blockCount_eq_of_cfDigit_agree horb horb' v n m hm hagree
  have hz'01 : z' ∈ Set.Ioo (0 : ℝ) 1 := by simpa using horb' 0
  rw [cfBadZone, cfCylinder_nil, List.length_nil, Function.iterate_zero,
    Set.preimage_id] at hz ⊢
  obtain ⟨-, -, hzdisc⟩ := hz
  exact ⟨hz'01, hz'01, by rwa [hbc] at hzdisc⟩

/-- **Multi-scale + cfK measure core** (the cfK-steer selection).  Like
`exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`, but the aggregate bound
`hbound` additionally leaves room for the cfK-large extension mass
`(gaussMeasure (cfKbadExtSet wx κ ntop)).toReal`, so the returned point is BOTH
freq-good at every scale in `NS` AND has a `cfK ≤ e^{κ·ntop}` extension past `wx`.
Combines `gaussMeasure_multiscale_cfBadZone_le` (bad-zone mass) with the packaged
`exists_rate_gaussMeasure_cfKbadExtSet_le` bound (the caller instantiates `κ`),
then extracts an irrational point via
`exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` with `B' = (bad) ∪ (cfK
large)`.  This is the selection at the heart of the (resolved) cfK-steer route for
`schedA_block_linear`. -/
theorem exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo
    (wx : List ℕ) (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ : ℝ} (hδ : 0 < δ) {c d : ℝ}
    (NS : Finset ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁) (hNS : ∀ n ∈ NS, n₁ ≤ n)
    (κ : ℝ) (ntop : ℕ)
    (hbound : (NS.card : ℝ) * (∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal)
        + (gaussMeasure (cfKbadExtSet wx κ ntop)).toReal
        < (gaussMeasure (Set.Ioo c d)).toReal) :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo c d ∧
      x ∉ (⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone wx v n δ) ∧
      x ∉ cfKbadExtSet wx κ ntop := by
  have hbad := gaussMeasure_multiscale_cfBadZone_le wx hwxpos F hF NS hn₁ hNS hδ
  set Bbad : Set ℝ := ⋃ n ∈ NS, ⋃ v ∈ F, cfBadZone wx v n δ with hBbad
  set S : Set ℝ := cfKbadExtSet wx κ ntop with hS
  have hBfin : gaussMeasure Bbad ≠ ⊤ := measure_ne_top _ _
  have hSfin : gaussMeasure S ≠ ⊤ := measure_ne_top _ _
  have hIfin : gaussMeasure (Set.Ioo c d) ≠ ⊤ := measure_ne_top _ _
  have hsumfin : gaussMeasure Bbad + gaussMeasure S ≠ ⊤ := by
    rw [ENNReal.add_ne_top]; exact ⟨hBfin, hSfin⟩
  have hunion_lt : gaussMeasure (Bbad ∪ S) < gaussMeasure (Set.Ioo c d) := by
    have hlt_toReal : (gaussMeasure Bbad + gaussMeasure S).toReal
        < (gaussMeasure (Set.Ioo c d)).toReal := by
      rw [ENNReal.toReal_add hBfin hSfin]; linarith [hbad, hbound]
    calc gaussMeasure (Bbad ∪ S)
        ≤ gaussMeasure Bbad + gaussMeasure S := measure_union_le _ _
      _ < gaussMeasure (Set.Ioo c d) := (ENNReal.toReal_lt_toReal hsumfin hIfin).mp hlt_toReal
  obtain ⟨x, hirr, hxI, hxni⟩ :=
    exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt (Bbad ∪ S) hunion_lt
  exact ⟨x, hirr, hxI, fun h => hxni (Or.inl h), fun h => hxni (Or.inr h)⟩

/-- **The STEERABLE frequency-good block (B6 crux, filler-free).**  Given a
genuine base `wx`, family `F`, tolerance `δ`, length target `L`, and a target
interval `(c,d)` all of whose irrationals lie in `cfCylinder wx`, there is a
SINGLE block `u` (`|u| ≥ L`, genuine, `δ`-frequency-good for every `v ∈ F`) with
`cfCylinder (wx ++ u) ⊆ (c,d)` — the WHOLE block is freq-good AND it steers into
the target, with NO uncontrolled placement prefix.  This is what the earlier
`exists_freq_good_block_in_Ioo` could not give (its `w`-prefix is uncontrolled):
the crux the interleaved schedule needs so each stream's appended block is a
single margin-good chunk feeding the EXISTING `chain_orbit_equidist`.  Wraps the
measure core `exists_irrational_notMem_cfBadZone_in_Ioo` (an irrational point of a
`⊂⊂`-buffered subinterval avoiding all bad zones), reads off its digit block, and
uses the vanishing cylinder width to land the whole cylinder inside `(c,d)`. -/
theorem exists_freq_good_block_steer (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx) (L : ℕ) :
    ∃ u : List ℕ, u ≠ [] ∧ L ≤ u.length ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      (∀ v ∈ F, |(countOccurrences v u : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  -- interval-measure positivity for nondegenerate subintervals of (0,1)
  have hμpos : ∀ p q : ℝ, 0 ≤ p → p < q → q ≤ 1 →
      0 < (gaussMeasure (Set.Ioo p q)).toReal := by
    intro p q hp hpq hq
    have hlp : Real.log (1 + p) < Real.log (1 + q) :=
      Real.log_lt_log (by linarith) (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : 0 < (Real.log (1 + q) - Real.log (1 + p)) / Real.log 2 :=
      div_pos (by linarith) hl2
    rw [gaussMeasure_Ioo hp hpq.le hq, ENNReal.toReal_ofReal harg.le]
    exact harg
  -- buffered target (c', d') ⊂⊂ (c, d)
  set β : ℝ := (d - c) / 4 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set c' : ℝ := c + β with hc'
  set d' : ℝ := d - β with hd'
  have hcc' : c < c' := by rw [hc']; linarith
  have hc'd' : c' < d' := by rw [hc', hd', hβ]; linarith
  have hd'd : d' < d := by rw [hd']; linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hd'1 : d' ≤ 1 := by rw [hd']; linarith
  have hμc'd' : 0 < (gaussMeasure (Set.Ioo c' d')).toReal := hμpos c' d' hc'0 hc'd' hd'1
  -- measure core on (c', d') + fib threshold for cylinder width < β
  obtain ⟨N0, hN0⟩ :=
    exists_irrational_notMem_cfBadZone_in_Ioo wx hwx hwxpos F hF hδ (c := c') (d := d') hμc'd'
  obtain ⟨N1, hN1⟩ := exists_fib_threshold (1 / β)
  set n : ℕ := max (max N0 N1) (max L 1) + 1 with hndef
  have hnN0 : N0 ≤ n := by
    rw [hndef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hnN1 : N1 ≤ n := by
    rw [hndef]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_succ _)
  have hnL : L ≤ n := by
    rw [hndef]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_succ _)
  have hn1 : 1 ≤ n := by
    rw [hndef]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_succ _)
  have hn0 : 0 < n := hn1
  obtain ⟨x, hirr, hxc'd', hxnot⟩ := hN0 n hnN0 hn0
  -- x lands in (c,d) hence in cfCylinder wx
  have hxcd : x ∈ Set.Ioo c d := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hxc'd'
    exact Set.mem_Ioo.2 ⟨lt_trans hcc' h1, lt_trans h2 hd'd⟩
  have hxwx : x ∈ cfCylinder wx := hsub x hxcd hirr
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := hxwx.1
  -- the digit block
  set u : List ℕ := (List.range n).map (fun i => cfDigit x (wx.length + i)) with hudef
  have hulen : u.length = n := by rw [hudef, List.length_map, List.length_range]
  have hune : u ≠ [] := by
    intro h; rw [h] at hulen; simp only [List.length_nil] at hulen; omega
  have hupos : ∀ a ∈ u, 1 ≤ a := by
    intro a ha
    rw [hudef, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit x hirr hx01 _
  -- x ∈ cfCylinder (wx ++ u): the length-(|wx|+n) digit prefix of x IS wx ++ u
  have hxcyl : x ∈ cfCylinder (wx ++ u) := by
    refine ⟨hx01, fun i hi => ?_⟩
    rw [List.length_append, hulen] at hi
    rcases lt_or_ge i wx.length with hlt | hge
    · rw [List.getD_append wx u 0 i hlt]
      exact hxwx.2 i hlt
    · rw [List.getD_append_right wx u 0 i hge, hudef]
      have hidx : i - wx.length < n := by omega
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hidx),
        List.getElem_map, List.getElem_range]
      congr 1
      omega
  -- cylinder width < β, hence cfCylinder (wx ++ u) ⊆ (c, d)
  have hsubcd : cfCylinder (wx ++ u) ⊆ Set.Ioo c d := by
    obtain ⟨aC, cC, hIcc, hwidth⟩ :=
      cfCylinder_subset_Icc_length (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
    have hvol : (volume (cfCylinder (wx ++ u))).toReal
        ≤ 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hb := volume_cfCylinder_le_fib (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
      calc (volume (cfCylinder (wx ++ u))).toReal
          ≤ (ENNReal.ofReal (1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
        _ = 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 :=
            ENNReal.toReal_ofReal (by positivity)
    have hfibgt : 1 / β < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hle : N1 ≤ (wx ++ u).length := by rw [List.length_append, hulen]; omega
      exact hN1 (wx ++ u).length hle
    have hfibpos : (0 : ℝ) < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have : 0 < Nat.fib ((wx ++ u).length + 1) := Nat.fib_pos.2 (by omega); positivity
    have hwlt : (volume (cfCylinder (wx ++ u))).toReal < β := by
      have h1 : 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 < β := by
        rw [div_lt_iff₀ hfibpos]
        rw [div_lt_iff₀ hβ0] at hfibgt
        nlinarith [hfibgt]
      linarith [hvol, h1]
    rw [← hwidth] at hwlt
    have hxIcc := hIcc hxcyl
    obtain ⟨haC, hcC⟩ := Set.mem_Icc.1 hxIcc
    obtain ⟨hxc, hxd⟩ := Set.mem_Ioo.1 hxc'd'
    intro y hy
    obtain ⟨hya, hyc⟩ := Set.mem_Icc.1 (hIcc hy)
    refine Set.mem_Ioo.2 ⟨?_, ?_⟩
    · have : c < aC := by
        have : x - β < aC := by linarith [hcC, hwlt]
        linarith [hxc]
      linarith
    · have : cC < d := by
        have : cC < x + β := by linarith [haC, hwlt]
        linarith [hxd]
      linarith
  -- frequency-goodness of the whole block u (copy of exists_freq_good_block)
  have hfreq : ∀ v ∈ F, |(countOccurrences v u : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length := by
    have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
      fun j => (irrational_orbit x hirr hxwx.1 j).2
    intro v hv
    have hnotCF : x ∉ cfBadZone wx v n δ :=
      fun h => hxnot (Set.mem_biUnion hv h)
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxwx hirr hnotCF
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv) wx.length n
    have hword : (List.range n).map (fun i => cfDigit x (wx.length + i)) = u := hudef.symm
    rw [hword] at hbr
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[wx.length] x) with hbc
    set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have habs' : |bc - γv * n| < δ * n := by
      have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
      rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
      linarith [habs]
    rw [hulen]
    rw [abs_lt] at habs' ⊢
    have hv0 : (0 : ℝ) ≤ v.length := by positivity
    constructor
    · linarith
    · linarith
  exact ⟨u, hune, hulen ▸ hnL, hupos, hsubcd, hfreq, x, hxcyl, hirr, hxcd⟩

/-- **Tight-length steerable freq-good block.**  Same as `exists_freq_good_block_steer`
but the block length is the CALLER's explicit `n` (given the resolution hypothesis
`4/(d-c) < fib(|wx|+n+1)²`), and the measure-core threshold `N0` is EXPOSED.  This
lets the interleaved schedule pick `n` logarithmic in the target width (via
`fib_sq_gt_of_goldenRatio`/`exists_nat_goldenRatio_pow_gt`), the control `hdom`
needs. -/
theorem exists_freq_good_block_steer_len (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → 1 ≤ n →
      (4 / (d - c) < (Nat.fib (wx.length + n + 1) : ℝ) ^ 2) →
      ∃ u : List ℕ, u.length = n ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
        cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
        (∀ v ∈ F, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length) ∧
        ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  have hμpos : ∀ p q : ℝ, 0 ≤ p → p < q → q ≤ 1 →
      0 < (gaussMeasure (Set.Ioo p q)).toReal := by
    intro p q hp hpq hq
    have hlp : Real.log (1 + p) < Real.log (1 + q) :=
      Real.log_lt_log (by linarith) (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : 0 < (Real.log (1 + q) - Real.log (1 + p)) / Real.log 2 :=
      div_pos (by linarith) hl2
    rw [gaussMeasure_Ioo hp hpq.le hq, ENNReal.toReal_ofReal harg.le]
    exact harg
  -- buffered target (c', d') ⊂⊂ (c, d)
  set β : ℝ := (d - c) / 4 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set c' : ℝ := c + β with hc'
  set d' : ℝ := d - β with hd'
  have hcc' : c < c' := by rw [hc']; linarith
  have hc'd' : c' < d' := by rw [hc', hd', hβ]; linarith
  have hd'd : d' < d := by rw [hd']; linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hd'1 : d' ≤ 1 := by rw [hd']; linarith
  have hμc'd' : 0 < (gaussMeasure (Set.Ioo c' d')).toReal := hμpos c' d' hc'0 hc'd' hd'1
  obtain ⟨N0, hN0⟩ :=
    exists_irrational_notMem_cfBadZone_in_Ioo wx hwx hwxpos F hF hδ (c := c') (d := d') hμc'd'
  refine ⟨N0, fun n hnN0 hn1 hres => ?_⟩
  have hn0 : 0 < n := hn1
  obtain ⟨x, hirr, hxc'd', hxnot⟩ := hN0 n hnN0 hn0
  -- x lands in (c,d) hence in cfCylinder wx
  have hxcd : x ∈ Set.Ioo c d := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hxc'd'
    exact Set.mem_Ioo.2 ⟨lt_trans hcc' h1, lt_trans h2 hd'd⟩
  have hxwx : x ∈ cfCylinder wx := hsub x hxcd hirr
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := hxwx.1
  set u : List ℕ := (List.range n).map (fun i => cfDigit x (wx.length + i)) with hudef
  have hulen : u.length = n := by rw [hudef, List.length_map, List.length_range]
  have hune : u ≠ [] := by
    intro h; rw [h] at hulen; simp only [List.length_nil] at hulen; omega
  have hupos : ∀ a ∈ u, 1 ≤ a := by
    intro a ha
    rw [hudef, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit x hirr hx01 _
  have hxcyl : x ∈ cfCylinder (wx ++ u) := by
    refine ⟨hx01, fun i hi => ?_⟩
    rw [List.length_append, hulen] at hi
    rcases lt_or_ge i wx.length with hlt | hge
    · rw [List.getD_append wx u 0 i hlt]
      exact hxwx.2 i hlt
    · rw [List.getD_append_right wx u 0 i hge, hudef]
      have hidx : i - wx.length < n := by omega
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hidx),
        List.getElem_map, List.getElem_range]
      congr 1
      omega
  have hsubcd : cfCylinder (wx ++ u) ⊆ Set.Ioo c d := by
    obtain ⟨aC, cC, hIcc, hwidth⟩ :=
      cfCylinder_subset_Icc_length (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
    have hvol : (volume (cfCylinder (wx ++ u))).toReal
        ≤ 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hb := volume_cfCylinder_le_fib (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
      calc (volume (cfCylinder (wx ++ u))).toReal
          ≤ (ENNReal.ofReal (1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
        _ = 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 :=
            ENNReal.toReal_ofReal (by positivity)
    have hfibgt : 1 / β < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hidx : (wx ++ u).length + 1 = wx.length + n + 1 := by
        rw [List.length_append, hulen]
      rw [hidx]
      have h1β : 1 / β = 4 / (d - c) := by rw [hβ]; rw [one_div_div]
      rw [h1β]; exact hres
    have hfibpos : (0 : ℝ) < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have : 0 < Nat.fib ((wx ++ u).length + 1) := Nat.fib_pos.2 (by omega); positivity
    have hwlt : (volume (cfCylinder (wx ++ u))).toReal < β := by
      have h1 : 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 < β := by
        rw [div_lt_iff₀ hfibpos]
        rw [div_lt_iff₀ hβ0] at hfibgt
        nlinarith [hfibgt]
      linarith [hvol, h1]
    rw [← hwidth] at hwlt
    have hxIcc := hIcc hxcyl
    obtain ⟨haC, hcC⟩ := Set.mem_Icc.1 hxIcc
    obtain ⟨hxc, hxd⟩ := Set.mem_Ioo.1 hxc'd'
    intro y hy
    obtain ⟨hya, hyc⟩ := Set.mem_Icc.1 (hIcc hy)
    refine Set.mem_Ioo.2 ⟨?_, ?_⟩
    · have : c < aC := by
        have : x - β < aC := by linarith [hcC, hwlt]
        linarith [hxc]
      linarith
    · have : cC < d := by
        have : cC < x + β := by linarith [haC, hwlt]
        linarith [hxd]
      linarith
  have hfreq : ∀ v ∈ F, |(countOccurrences v u : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * u.length| < δ * u.length + v.length := by
    have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
      fun j => (irrational_orbit x hirr hxwx.1 j).2
    intro v hv
    have hnotCF : x ∉ cfBadZone wx v n δ :=
      fun h => hxnot (Set.mem_biUnion hv h)
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxwx hirr hnotCF
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv) wx.length n
    have hword : (List.range n).map (fun i => cfDigit x (wx.length + i)) = u := hudef.symm
    rw [hword] at hbr
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[wx.length] x) with hbc
    set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have habs' : |bc - γv * n| < δ * n := by
      have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
      rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
      linarith [habs]
    rw [hulen]
    rw [abs_lt] at habs' ⊢
    have hv0 : (0 : ℝ) ≤ v.length := by positivity
    constructor
    · linarith
    · linarith
  exact ⟨u, hulen, hune, hupos, hsubcd, hfreq, x, hxcyl, hirr, hxcd⟩

/-- **Multi-scale (per-scale) uniformly-good steerable block.**  Like
`exists_freq_good_block_steer_len`, but the freq-goodness holds at EVERY scale
`n ∈ NS` on the prefix `u.take n` (not merely on the whole block), because the
underlying point avoids the bad zones at all scales simultaneously.  With
quadratically-spaced `NS` this is the raw material for uniform-prefix-goodness:
every prefix length interpolates between two adjacent scales in `NS`.  The block
length is the top scale `NS.max'`; the caller supplies the resolution hypothesis
and the multi-scale measure bound (against the buffered target `(c', d')`). -/
theorem exists_multiscale_freq_good_block_steer_len (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx)
    (NS : Finset ℕ) (hNSne : NS.Nonempty) {n₁ : ℕ} (hn₁ : 0 < n₁)
    (hNS : ∀ n ∈ NS, n₁ ≤ n)
    (hbound : (NS.card : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal))
        < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal)
    (hres : 4 / (d - c) < (Nat.fib (wx.length + NS.max' hNSne + 1) : ℝ) ^ 2) :
    ∃ u : List ℕ, u.length = NS.max' hNSne ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      (∀ n ∈ NS, ∀ v ∈ F, |(countOccurrences v (u.take n) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  set ntop := NS.max' hNSne with hntopdef
  have hn₁top : n₁ ≤ ntop := hNS ntop (NS.max'_mem hNSne)
  have hntop0 : 0 < ntop := lt_of_lt_of_le hn₁ hn₁top
  -- buffered target (c', d') ⊂⊂ (c, d)
  set β : ℝ := (d - c) / 4 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set c' : ℝ := c + β with hc'
  set d' : ℝ := d - β with hd'
  have hcc' : c < c' := by rw [hc']; linarith
  have hc'd' : c' < d' := by rw [hc', hd', hβ]; linarith
  have hd'd : d' < d := by rw [hd']; linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hd'1 : d' ≤ 1 := by rw [hd']; linarith
  have hμc'd' : 0 < (gaussMeasure (Set.Ioo c' d')).toReal := by
    have hlp : Real.log (1 + c') < Real.log (1 + d') :=
      Real.log_lt_log (by linarith) (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : 0 < (Real.log (1 + d') - Real.log (1 + c')) / Real.log 2 :=
      div_pos (by linarith) hl2
    rw [gaussMeasure_Ioo hc'0 hc'd'.le hd'1, ENNReal.toReal_ofReal harg.le]
    exact harg
  -- multi-scale core on (c', d')
  obtain ⟨x, hirr, hxc'd', hxnot⟩ :=
    exists_irrational_notMem_multiscale_cfBadZone_in_Ioo wx hwxpos F hF hδ
      (c := c') (d := d') hμc'd' NS hn₁ hNS (by rw [hc', hd']; exact hbound)
  -- x lands in (c,d) hence in cfCylinder wx
  have hxcd : x ∈ Set.Ioo c d := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hxc'd'
    exact Set.mem_Ioo.2 ⟨lt_trans hcc' h1, lt_trans h2 hd'd⟩
  have hxwx : x ∈ cfCylinder wx := hsub x hxcd hirr
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := hxwx.1
  set u : List ℕ := (List.range ntop).map (fun i => cfDigit x (wx.length + i)) with hudef
  have hulen : u.length = ntop := by rw [hudef, List.length_map, List.length_range]
  have hune : u ≠ [] := by
    intro h; rw [h] at hulen; simp only [List.length_nil] at hulen; omega
  have hupos : ∀ a ∈ u, 1 ≤ a := by
    intro a ha
    rw [hudef, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit x hirr hx01 _
  have hxcyl : x ∈ cfCylinder (wx ++ u) := by
    refine ⟨hx01, fun i hi => ?_⟩
    rw [List.length_append, hulen] at hi
    rcases lt_or_ge i wx.length with hlt | hge
    · rw [List.getD_append wx u 0 i hlt]
      exact hxwx.2 i hlt
    · rw [List.getD_append_right wx u 0 i hge, hudef]
      have hidx : i - wx.length < ntop := by omega
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hidx),
        List.getElem_map, List.getElem_range]
      congr 1
      omega
  have hsubcd : cfCylinder (wx ++ u) ⊆ Set.Ioo c d := by
    obtain ⟨aC, cC, hIcc, hwidth⟩ :=
      cfCylinder_subset_Icc_length (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
    have hvol : (volume (cfCylinder (wx ++ u))).toReal
        ≤ 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hb := volume_cfCylinder_le_fib (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
      calc (volume (cfCylinder (wx ++ u))).toReal
          ≤ (ENNReal.ofReal (1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
        _ = 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 :=
            ENNReal.toReal_ofReal (by positivity)
    have hfibgt : 1 / β < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hidx : (wx ++ u).length + 1 = wx.length + ntop + 1 := by
        rw [List.length_append, hulen]
      rw [hidx]
      have h1β : 1 / β = 4 / (d - c) := by rw [hβ]; rw [one_div_div]
      rw [h1β]; exact hres
    have hfibpos : (0 : ℝ) < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have : 0 < Nat.fib ((wx ++ u).length + 1) := Nat.fib_pos.2 (by omega); positivity
    have hwlt : (volume (cfCylinder (wx ++ u))).toReal < β := by
      have h1 : 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 < β := by
        rw [div_lt_iff₀ hfibpos]
        rw [div_lt_iff₀ hβ0] at hfibgt
        nlinarith [hfibgt]
      linarith [hvol, h1]
    rw [← hwidth] at hwlt
    have hxIcc := hIcc hxcyl
    obtain ⟨haC, hcC⟩ := Set.mem_Icc.1 hxIcc
    obtain ⟨hxc, hxd⟩ := Set.mem_Ioo.1 hxc'd'
    intro y hy
    obtain ⟨hya, hyc⟩ := Set.mem_Icc.1 (hIcc hy)
    refine Set.mem_Ioo.2 ⟨?_, ?_⟩
    · have : c < aC := by
        have : x - β < aC := by linarith [hcC, hwlt]
        linarith [hxc]
      linarith
    · have : cC < d := by
        have : cC < x + β := by linarith [haC, hwlt]
        linarith [hxd]
      linarith
  -- per-scale freq-goodness of every prefix u.take n, n ∈ NS
  have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
    fun j => (irrational_orbit x hirr hxwx.1 j).2
  have hfreqNS : ∀ n ∈ NS, ∀ v ∈ F, |(countOccurrences v (u.take n) : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length := by
    intro n hnNS v hv
    have hnn1 : n₁ ≤ n := hNS n hnNS
    have hn0' : 0 < n := lt_of_lt_of_le hn₁ hnn1
    have hntop : n ≤ ntop := NS.le_max' n hnNS
    have hutaken : u.take n = (List.range n).map (fun i => cfDigit x (wx.length + i)) := by
      rw [hudef, ← List.map_take, List.take_range, Nat.min_eq_left hntop]
    rw [hutaken]
    have hnotCF : x ∉ cfBadZone wx v n δ :=
      fun h => hxnot (Set.mem_biUnion hnNS (Set.mem_biUnion hv h))
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxwx hirr hnotCF
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv) wx.length n
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[wx.length] x) with hbc
    set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0'
    have habs' : |bc - γv * n| < δ * n := by
      have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
      rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
      linarith [habs]
    rw [abs_lt] at habs' ⊢
    have hv0 : (0 : ℝ) ≤ v.length := by positivity
    constructor
    · linarith
    · linarith
  exact ⟨u, hulen, hune, hupos, hsubcd, hfreqNS, x, hxcyl, hirr, hxcd⟩

/-- **cfK-cap bridge.**  A point `x` avoiding the cfK-large extension set
`cfKbadExtSet wx κ ntop` and lying in `cfCylinder (wx ++ u)` for a genuine block `u`
of length `ntop` HAS a cfK-capped block: `cfK u ≤ e^{κ·ntop}`.  (Else `u ∈ genWords ntop`
with `cfK u > e^{κ·ntop}` would put `x` in the else-branch `cfCylinder (wx ++ u)` of the
bad-set union.)  This is the sole cfK step: the whole block-builder chain reads `u` off
`x`'s digits, so grafting the cfK cap reduces to swapping the selection core for its
cfK-aware variant (`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo`) and
invoking this bridge. -/
theorem cfK_le_of_notMem_cfKbadExtSet {wx u : List ℕ} {κ : ℝ} {ntop : ℕ}
    (hulen : u.length = ntop) (hupos : ∀ a ∈ u, 1 ≤ a) {x : ℝ}
    (hxcyl : x ∈ cfCylinder (wx ++ u)) (hxni : x ∉ cfKbadExtSet wx κ ntop) :
    (cfK u : ℝ) ≤ Real.exp (κ * ntop) := by
  by_contra h
  apply hxni
  rw [cfKbadExtSet, Set.mem_iUnion₂]
  exact ⟨u, ⟨hulen, hupos⟩, by rw [if_neg h]; exact hxcyl⟩

/-- **Multi-scale steer block with a cfK cap** (cfK-graft layer 1).  Identical to
`exists_multiscale_freq_good_block_steer_len`, but the aggregate `hbound` additionally
leaves room for the cfK-large extension mass at relative order `NS.max' hNSne`, and the
conclusion EXPOSES `cfK u ≤ e^{κ·|u|}` — the Lévy-uniform bound (`exists_rate_gaussMeasure_cfKbadExtSet_le`
supplies the rate `κ`) that turns the resolution `Nfib` AFFINE in `|wx|`
(`exists_fib_threshold_linear_of_cfK`).  Swaps the selection core for its cfK-aware form
and reads the cap off the bridge `cfK_le_of_notMem_cfKbadExtSet`. -/
theorem exists_multiscale_freq_good_block_steer_len_cfK (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx)
    (NS : Finset ℕ) (hNSne : NS.Nonempty) {n₁ : ℕ} (hn₁ : 0 < n₁)
    (hNS : ∀ n ∈ NS, n₁ ≤ n) (κ : ℝ)
    (hbound : (NS.card : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal))
        + (gaussMeasure (cfKbadExtSet wx κ (NS.max' hNSne))).toReal
        < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal)
    (hres : 4 / (d - c) < (Nat.fib (wx.length + NS.max' hNSne + 1) : ℝ) ^ 2) :
    ∃ u : List ℕ, u.length = NS.max' hNSne ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      (∀ n ∈ NS, ∀ v ∈ F, |(countOccurrences v (u.take n) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
      (cfK u : ℝ) ≤ Real.exp (κ * (u.length : ℝ)) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  set ntop := NS.max' hNSne with hntopdef
  have hn₁top : n₁ ≤ ntop := hNS ntop (NS.max'_mem hNSne)
  have hntop0 : 0 < ntop := lt_of_lt_of_le hn₁ hn₁top
  set β : ℝ := (d - c) / 4 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set c' : ℝ := c + β with hc'
  set d' : ℝ := d - β with hd'
  have hcc' : c < c' := by rw [hc']; linarith
  have hc'd' : c' < d' := by rw [hc', hd', hβ]; linarith
  have hd'd : d' < d := by rw [hd']; linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hd'1 : d' ≤ 1 := by rw [hd']; linarith
  -- multi-scale + cfK core on (c', d')
  obtain ⟨x, hirr, hxc'd', hxnot, hxnicfK⟩ :=
    exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo wx hwxpos F hF hδ
      (c := c') (d := d') NS hn₁ hNS κ ntop (by rw [hc', hd']; exact hbound)
  have hxcd : x ∈ Set.Ioo c d := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hxc'd'
    exact Set.mem_Ioo.2 ⟨lt_trans hcc' h1, lt_trans h2 hd'd⟩
  have hxwx : x ∈ cfCylinder wx := hsub x hxcd hirr
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := hxwx.1
  set u : List ℕ := (List.range ntop).map (fun i => cfDigit x (wx.length + i)) with hudef
  have hulen : u.length = ntop := by rw [hudef, List.length_map, List.length_range]
  have hune : u ≠ [] := by
    intro h; rw [h] at hulen; simp only [List.length_nil] at hulen; omega
  have hupos : ∀ a ∈ u, 1 ≤ a := by
    intro a ha
    rw [hudef, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact one_le_cfDigit x hirr hx01 _
  have hxcyl : x ∈ cfCylinder (wx ++ u) := by
    refine ⟨hx01, fun i hi => ?_⟩
    rw [List.length_append, hulen] at hi
    rcases lt_or_ge i wx.length with hlt | hge
    · rw [List.getD_append wx u 0 i hlt]
      exact hxwx.2 i hlt
    · rw [List.getD_append_right wx u 0 i hge, hudef]
      have hidx : i - wx.length < ntop := by omega
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hidx),
        List.getElem_map, List.getElem_range]
      congr 1
      omega
  have hsubcd : cfCylinder (wx ++ u) ⊆ Set.Ioo c d := by
    obtain ⟨aC, cC, hIcc, hwidth⟩ :=
      cfCylinder_subset_Icc_length (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
    have hvol : (volume (cfCylinder (wx ++ u))).toReal
        ≤ 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hb := volume_cfCylinder_le_fib (wx ++ u) (by simp [hwx]) (fun a ha =>
        (List.mem_append.1 ha).elim (hwxpos a) (hupos a))
      calc (volume (cfCylinder (wx ++ u))).toReal
          ≤ (ENNReal.ofReal (1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
        _ = 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 :=
            ENNReal.toReal_ofReal (by positivity)
    have hfibgt : 1 / β < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have hidx : (wx ++ u).length + 1 = wx.length + ntop + 1 := by
        rw [List.length_append, hulen]
      rw [hidx]
      have h1β : 1 / β = 4 / (d - c) := by rw [hβ]; rw [one_div_div]
      rw [h1β]; exact hres
    have hfibpos : (0 : ℝ) < (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 := by
      have : 0 < Nat.fib ((wx ++ u).length + 1) := Nat.fib_pos.2 (by omega); positivity
    have hwlt : (volume (cfCylinder (wx ++ u))).toReal < β := by
      have h1 : 1 / (Nat.fib ((wx ++ u).length + 1) : ℝ) ^ 2 < β := by
        rw [div_lt_iff₀ hfibpos]
        rw [div_lt_iff₀ hβ0] at hfibgt
        nlinarith [hfibgt]
      linarith [hvol, h1]
    rw [← hwidth] at hwlt
    have hxIcc := hIcc hxcyl
    obtain ⟨haC, hcC⟩ := Set.mem_Icc.1 hxIcc
    obtain ⟨hxc, hxd⟩ := Set.mem_Ioo.1 hxc'd'
    intro y hy
    obtain ⟨hya, hyc⟩ := Set.mem_Icc.1 (hIcc hy)
    refine Set.mem_Ioo.2 ⟨?_, ?_⟩
    · have : c < aC := by
        have : x - β < aC := by linarith [hcC, hwlt]
        linarith [hxc]
      linarith
    · have : cC < d := by
        have : cC < x + β := by linarith [haC, hwlt]
        linarith [hxd]
      linarith
  have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
    fun j => (irrational_orbit x hirr hxwx.1 j).2
  have hfreqNS : ∀ n ∈ NS, ∀ v ∈ F, |(countOccurrences v (u.take n) : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length := by
    intro n hnNS v hv
    have hnn1 : n₁ ≤ n := hNS n hnNS
    have hn0' : 0 < n := lt_of_lt_of_le hn₁ hnn1
    have hntop : n ≤ ntop := NS.le_max' n hnNS
    have hutaken : u.take n = (List.range n).map (fun i => cfDigit x (wx.length + i)) := by
      rw [hudef, ← List.map_take, List.take_range, Nat.min_eq_left hntop]
    rw [hutaken]
    have hnotCF : x ∉ cfBadZone wx v n δ :=
      fun h => hxnot (Set.mem_biUnion hnNS (Set.mem_biUnion hv h))
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxwx hirr hnotCF
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv) wx.length n
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[wx.length] x) with hbc
    set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0'
    have habs' : |bc - γv * n| < δ * n := by
      have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
      rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
      linarith [habs]
    rw [abs_lt] at habs' ⊢
    have hv0 : (0 : ℝ) ≤ v.length := by positivity
    constructor
    · linarith
    · linarith
  have hcfKu : (cfK u : ℝ) ≤ Real.exp (κ * (u.length : ℝ)) := by
    have := cfK_le_of_notMem_cfKbadExtSet hulen hupos hxcyl hxnicfK
    rwa [hulen]
  exact ⟨u, hulen, hune, hupos, hsubcd, hfreqNS, hcfKu, x, hxcyl, hirr, hxcd⟩

/-- **Prefix-frequency interpolation.**  If the frequency deviation of `v` is
controlled at prefix length `n`, it is controlled at any larger prefix length
`k ≤ |u|`, up to an additive `2(k−n) + |v|`.  (`countOccurrences` is monotone in
the prefix and grows by at most `1` per position, plus a `|v|−1` seam term.)  With
quadratically-spaced good scales `n`, the gap `k−n = o(k)`, so every prefix is
good — the hdom-free replacement for block-shortness. -/
theorem abs_countOccurrences_take_interp {v u : List ℕ} (hv : v ≠ []) {γv : ℝ}
    (hγ0 : 0 ≤ γv) (hγ1 : γv ≤ 1) {n k : ℕ} (hnk : n ≤ k) (hku : k ≤ u.length) :
    |(countOccurrences v (u.take k) : ℝ) - γv * k|
      ≤ |(countOccurrences v (u.take n) : ℝ) - γv * n| + 2 * ((k : ℝ) - n)
        + v.length := by
  set rest : List ℕ := (u.take k).drop n with hrest
  have hsplit : u.take n ++ rest = u.take k := by
    have h1 : (u.take k).take n = u.take n := by
      rw [List.take_take, Nat.min_eq_left hnk]
    rw [hrest, ← h1, List.take_append_drop]
  have hlenk : (u.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hku]
  have hlenrest : rest.length = k - n := by
    rw [hrest, List.length_drop, hlenk]
  -- (A) monotone: Cn ≤ Ck
  have hA : countOccurrences v (u.take n) ≤ countOccurrences v (u.take k) := by
    have := add_countOccurrences_le_append hv (u.take n) rest
    rw [hsplit] at this
    omega
  -- (B) increment ≤ (k-n) + (|v|-1)
  have hB : countOccurrences v (u.take k)
      ≤ countOccurrences v (u.take n) + (k - n) + (v.length - 1) := by
    have hle := countOccurrences_append_le hv (u.take n) rest
    rw [hsplit] at hle
    have hrl := countOccurrences_le_length hv rest
    rw [hlenrest] at hrl
    omega
  -- cast to reals
  set Cn : ℝ := (countOccurrences v (u.take n) : ℝ) with hCn
  set Ck : ℝ := (countOccurrences v (u.take k) : ℝ) with hCk
  have hAR : Cn ≤ Ck := by rw [hCn, hCk]; exact_mod_cast hA
  have hnkR : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hknR : (0 : ℝ) ≤ (k : ℝ) - n := by linarith
  have hv1R : (1 : ℝ) ≤ v.length := by exact_mod_cast List.length_pos_of_ne_nil hv
  have hv1 : 1 ≤ v.length := List.length_pos_of_ne_nil hv
  have hBR : Ck ≤ Cn + ((k : ℝ) - n) + (v.length - 1) := by
    have hc : (countOccurrences v (u.take k) : ℝ)
        ≤ ((countOccurrences v (u.take n) + (k - n) + (v.length - 1) : ℕ) : ℝ) := by
      exact_mod_cast hB
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hnk, Nat.cast_sub hv1] at hc
    push_cast at hc
    rw [hCn, hCk]; linarith [hc]
  -- assemble
  have hCkCn : |Ck - Cn| ≤ ((k : ℝ) - n) + (v.length - 1) := by
    rw [abs_le]; constructor <;> linarith [hAR, hBR]
  have htri : |Ck - γv * k| ≤ |Cn - γv * n| + |Ck - Cn| + |γv * ((k : ℝ) - n)| := by
    have hd : Ck - γv * k = (Cn - γv * n) + (Ck - Cn) + (-(γv * ((k : ℝ) - n))) := by ring
    rw [hd]
    calc |(Cn - γv * n) + (Ck - Cn) + (-(γv * ((k : ℝ) - n)))|
        ≤ |(Cn - γv * n) + (Ck - Cn)| + |(-(γv * ((k : ℝ) - n)))| := abs_add_le _ _
      _ ≤ |Cn - γv * n| + |Ck - Cn| + |γv * ((k : ℝ) - n)| := by
          rw [abs_neg]; gcongr; exact abs_add_le _ _
  have hmuleq : |γv * ((k : ℝ) - n)| = γv * ((k : ℝ) - n) := by
    rw [abs_mul, abs_of_nonneg hγ0, abs_of_nonneg hknR]
  have hγkn : γv * ((k : ℝ) - n) ≤ (k : ℝ) - n := by nlinarith [hγ1, hknR]
  linarith [htri, hCkCn, hmuleq, hγkn, hv1R]

/-- Quadratically-spaced scale set `{n₁ + j² : j ≤ m}`. -/
def quadScales (n₁ m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).image (fun j => n₁ + j ^ 2)

theorem quadScales_nonempty (n₁ m : ℕ) : (quadScales n₁ m).Nonempty := by
  refine Finset.Nonempty.image ?_ _
  exact ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩

theorem quadScales_card_le (n₁ m : ℕ) : (quadScales n₁ m).card ≤ m + 1 := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_range]

theorem quadScales_mem_ge (n₁ m : ℕ) : ∀ n ∈ quadScales n₁ m, n₁ ≤ n := by
  intro n hn
  rw [quadScales, Finset.mem_image] at hn
  obtain ⟨j, -, rfl⟩ := hn
  omega

theorem quadScales_max (n₁ m : ℕ) :
    (quadScales n₁ m).max' (quadScales_nonempty n₁ m) = n₁ + m ^ 2 := by
  refine le_antisymm ?_ ?_
  · refine Finset.max'_le _ _ _ (fun n hn => ?_)
    rw [quadScales, Finset.mem_image] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have : j ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hjm 2
    omega
  · refine Finset.le_max' _ _ ?_
    rw [quadScales, Finset.mem_image]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_self _), rfl⟩

/-- **Quadratic covering.**  Every `k ∈ [n₁, n₁+m²]` sits just above a scale
`n ∈ quadScales n₁ m` with gap `k − n ≤ 2·√(k−n₁)`. -/
theorem quadScales_cover {n₁ m k : ℕ} (hk1 : n₁ ≤ k) (hk2 : k ≤ n₁ + m ^ 2) :
    ∃ n ∈ quadScales n₁ m, n ≤ k ∧ k - n ≤ 2 * Nat.sqrt (k - n₁) := by
  set j := Nat.sqrt (k - n₁) with hj
  have hjm : j ≤ m := by
    rw [hj]
    have h1 : Nat.sqrt (k - n₁) ≤ Nat.sqrt (m ^ 2) := Nat.sqrt_le_sqrt (by omega)
    rwa [Nat.sqrt_eq'] at h1
  have hj2le : j ^ 2 ≤ k - n₁ := by rw [hj]; exact Nat.sqrt_le' _
  have hj2lt : k - n₁ < (j + 1) ^ 2 := by
    rw [hj, pow_two]; exact Nat.lt_succ_sqrt _
  refine ⟨n₁ + j ^ 2, ?_, by omega, ?_⟩
  · rw [quadScales, Finset.mem_image]
    exact ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  · have : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
    omega

/-- **THE UNIFORMLY-PREFIX-GOOD STEERABLE BLOCK (B6 crux crack).**  A steer block
`u` of length `n₁+m²` landing `cfCylinder(wx++u) ⊆ (c,d)` whose EVERY prefix
`u.take k` (`n₁ ≤ k ≤ |u|`) is freq-good with slack `4√k + 2|v| = o(k)`:
`|countOcc v (u.take k) − γv·k| < δ·k + (4√k + 2|v|)`.  This is the hdom-FREE
replacement for block-shortness — the property the affine two-stream schedule needs
because its blocks are `Θ(word)`.  Assembles the multi-scale per-scale block
(`exists_multiscale_freq_good_block_steer_len` at `NS = quadScales n₁ m`) with the
prefix interpolation (`abs_countOccurrences_take_interp`) via the quadratic
covering. -/
theorem exists_uniformly_freq_good_block_steer (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx)
    (m : ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁)
    (hbound : ((m + 1 : ℕ) : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal))
        < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal)
    (hres : 4 / (d - c) < (Nat.fib (wx.length + (n₁ + m ^ 2) + 1) : ℝ) ^ 2) :
    ∃ u : List ℕ, u.length = n₁ + m ^ 2 ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      (∀ k, n₁ ≤ k → k ≤ u.length → ∀ v ∈ F,
        |(countOccurrences v (u.take k) : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * k|
          < δ * k + (4 * Nat.sqrt k + 2 * v.length)) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  set NS := quadScales n₁ m with hNSdef
  have hNSne : NS.Nonempty := quadScales_nonempty n₁ m
  have hmax : NS.max' hNSne = n₁ + m ^ 2 := quadScales_max n₁ m
  set A₁ : ℝ := ∑ v ∈ F, 7 * ((8 * v.length + 80)
      * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
      * (gaussMeasure (cfCylinder wx)).toReal with hA₁
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    refine Finset.sum_nonneg fun v _ => ?_
    have h0 : (0:ℝ) ≤ 8 * v.length + 80 := by positivity
    have h1 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have h2 : (0:ℝ) ≤ (gaussMeasure (cfCylinder wx)).toReal := ENNReal.toReal_nonneg
    positivity
  have hcard : (NS.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast quadScales_card_le n₁ m
  have hboundNS : (NS.card : ℝ) * A₁
      < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
    have : (NS.card : ℝ) * A₁ ≤ ((m + 1 : ℕ) : ℝ) * A₁ :=
      mul_le_mul_of_nonneg_right hcard hA₁0
    linarith [this, hbound]
  have hresNS : 4 / (d - c) < (Nat.fib (wx.length + NS.max' hNSne + 1) : ℝ) ^ 2 := by
    rw [hmax]; exact hres
  obtain ⟨u, hulen, hune, hupos, hsubcd, hfreqNS, x, hxcyl, hirr, hxcd⟩ :=
    exists_multiscale_freq_good_block_steer_len wx hwx hwxpos F hF hFne hδ hc0 hcd hd1 hsub
      NS hNSne hn₁ (quadScales_mem_ge n₁ m) hboundNS hresNS
  have hulen' : u.length = n₁ + m ^ 2 := by rw [hulen, hmax]
  refine ⟨u, hulen', hune, hupos, hsubcd, ?_, x, hxcyl, hirr, hxcd⟩
  intro k hk1 hk2 v hv
  have hk2' : k ≤ n₁ + m ^ 2 := by rw [← hulen']; exact hk2
  obtain ⟨n, hnNS, hnk, hgap⟩ := quadScales_cover hk1 hk2'
  have hgood := hfreqNS n hnNS v hv
  obtain ⟨hγ0, hγ1⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
  have hku : k ≤ u.length := hk2
  have hinterp := abs_countOccurrences_take_interp (hFne v hv) hγ0 hγ1 hnk hku
  have hsqrt : Nat.sqrt (k - n₁) ≤ Nat.sqrt k := Nat.sqrt_le_sqrt (by omega)
  have hgapN : k - n ≤ 2 * Nat.sqrt k := le_trans hgap (by omega)
  have hgapR : (k : ℝ) - (n : ℝ) ≤ 2 * (Nat.sqrt k : ℝ) := by
    have hc : ((k - n : ℕ) : ℝ) ≤ ((2 * Nat.sqrt k : ℕ) : ℝ) := by exact_mod_cast hgapN
    rw [Nat.cast_sub hnk] at hc
    push_cast at hc
    linarith [hc]
  have hδnk : δ * (n : ℝ) ≤ δ * (k : ℝ) := by
    apply mul_le_mul_of_nonneg_left ?_ hδ.le; exact_mod_cast hnk
  calc |(countOccurrences v (u.take k) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * k|
      ≤ |(countOccurrences v (u.take n) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n| + 2 * ((k : ℝ) - n) + v.length := hinterp
    _ < (δ * n + v.length) + 2 * ((k : ℝ) - n) + v.length := by linarith [hgood]
    _ ≤ δ * k + (4 * Nat.sqrt k + 2 * v.length) := by linarith [hδnk, hgapR]

/-- **Uniformly-prefix-good steer block with a cfK cap** (cfK-graft layer 2).  Mirror of
`exists_uniformly_freq_good_block_steer` calling the layer-1 cfK builder at
`NS = quadScales n₁ m` (so `NS.max' = n₁+m²`).  The cfK cap `cfK u ≤ e^{κ|u|}` passes
straight through — `u` is the same digit block, `|u| = n₁+m²` unchanged.  The aggregate
`hbound` gains the cfK-large extension mass at relative order `n₁+m²`. -/
theorem exists_uniformly_freq_good_block_steer_cfK (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx)
    (m : ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁) (κ : ℝ)
    (hbound : ((m + 1 : ℕ) : ℝ) * ((∑ v ∈ F, 7 * ((8 * v.length + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
        * (gaussMeasure (cfCylinder wx)).toReal))
        + (gaussMeasure (cfKbadExtSet wx κ (n₁ + m ^ 2))).toReal
        < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal)
    (hres : 4 / (d - c) < (Nat.fib (wx.length + (n₁ + m ^ 2) + 1) : ℝ) ^ 2) :
    ∃ u : List ℕ, u.length = n₁ + m ^ 2 ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      (∀ k, n₁ ≤ k → k ≤ u.length → ∀ v ∈ F,
        |(countOccurrences v (u.take k) : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * k|
          < δ * k + (4 * Nat.sqrt k + 2 * v.length)) ∧
      (cfK u : ℝ) ≤ Real.exp (κ * (u.length : ℝ)) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  set NS := quadScales n₁ m with hNSdef
  have hNSne : NS.Nonempty := quadScales_nonempty n₁ m
  have hmax : NS.max' hNSne = n₁ + m ^ 2 := quadScales_max n₁ m
  set A₁ : ℝ := ∑ v ∈ F, 7 * ((8 * v.length + 80)
      * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n₁))
      * (gaussMeasure (cfCylinder wx)).toReal with hA₁
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    refine Finset.sum_nonneg fun v _ => ?_
    have h0 : (0:ℝ) ≤ 8 * v.length + 80 := by positivity
    have h1 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have h2 : (0:ℝ) ≤ (gaussMeasure (cfCylinder wx)).toReal := ENNReal.toReal_nonneg
    positivity
  have hcard : (NS.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast quadScales_card_le n₁ m
  have hboundNS : (NS.card : ℝ) * A₁
      + (gaussMeasure (cfKbadExtSet wx κ (NS.max' hNSne))).toReal
      < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
    have hle : (NS.card : ℝ) * A₁ ≤ ((m + 1 : ℕ) : ℝ) * A₁ :=
      mul_le_mul_of_nonneg_right hcard hA₁0
    rw [hmax]
    linarith [hle, hbound]
  have hresNS : 4 / (d - c) < (Nat.fib (wx.length + NS.max' hNSne + 1) : ℝ) ^ 2 := by
    rw [hmax]; exact hres
  obtain ⟨u, hulen, hune, hupos, hsubcd, hfreqNS, hcfKu, x, hxcyl, hirr, hxcd⟩ :=
    exists_multiscale_freq_good_block_steer_len_cfK wx hwx hwxpos F hF hFne hδ hc0 hcd hd1 hsub
      NS hNSne hn₁ (quadScales_mem_ge n₁ m) κ hboundNS hresNS
  have hulen' : u.length = n₁ + m ^ 2 := by rw [hulen, hmax]
  refine ⟨u, hulen', hune, hupos, hsubcd, ?_, hcfKu, x, hxcyl, hirr, hxcd⟩
  intro k hk1 hk2 v hv
  have hk2' : k ≤ n₁ + m ^ 2 := by rw [← hulen']; exact hk2
  obtain ⟨n, hnNS, hnk, hgap⟩ := quadScales_cover hk1 hk2'
  have hgood := hfreqNS n hnNS v hv
  obtain ⟨hγ0, hγ1⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
  have hku : k ≤ u.length := hk2
  have hinterp := abs_countOccurrences_take_interp (hFne v hv) hγ0 hγ1 hnk hku
  have hsqrt : Nat.sqrt (k - n₁) ≤ Nat.sqrt k := Nat.sqrt_le_sqrt (by omega)
  have hgapN : k - n ≤ 2 * Nat.sqrt k := le_trans hgap (by omega)
  have hgapR : (k : ℝ) - (n : ℝ) ≤ 2 * (Nat.sqrt k : ℝ) := by
    have hc : ((k - n : ℕ) : ℝ) ≤ ((2 * Nat.sqrt k : ℕ) : ℝ) := by exact_mod_cast hgapN
    rw [Nat.cast_sub hnk] at hc
    push_cast at hc
    linarith [hc]
  have hδnk : δ * (n : ℝ) ≤ δ * (k : ℝ) := by
    apply mul_le_mul_of_nonneg_left ?_ hδ.le; exact_mod_cast hnk
  calc |(countOccurrences v (u.take k) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * k|
      ≤ |(countOccurrences v (u.take n) : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n| + 2 * ((k : ℝ) - n) + v.length := hinterp
    _ < (δ * n + v.length) + 2 * ((k : ℝ) - n) + v.length := by linarith [hgood]
    _ ≤ δ * k + (4 * Nat.sqrt k + 2 * v.length) := by linarith [hδnk, hgapR]

/-- **Feasible block parameter.**  For any target ratio `β > 0` and length/fib
thresholds `Lc`, `Nfib`, there is `m > 0` with `m² ≥ Lc`, `m² ≥ Nfib`, and
`(m+1)/(m·⌊√m⌋) < β`.  The last is the measure-budget slack: with `n₁ = m·⌊√m⌋`
(so `m ≪ n₁ ≪ m²`), the crude budget `(m+1)·S/n₁ = (m+1)S/(m·⌊√m⌋) ≤ 2S/⌊√m⌋ → 0`
clears any fixed target, while `n₁ = o(m²) = o(|block|)` keeps the below-threshold
region negligible (needed for the `o(word)` slack telescoping). -/
theorem exists_uniform_block_param (β : ℝ) (hβ : 0 < β) (Lc Nfib : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Lc ≤ m ^ 2 ∧ Nfib ≤ m ^ 2 ∧
      ((m : ℝ) + 1) / ((m : ℝ) * (Nat.sqrt m : ℝ)) < β := by
  obtain ⟨t, ht⟩ := exists_nat_gt (2 / β)
  refine ⟨max (max Lc Nfib) (max (t ^ 2) 1), ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
  · have hle : Lc ≤ max (max Lc Nfib) (max (t ^ 2) 1) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have h1 : 1 ≤ max (max Lc Nfib) (max (t ^ 2) 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith [hle, h1]
  · have hle : Nfib ≤ max (max Lc Nfib) (max (t ^ 2) 1) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have h1 : 1 ≤ max (max Lc Nfib) (max (t ^ 2) 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith [hle, h1]
  · set m := max (max Lc Nfib) (max (t ^ 2) 1) with hmdef
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
    have ht2m : t ^ 2 ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
    have hsqrt : t ≤ Nat.sqrt m := by
      have h := Nat.sqrt_le_sqrt ht2m
      rwa [Nat.sqrt_eq'] at h
    have htR0 : (0 : ℝ) < (t : ℝ) := by
      have h0 : (0 : ℝ) < 2 / β := by positivity
      have : (0 : ℝ) < (t : ℝ) := lt_trans h0 ht
      exact this
    have hsqrtR : (t : ℝ) ≤ (Nat.sqrt m : ℝ) := by exact_mod_cast hsqrt
    have hsqrtpos : (0 : ℝ) < (Nat.sqrt m : ℝ) := lt_of_lt_of_le htR0 hsqrtR
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have h1 : ((m : ℝ) + 1) / ((m : ℝ) * (Nat.sqrt m : ℝ)) ≤ 2 / (Nat.sqrt m : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hsqrtpos]
      nlinarith [hmR, hsqrtpos.le]
    have h2 : (2 : ℝ) / (Nat.sqrt m : ℝ) ≤ 2 / (t : ℝ) := by
      gcongr
    have h3 : (2 : ℝ) / (t : ℝ) < β := by
      rw [div_lt_iff₀ htR0]
      rw [div_lt_iff₀ hβ] at ht
      nlinarith [ht]
    linarith [h1, h2, h3]

/-- **Gauss-measure lower density bound.**  On `[0,1]` the Gauss density
`1/((1+x)ln2)` is `≥ 1/(2ln2)`, so `μ_G(u,v) ≥ (v−u)/(2ln2)`.  With the matching
upper bound below, ratios of Gauss measures of subintervals of `(0,1)` are pinned
to their WIDTH ratios up to the constant `2` — the word-independent comparison the
interleaved schedule's per-round measure budget needs (`γtar ≥ q·c₀·γwx`). -/
theorem gaussMeasure_Ioo_toReal_ge {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (v - u) / (2 * Real.log 2) ≤ (gaussMeasure (Set.Ioo u v)).toReal := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1u : (0:ℝ) < 1 + u := by linarith
  have h1v : (0:ℝ) < 1 + v := by linarith
  have hdiff : Real.log (1 + v) - Real.log (1 + u) = Real.log ((1+v)/(1+u)) := by
    rw [Real.log_div (ne_of_gt h1v) (ne_of_gt h1u)]
  have hxpos : (0:ℝ) < (1+v)/(1+u) := by positivity
  have hx1 : (1:ℝ) ≤ (1+v)/(1+u) := (one_le_div h1u).mpr (by linarith)
  have hnum : 0 ≤ Real.log (1 + v) - Real.log (1 + u) := by
    rw [hdiff]; exact Real.log_nonneg hx1
  have hlow : 1 - ((1+v)/(1+u))⁻¹ ≤ Real.log ((1+v)/(1+u)) :=
    Real.one_sub_inv_le_log_of_pos hxpos
  have hinv : ((1+v)/(1+u))⁻¹ = (1+u)/(1+v) := by rw [inv_div]
  have h2 : 1 - (1+u)/(1+v) = (v - u)/(1+v) := by field_simp; ring
  have h3 : (v - u)/2 ≤ (v - u)/(1+v) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have hbound : (v - u) / 2 ≤ Real.log (1 + v) - Real.log (1 + u) := by
    rw [hinv, h2] at hlow; rw [hdiff]; linarith [hlow, h3]
  rw [gaussMeasure_Ioo hu huv hv, ENNReal.toReal_ofReal (div_nonneg hnum hl2.le)]
  rw [div_le_div_iff₀ (by positivity) hl2]
  nlinarith [hbound, hl2]

/-- **Gauss-measure upper density bound.**  `μ_G(u,v) ≤ (v−u)/ln2` (density
`≤ 1/ln2` on `[0,1]`).  Pairs with `gaussMeasure_Ioo_toReal_ge`. -/
theorem gaussMeasure_Ioo_toReal_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (gaussMeasure (Set.Ioo u v)).toReal ≤ (v - u) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1u : (0:ℝ) < 1 + u := by linarith
  have h1v : (0:ℝ) < 1 + v := by linarith
  have hdiff : Real.log (1 + v) - Real.log (1 + u) = Real.log ((1+v)/(1+u)) := by
    rw [Real.log_div (ne_of_gt h1v) (ne_of_gt h1u)]
  have hxpos : (0:ℝ) < (1+v)/(1+u) := by positivity
  have hx1 : (1:ℝ) ≤ (1+v)/(1+u) := (one_le_div h1u).mpr (by linarith)
  have hnum : 0 ≤ Real.log (1 + v) - Real.log (1 + u) := by
    rw [hdiff]; exact Real.log_nonneg hx1
  have hup : Real.log ((1+v)/(1+u)) ≤ (1+v)/(1+u) - 1 := Real.log_le_sub_one_of_pos hxpos
  have h2 : (1+v)/(1+u) - 1 = (v - u)/(1+u) := by field_simp; ring
  have h3 : (v - u)/(1+u) ≤ v - u := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [huv, hu]
  have hbound : Real.log (1 + v) - Real.log (1 + u) ≤ v - u := by
    rw [h2] at hup; rw [hdiff]; linarith [hup, h3]
  rw [gaussMeasure_Ioo hu huv hv, ENNReal.toReal_ofReal (div_nonneg hnum hl2.le)]
  rw [div_le_div_iff₀ hl2 hl2]
  nlinarith [hbound, hl2]

/-- **Middle-half Gauss mass is a WORD-INDEPENDENT fraction of the whole interval.**
For `0 ≤ c ≤ d ≤ 1`, the middle half `(c+(d−c)/4, d−(d−c)/4)` carries `≥ ¼` of the Gauss
mass of `(c,d)`.  Proof: width of the middle half is `(d−c)/2`, so its mass is
`≥ (d−c)/(4 ln2)` (lower density `1/(2ln2)`), while `γ(c,d) ≤ (d−c)/ln2` (upper density
`1/ln2`); the ratio is `≥ ¼` with NO dependence on `c,d` (hence none on the cylinder
depth).  This is exactly the `γtar/γ(hull) = Θ(1)` fact that makes the L4 self-hull
steer's block parameter `β = γtar·δ²/(S+γwx)` word-independent — the resolution of the
block-linear crux (see PENDING_WORK: relative regularization). -/
theorem gaussMeasure_middle_half_ge {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (1 / 4) * (gaussMeasure (Set.Ioo c d)).toReal
      ≤ (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : 0 ≤ c + (d - c) / 4 := by nlinarith [hcd]
  have hmm : c + (d - c) / 4 ≤ d - (d - c) / 4 := by nlinarith [hcd]
  have hm1 : d - (d - c) / 4 ≤ 1 := by nlinarith [hcd, hd]
  have hlow := gaussMeasure_Ioo_toReal_ge hm0 hmm hm1
  have hup := gaussMeasure_Ioo_toReal_le hc hcd hd
  have hmidwidth : (d - (d - c) / 4) - (c + (d - c) / 4) = (d - c) / 2 := by ring
  rw [hmidwidth] at hlow
  -- γ(mid) ≥ (d−c)/(4 ln2) ≥ ¼·γ(c,d)
  have hstep : (1 / 4) * (gaussMeasure (Set.Ioo c d)).toReal ≤ (d - c) / 2 / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    have hthis : (gaussMeasure (Set.Ioo c d)).toReal * Real.log 2 ≤ (d - c) :=
      (le_div_iff₀ hl2).mp hup
    nlinarith [hthis, hl2]
  exact le_trans hstep hlow

/-- `gaussMeasure` has no atoms: every singleton is null (it is `≪ volume`). -/
theorem gaussMeasure_singleton (x : ℝ) : gaussMeasure {x} = 0 := by
  have hac : gaussMeasure ≪ MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hac2 : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1) ≪ MeasureTheory.volume :=
    MeasureTheory.Measure.restrict_le_self.absolutelyContinuous
  exact (hac.trans hac2) (by simp [Real.volume_singleton])

/-- **The middle-half of the hull carries a fixed fraction of the cylinder's mass.**
For a cylinder inside a hull `Icc a b`, `γtar := γ(middle-half of [a,b]) ≥ ¼·γ(cfCylinder w)`.
Bounds `γ(cfCylinder w) ≤ γ(Ioo a b)` (atomless: `γ(Icc)=γ(Ioo)`) then applies
`gaussMeasure_middle_half_ge`.  This is the `ratio = 1/4` input that makes
`two_div_beta_rel_le` collapse the block parameter's word-dependence. -/
theorem gaussMeasure_middle_half_hull_ge (w : List ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hsub : cfCylinder w ⊆ Set.Icc a b) :
    (1 / 4) * (gaussMeasure (cfCylinder w)).toReal
      ≤ (gaussMeasure (Set.Ioo (a + (b - a) / 4) (b - (b - a) / 4))).toReal := by
  -- γ(cfCylinder w) ≤ γ(Icc a b) ≤ γ(Ioo a b)
  have hIccIoo : gaussMeasure (Set.Icc a b) ≤ gaussMeasure (Set.Ioo a b) := by
    have hcover : Set.Icc a b ⊆ Set.Ioo a b ∪ ({a} ∪ {b}) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact Or.inr (Or.inl h.symm)
      rcases eq_or_lt_of_le hx.2 with h2 | h2
      · exact Or.inr (Or.inr h2)
      · exact Or.inl ⟨h, h2⟩
    calc gaussMeasure (Set.Icc a b)
        ≤ gaussMeasure (Set.Ioo a b ∪ ({a} ∪ {b})) := measure_mono hcover
      _ ≤ gaussMeasure (Set.Ioo a b) + gaussMeasure ({a} ∪ {b}) := measure_union_le _ _
      _ ≤ gaussMeasure (Set.Ioo a b) + (gaussMeasure {a} + gaussMeasure {b}) := by
          gcongr; exact measure_union_le _ _
      _ = gaussMeasure (Set.Ioo a b) := by
          rw [gaussMeasure_singleton, gaussMeasure_singleton]; simp
  have hle : gaussMeasure (cfCylinder w) ≤ gaussMeasure (Set.Ioo a b) :=
    (measure_mono hsub).trans hIccIoo
  have hfin : gaussMeasure (Set.Ioo a b) ≠ ⊤ := measure_ne_top _ _
  have hleR : (gaussMeasure (cfCylinder w)).toReal ≤ (gaussMeasure (Set.Ioo a b)).toReal :=
    ENNReal.toReal_mono hfin hle
  have hmid := gaussMeasure_middle_half_ge ha hab hb
  linarith [hmid, hleR]

/-- **Relative regularization kills the block parameter's word-dependence.**  With the
block parameter `β_rel = γtar·δ²/(S + γwx)`, `S = γwx·Sg` (relative regularizer `+γwx`
instead of the scaling-breaking absolute `+1`), the quantity `2/β_rel` — which drives the
tight block length via `⌈2/β_rel⌉` — is bounded by `2(Sg+1)/(ratio·δ²)`, WORD-INDEPENDENT,
as soon as the target carries a fixed fraction of the cylinder mass, `γtar ≥ ratio·γwx`.
The `γwx` cancels top and bottom: `2/β_rel = 2·γwx(Sg+1)/(γtar·δ²) ≤ 2(Sg+1)/(ratio·δ²)`.
This is the arithmetic core of the block-linear crux resolution (see PENDING_WORK): for the
L4 self-hull steer `ratio = 1/8` (`gaussMeasure_middle_half_ge`), so the block stays linear
in `L + Nfib` and the word grows only geometrically. -/
theorem two_div_beta_rel_le {Sg δ ratio γwx γtar : ℝ}
    (hSg : 0 ≤ Sg) (hδ : 0 < δ) (hratio : 0 < ratio) (hγwx : 0 < γwx)
    (htar : ratio * γwx ≤ γtar) :
    2 / (γtar * δ ^ 2 / (γwx * Sg + γwx)) ≤ 2 * (Sg + 1) / (ratio * δ ^ 2) := by
  have hγtar : 0 < γtar := lt_of_lt_of_le (mul_pos hratio hγwx) htar
  have hden : (0 : ℝ) < γwx * Sg + γwx := by nlinarith [mul_nonneg hγwx.le hSg, hγwx]
  have hβpos : (0 : ℝ) < γtar * δ ^ 2 / (γwx * Sg + γwx) := by positivity
  rw [div_div_eq_mul_div,
    div_le_div_iff₀ (by positivity : (0:ℝ) < γtar * δ ^ 2) (by positivity : (0:ℝ) < ratio * δ ^ 2)]
  -- 2*(γwx*Sg+γwx) * (ratio*δ²) ≤ 2*(Sg+1) * (γtar*δ²)
  have hfactor : γwx * Sg + γwx = γwx * (Sg + 1) := by ring
  rw [hfactor]
  have hδ2 : 0 < δ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right htar (by positivity : (0:ℝ) ≤ (Sg + 1) * δ ^ 2),
    mul_nonneg hγwx.le hSg, hγtar.le, hδ2]

/-- **Tight block parameter (word-independent block length).**  Like
`exists_uniform_block_param` but returns `m` with `m² ~ max(Lc, Nfib, poly(1/β))`
instead of the lossy `m ~ max(Lc, Nfib, …)` (whose `m² ~ Nfib²` is QUADRATIC in the
resolution `Nfib`).  Concretely `m = max(⌈√max(Lc,Nfib)⌉+1, (⌈2/β⌉+1)²)`, giving
the same three feasibility clauses PLUS the explicit upper bound
`m² ≤ 6(Lc+Nfib) + 2 + 2(⌈2/β⌉+1)⁴` — LINEAR in `Lc, Nfib`, with the only
`β`-dependence isolated in the last (word-independent) term.  This is what lets the
interleaved schedule keep each block `|u_s| = n₁+m² = O(|w_s|)` (`hgeom` for
`slack_telescoping`): with `Nfib ~ |w_s|` (resolution) and `Lc, β` per-level
bounded, the block stays `≲ |w_s|` so the word grows at most geometrically. -/
theorem exists_uniform_block_param_tight (β : ℝ) (hβ : 0 < β) (Lc Nfib : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Lc ≤ m ^ 2 ∧ Nfib ≤ m ^ 2 ∧
      ((m : ℝ) + 1) / ((m : ℝ) * (Nat.sqrt m : ℝ)) < β ∧
      m ^ 2 ≤ 6 * (Lc + Nfib) + 2 + 2 * (Nat.ceil (2 / β) + 1) ^ 4 := by
  set t : ℕ := Nat.ceil (2 / β) + 1 with htdef
  set s : ℕ := Nat.sqrt (max Lc Nfib) + 1 with hsdef
  set m : ℕ := max s (t ^ 2) with hmdef
  have hs2 : max Lc Nfib < s ^ 2 := by
    rw [hsdef, pow_two]; exact Nat.lt_succ_sqrt (max Lc Nfib)
  have hsm : s ≤ m := le_max_left _ _
  have htm : t ^ 2 ≤ m := le_max_right _ _
  have hs1 : 1 ≤ s := by rw [hsdef]; omega
  have hm1 : 1 ≤ m := le_trans hs1 hsm
  have hm0 : 0 < m := hm1
  have hms2 : s ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hsm 2
  have hLcm : Lc ≤ m ^ 2 := le_trans (le_trans (le_max_left _ _) (le_of_lt hs2)) hms2
  have hNfibm : Nfib ≤ m ^ 2 := le_trans (le_trans (le_max_right _ _) (le_of_lt hs2)) hms2
  have ht1 : 1 ≤ t := by omega
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht1
  have hsqrtm : t ≤ Nat.sqrt m := by
    have h := Nat.sqrt_le_sqrt htm; rwa [Nat.sqrt_eq'] at h
  have hsqrtmR : (t:ℝ) ≤ (Nat.sqrt m : ℝ) := by exact_mod_cast hsqrtm
  have hsqrtpos : (0:ℝ) < (Nat.sqrt m : ℝ) := lt_of_lt_of_le htpos hsqrtmR
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hβbound : ((m : ℝ) + 1) / ((m : ℝ) * (Nat.sqrt m : ℝ)) < β := by
    have h1 : ((m : ℝ) + 1) / ((m : ℝ) * (Nat.sqrt m : ℝ)) ≤ 2 / (Nat.sqrt m : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hsqrtpos]; nlinarith [hmR, hsqrtpos.le]
    have h2 : (2:ℝ) / (Nat.sqrt m : ℝ) ≤ 2 / (t:ℝ) := by gcongr
    have h3 : (2:ℝ) / (t:ℝ) < β := by
      have hceil : (2/β : ℝ) ≤ (Nat.ceil (2/β) : ℝ) := Nat.le_ceil _
      have htgt : (2/β : ℝ) < (t:ℝ) := by rw [htdef]; push_cast; linarith [hceil]
      rw [div_lt_iff₀ htpos]
      have := (div_lt_iff₀ hβ).mp htgt
      nlinarith [this]
    linarith [h1, h2, h3]
  refine ⟨m, hm0, hLcm, hNfibm, hβbound, ?_⟩
  have hsq : Nat.sqrt (max Lc Nfib) ^ 2 ≤ max Lc Nfib := Nat.sqrt_le' _
  have hsqle : Nat.sqrt (max Lc Nfib) ≤ max Lc Nfib := Nat.sqrt_le_self _
  have hmaxle : max Lc Nfib ≤ Lc + Nfib := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hs2ub : s ^ 2 ≤ 3 * (Lc + Nfib) + 1 := by
    have hexp : s ^ 2 = Nat.sqrt (max Lc Nfib) ^ 2 + 2 * Nat.sqrt (max Lc Nfib) + 1 := by
      rw [hsdef]; ring
    rw [hexp]; omega
  have hm2ub : m ^ 2 ≤ s ^ 2 + t ^ 4 := by
    rcases le_total s (t ^ 2) with h | h
    · rw [hmdef, max_eq_right h]
      have ht4 : (t ^ 2) ^ 2 = t ^ 4 := by ring
      rw [ht4]; omega
    · rw [hmdef, max_eq_left h]; nlinarith [Nat.zero_le (t ^ 4)]
  calc m ^ 2 ≤ s ^ 2 + t ^ 4 := hm2ub
    _ ≤ 3 * (Lc + Nfib) + 1 + t ^ 4 := by omega
    _ ≤ 6 * (Lc + Nfib) + 2 + 2 * t ^ 4 := by omega

/-- **Length-driven uniformly-good steer block (per-round FEASIBILITY discharged).**
Like `exists_uniformly_freq_good_block_steer` but the caller supplies only a
minimum length `L`; the two budget inequalities (`hbound` measure, `hres`
resolution) are discharged INTERNALLY by choosing `m` large and `n₁ = m·⌊√m⌋`
(so `m ≪ n₁ ≪ m²`, via `exists_uniform_block_param`).  Output: a block `u` with
`|u| ≥ L`, `cfCylinder(wx++u) ⊆ (c,d)`, the folded uniform prefix bound
`∀k≤|u|, |dev(u.take k)| < δ·k + (4⌊√|u|⌋ + 2|v| + n₁)` (below-threshold `k<n₁`
absorbed by the `+n₁`), and the exposed `n₁² ≤ |u|·⌊√|u|⌋` witnessing `n₁ = o(|u|)`
(the smallness the schedule's `o(word)` slack telescoping needs). -/
theorem exists_uniformly_freq_good_block_steer_len (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx) (L : ℕ) :
    ∃ (u : List ℕ) (n₁ : ℕ), L ≤ u.length ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      n₁ ^ 2 ≤ u.length * Nat.sqrt u.length ∧
      (∀ k, k ≤ u.length → ∀ v ∈ F,
        |(countOccurrences v (u.take k) : ℝ) - (gaussMeasure (cfCylinder v)).toReal * k|
          < δ * k + (4 * Nat.sqrt u.length + 2 * v.length + n₁)) ∧
      ∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d := by
  -- target measure of the middle half of `(c,d)` is positive
  have hu0v0 : c + (d - c) / 4 < d - (d - c) / 4 := by nlinarith [hcd]
  have hu00 : 0 ≤ c + (d - c) / 4 := by nlinarith [hc0, hcd]
  have hv01 : d - (d - c) / 4 ≤ 1 := by nlinarith [hd1, hcd]
  have hposreal : 0 < (Real.log (1 + (d - (d - c) / 4)) - Real.log (1 + (c + (d - c) / 4)))
      / Real.log 2 := by
    apply div_pos
    · rw [sub_pos]; apply Real.log_lt_log (by nlinarith [hu00]) (by linarith [hu0v0])
    · exact Real.log_pos (by norm_num)
  have hγtar : 0 < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
    rw [gaussMeasure_Ioo hu00 hu0v0.le hv01, ENNReal.toReal_ofReal hposreal.le]; exact hposreal
  set γtar := (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal with hγtardef
  set γwx := (gaussMeasure (cfCylinder wx)).toReal with hγwxdef
  set S := ∑ v ∈ F, 7 * (8 * (v.length : ℝ) + 80)
      * (gaussMeasure (cfCylinder v)).toReal * γwx with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]; refine Finset.sum_nonneg fun v _ => ?_
    have : 0 ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ γwx := ENNReal.toReal_nonneg
    positivity
  set β := γtar * δ ^ 2 / (S + 1) with hβdef
  have hβ : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hγtar (by positivity)) (by linarith [hS0])
  obtain ⟨Nfib, hNfib⟩ := exists_fib_threshold (4 / (d - c))
  obtain ⟨m, hm0, hLm, hNfibm, hfrac⟩ := exists_uniform_block_param β hβ L Nfib
  have hsqrtm1 : 1 ≤ Nat.sqrt m := by
    have h := Nat.sqrt_le_sqrt (show 1 ≤ m by omega); simpa using h
  set n₁ := m * Nat.sqrt m with hn₁def
  have hn₁0 : 0 < n₁ := by rw [hn₁def]; exact Nat.mul_pos hm0 hsqrtm1
  have hn₁R : (n₁ : ℝ) = (m : ℝ) * (Nat.sqrt m : ℝ) := by rw [hn₁def]; push_cast; ring
  -- discharge the measure budget `hbound`
  have hbound : ((m + 1 : ℕ) : ℝ) * (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ)))
        * γwx) < γtar := by
    have hsumeq : (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ))) * γwx)
        = S / (δ ^ 2 * (n₁ : ℝ)) := by
      rw [hSdef, Finset.sum_div]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsumeq]
    have hfrac2 : ((m : ℝ) + 1) / (n₁ : ℝ) < γtar * δ ^ 2 / (S + 1) := by
      rw [hn₁R]; rw [hβdef] at hfrac; exact hfrac
    rw [div_lt_div_iff₀ (by rw [hn₁R]; positivity) (by linarith [hS0] : (0 : ℝ) < S + 1)] at hfrac2
    have hden : (0 : ℝ) < δ ^ 2 * (n₁ : ℝ) := by rw [hn₁R]; positivity
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    push_cast
    nlinarith [hfrac2, hm1R]
  -- discharge the resolution `hres`
  have hres : 4 / (d - c) < (Nat.fib (wx.length + (n₁ + m ^ 2) + 1) : ℝ) ^ 2 :=
    hNfib (wx.length + (n₁ + m ^ 2)) (by omega)
  -- produce the block
  obtain ⟨u, hulen, hune, hupos, hsubcd, hufreq, x, hxcyl, hxirr, hxcd⟩ :=
    exists_uniformly_freq_good_block_steer wx hwx hwxpos F hF hFne hδ hc0 hcd hd1 hsub
      m (n₁ := n₁) hn₁0 hbound hres
  refine ⟨u, n₁, ?_, hune, hupos, hsubcd, ?_, ?_, x, hxcyl, hxirr, hxcd⟩
  · rw [hulen]; omega
  · -- n₁² ≤ |u|·⌊√|u|⌋
    rw [hulen]
    have hsm : Nat.sqrt m ^ 2 ≤ m := Nat.sqrt_le' m
    have h1 : n₁ ^ 2 ≤ m ^ 3 := by
      have he : n₁ ^ 2 = m ^ 2 * Nat.sqrt m ^ 2 := by rw [hn₁def]; ring
      rw [he]; nlinarith [hsm, Nat.zero_le (m ^ 2)]
    have hge : m ^ 2 ≤ n₁ + m ^ 2 := by omega
    have hsq : m ≤ Nat.sqrt (n₁ + m ^ 2) := by
      have h := Nat.sqrt_le_sqrt hge; rwa [Nat.sqrt_eq'] at h
    have h2 : m ^ 3 ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := by
      calc m ^ 3 = m ^ 2 * m := by ring
        _ ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := Nat.mul_le_mul hge hsq
    exact le_trans h1 h2
  · -- folded uniform prefix bound
    intro k hk v hv
    set γv := (gaussMeasure (cfCylinder v)).toReal with hγvdef
    obtain ⟨hγ0v, hγ1v⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
    have hsqle : (Nat.sqrt k : ℝ) ≤ (Nat.sqrt u.length : ℝ) := by
      exact_mod_cast Nat.sqrt_le_sqrt hk
    have hn₁nn : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    by_cases hkn₁ : n₁ ≤ k
    · have hb := hufreq k hkn₁ hk v hv
      have : δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length)
          ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := by
        push_cast; nlinarith [hsqle, hn₁nn]
      calc |(countOccurrences v (u.take k) : ℝ) - γv * k|
          < δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length) := hb
        _ ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := this
    · push_neg at hkn₁
      have hvne := hFne v hv
      have hcnt : (countOccurrences v (u.take k) : ℝ) ≤ (k : ℝ) := by
        have h1 := countOccurrences_le_length hvne (u.take k)
        have h2 : (u.take k).length ≤ k := by rw [List.length_take]; exact min_le_left _ _
        exact_mod_cast le_trans h1 h2
      have hccnn : (0 : ℝ) ≤ (countOccurrences v (u.take k) : ℝ) := Nat.cast_nonneg _
      have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hcrude : |(countOccurrences v (u.take k) : ℝ) - γv * k| ≤ (k : ℝ) := by
        rw [abs_le]; constructor <;> nlinarith [hcnt, hccnn, hγ0v, hγ1v, hkR]
      have hklt : (k : ℝ) < (n₁ : ℝ) := by exact_mod_cast hkn₁
      have hδk : (0 : ℝ) ≤ δ * k := by positivity
      have hrest : (0 : ℝ) ≤ 4 * (Nat.sqrt u.length : ℝ) + 2 * v.length := by positivity
      linarith [hcrude, hklt, hδk, hrest]


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

/-- **THE ψ-ROUND STEP, FILLER-FREE (interleaved schedule).**  Same as
`exists_freq_good_extend_affine`, but each stream's APPENDED block
(`w'.drop w.length`) is a SINGLE frequency-good word — NO uncontrolled placement
filler — because it is built with `exists_freq_good_block_steer` (the steerable
block that navigates into the target while staying freq-good).  This is the form
the recursion feeds to the EXISTING `chain_orbit_equidist`: `chainApp w s =
w(s+1).drop|w s|` is exactly the exposed freq-good block, so the schedule
satisfies `hgood` with `chainApp` itself (`hdom` follows from slow growth).  The
route-decisive payoff of the steerable-block crack. -/
theorem exists_freq_good_extend_affine_steer {q : ℝ} (hq : 0 < q) (r : ℝ)
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
        L ≤ (wz'.drop wz.length).length ∧
          (∀ v ∈ F, |(countOccurrences v (wz'.drop wz.length) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * (wz'.drop wz.length).length|
              < δ * (wz'.drop wz.length).length + v.length)) ∧
      (wx' ≠ [] ∧ (∀ c ∈ wx', 1 ≤ c) ∧ wx'.take wx.length = wx ∧
        wx.length < wx'.length ∧ L ≤ wx'.length ∧ cfCylinder wx' ⊆ cfCylinder wx ∧
        L ≤ (wx'.drop wx.length).length ∧
          (∀ v ∈ F, |(countOccurrences v (wx'.drop wx.length) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * (wx'.drop wx.length).length|
              < δ * (wx'.drop wx.length).length + v.length)) ∧
      (0 ≤ e' ∧ e' < f' ∧ f' ≤ 1 ∧
        (∀ x ∈ Set.Ioo e' f', Irrational x → x ∈ cfCylinder wz')) ∧
      cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
  -- (1) wx-interval (a,b); (2) image bounds ψ((a,b)) ⊆ Icc e f
  obtain ⟨a, b, ha, hab, hb, hxIcc, hxint⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wx hwx hwxpos
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
  have hJ0 : 0 ≤ q * a + r := le_trans he0 hlo
  have hJ1 : q * b + r ≤ 1 := le_trans hhi hf1
  -- (3) steer a freq-good z-block into J_z = Ioo(qa+r)(qb+r)
  have hzsub : ∀ y ∈ Set.Ioo (q * a + r) (q * b + r), Irrational y → y ∈ cfCylinder wz := by
    intro y hy hyirr
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy
    exact hzint y (Set.mem_Ioo.2 ⟨lt_of_le_of_lt hlo h1, lt_of_lt_of_le h2 hhi⟩) hyirr
  obtain ⟨uz, huzne, huzL, huzpos, huzsubcd, huzfreq, pz, hpzmem, hpzirr, hpzcd⟩ :=
    exists_freq_good_block_steer wz hwz hwzpos F hF hFne hδ hJ0 huv hJ1 hzsub L
  set wz' := wz ++ uz with hwz'def
  have hwz'ne : wz' ≠ [] := by simp [hwz'def, huzne]
  have hwz'pos : ∀ c ∈ wz', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwzpos c) (huzpos c)
  have htakez : wz'.take wz.length = wz := by rw [hwz'def, List.take_left]
  have hdropz : wz'.drop wz.length = uz := by rw [hwz'def, List.drop_left]
  have hzgt : wz.length < wz'.length := by
    rw [hwz'def, List.length_append]
    have : 0 < uz.length := List.length_pos_of_ne_nil huzne
    omega
  have hsubz : cfCylinder wz' ⊆ cfCylinder wz := by
    rw [hwz'def]; exact cfCylinder_append_subset wz uz
  have hzL : L ≤ wz'.length := by
    rw [hwz'def, List.length_append]; omega
  -- (4) wz'-interval (e',f')
  obtain ⟨e', f', he'0, he'f', hf'1, hz'Icc, hz'int⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wz' hwz'ne hwz'pos
  -- (5) steer a freq-good x-block into (a,b) ∩ ψ⁻¹(Ioo e' f')
  have hpzIcc : pz ∈ Set.Icc e' f' := hz'Icc (by rw [hwz'def]; exact hpzmem)
  have he'pz : e' ≤ pz := hpzIcc.1
  have hpzf' : pz ≤ f' := hpzIcc.2
  obtain ⟨hpzlo, hpzhi⟩ := Set.mem_Ioo.1 hpzcd
  set a' := (e' - r) / q with ha'def
  set b' := (f' - r) / q with hb'def
  have ha'b : a' < b := (div_lt_iff₀ hq).mpr (by rw [ha'def] at *; nlinarith)
  have hab' : a < b' := (lt_div_iff₀ hq).mpr (by nlinarith)
  have ha'b' : a' < b' := by rw [ha'def, hb'def]; gcongr
  have hmax : max a a' < min b b' :=
    max_lt (lt_min hab hab') (lt_min ha'b ha'b')
  have hm0 : 0 ≤ max a a' := le_trans ha (le_max_left _ _)
  have hm1 : min b b' ≤ 1 := le_trans (min_le_left _ _) hb
  have hxsub : ∀ y ∈ Set.Ioo (max a a') (min b b'), Irrational y → y ∈ cfCylinder wx := by
    intro y hy hyirr
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy
    exact hxint y (Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_left _ _) h1,
      lt_of_lt_of_le h2 (min_le_left _ _)⟩) hyirr
  obtain ⟨ux, huxne, huxL, huxpos, huxsubcd, huxfreq, px, hpxmem, hpxirr, hpxcd⟩ :=
    exists_freq_good_block_steer wx hwx hwxpos F hF hFne hδ hm0 hmax hm1 hxsub L
  set wx' := wx ++ ux with hwx'def
  have hwx'ne : wx' ≠ [] := by simp [hwx'def, huxne]
  have hwx'pos : ∀ c ∈ wx', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwxpos c) (huxpos c)
  have htakex : wx'.take wx.length = wx := by rw [hwx'def, List.take_left]
  have hdropx : wx'.drop wx.length = ux := by rw [hwx'def, List.drop_left]
  have hxgt : wx.length < wx'.length := by
    rw [hwx'def, List.length_append]
    have : 0 < ux.length := List.length_pos_of_ne_nil huxne
    omega
  have hsubx : cfCylinder wx' ⊆ cfCylinder wx := by
    rw [hwx'def]; exact cfCylinder_append_subset wx ux
  have hxL : L ≤ wx'.length := by rw [hwx'def, List.length_append]; omega
  -- new invariant: cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')
  have hinv' : cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
    rw [preimage_affineMap_Ioo hq]
    intro y hy
    have hy2 := huxsubcd hy
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy2
    exact Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_right _ _) h1,
      lt_of_lt_of_le h2 (min_le_right _ _)⟩
  -- assemble (chainApp = the whole freq-good block, no filler)
  refine ⟨wx', wz', e', f',
    ⟨hwz'ne, hwz'pos, htakez, hzgt, hzL, hsubz, ?_, ?_⟩,
    ⟨hwx'ne, hwx'pos, htakex, hxgt, hxL, hsubx, ?_, ?_⟩,
    ⟨he'0, he'f', hf'1, hz'int⟩, hinv'⟩
  · rw [hdropz]; exact huzL
  · rw [hdropz]; exact huzfreq
  · rw [hdropx]; exact huxL
  · rw [hdropx]; exact huxfreq

/-- **THE ψ-ROUND STEP, FILLER-FREE + UNIFORM-PREFIX (interleaved schedule).**
Same interval-threading as `exists_freq_good_extend_affine_steer`, but each
stream's appended block `w'.drop w.length` is produced by
`exists_uniformly_freq_good_block_steer_len`, so the frequency-goodness holds
UNIFORMLY over every prefix `q ≤ |block|` with an `o(|block|)` slack
`C = 4·√|block| + 2|v| + n₁` (`n₁² ≤ |block|·√|block|`).  This is exactly the
`hblock` payload the HDOM-FREE `chain_orbit_equidist_uniform` consumes for both
streams — the steer blocks are `Θ(word)` (so `chain_orbit_equidist`'s `hdom`
fails) but ARE uniformly prefix-good with sublinear slack. -/
theorem exists_freq_good_extend_affine_steer_uniform {q : ℝ} (hq : 0 < q) (r : ℝ)
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
        L ≤ (wz'.drop wz.length).length ∧ ∃ n₁ : ℕ,
          n₁ ^ 2 ≤ (wz'.drop wz.length).length * Nat.sqrt (wz'.drop wz.length).length ∧
          (∀ k, k ≤ (wz'.drop wz.length).length → ∀ v ∈ F,
            |(countOccurrences v ((wz'.drop wz.length).take k) : ℝ)
              - (gaussMeasure (cfCylinder v)).toReal * k|
                < δ * k + (4 * Nat.sqrt (wz'.drop wz.length).length + 2 * v.length + n₁))) ∧
      (wx' ≠ [] ∧ (∀ c ∈ wx', 1 ≤ c) ∧ wx'.take wx.length = wx ∧
        wx.length < wx'.length ∧ L ≤ wx'.length ∧ cfCylinder wx' ⊆ cfCylinder wx ∧
        L ≤ (wx'.drop wx.length).length ∧ ∃ n₁ : ℕ,
          n₁ ^ 2 ≤ (wx'.drop wx.length).length * Nat.sqrt (wx'.drop wx.length).length ∧
          (∀ k, k ≤ (wx'.drop wx.length).length → ∀ v ∈ F,
            |(countOccurrences v ((wx'.drop wx.length).take k) : ℝ)
              - (gaussMeasure (cfCylinder v)).toReal * k|
                < δ * k + (4 * Nat.sqrt (wx'.drop wx.length).length + 2 * v.length + n₁))) ∧
      (0 ≤ e' ∧ e' < f' ∧ f' ≤ 1 ∧
        (∀ x ∈ Set.Ioo e' f', Irrational x → x ∈ cfCylinder wz') ∧
        cfCylinder wz' ⊆ Set.Icc e' f') ∧
      cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
  -- (1) wx-interval (a,b); (2) image bounds ψ((a,b)) ⊆ Icc e f
  obtain ⟨a, b, ha, hab, hb, hxIcc, hxint⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wx hwx hwxpos
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
  have hJ0 : 0 ≤ q * a + r := le_trans he0 hlo
  have hJ1 : q * b + r ≤ 1 := le_trans hhi hf1
  -- (3) steer a UNIFORM freq-good z-block into J_z = Ioo(qa+r)(qb+r)
  have hzsub : ∀ y ∈ Set.Ioo (q * a + r) (q * b + r), Irrational y → y ∈ cfCylinder wz := by
    intro y hy hyirr
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy
    exact hzint y (Set.mem_Ioo.2 ⟨lt_of_le_of_lt hlo h1, lt_of_lt_of_le h2 hhi⟩) hyirr
  obtain ⟨uz, n₁z, huzL, huzne, huzpos, huzsubcd, hn₁zsq, huzfreq, pz, hpzmem, hpzirr, hpzcd⟩ :=
    exists_uniformly_freq_good_block_steer_len wz hwz hwzpos F hF hFne hδ hJ0 huv hJ1 hzsub L
  set wz' := wz ++ uz with hwz'def
  have hwz'ne : wz' ≠ [] := by simp [hwz'def, huzne]
  have hwz'pos : ∀ c ∈ wz', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwzpos c) (huzpos c)
  have htakez : wz'.take wz.length = wz := by rw [hwz'def, List.take_left]
  have hdropz : wz'.drop wz.length = uz := by rw [hwz'def, List.drop_left]
  have hzgt : wz.length < wz'.length := by
    rw [hwz'def, List.length_append]
    have : 0 < uz.length := List.length_pos_of_ne_nil huzne
    omega
  have hsubz : cfCylinder wz' ⊆ cfCylinder wz := by
    rw [hwz'def]; exact cfCylinder_append_subset wz uz
  have hzL : L ≤ wz'.length := by
    rw [hwz'def, List.length_append]; omega
  -- (4) wz'-interval (e',f')
  obtain ⟨e', f', he'0, he'f', hf'1, hz'Icc, hz'int⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wz' hwz'ne hwz'pos
  -- (5) steer a UNIFORM freq-good x-block into (a,b) ∩ ψ⁻¹(Ioo e' f')
  have hpzIcc : pz ∈ Set.Icc e' f' := hz'Icc (by rw [hwz'def]; exact hpzmem)
  have he'pz : e' ≤ pz := hpzIcc.1
  have hpzf' : pz ≤ f' := hpzIcc.2
  obtain ⟨hpzlo, hpzhi⟩ := Set.mem_Ioo.1 hpzcd
  set a' := (e' - r) / q with ha'def
  set b' := (f' - r) / q with hb'def
  have ha'b : a' < b := (div_lt_iff₀ hq).mpr (by rw [ha'def] at *; nlinarith)
  have hab' : a < b' := (lt_div_iff₀ hq).mpr (by nlinarith)
  have ha'b' : a' < b' := by rw [ha'def, hb'def]; gcongr
  have hmax : max a a' < min b b' :=
    max_lt (lt_min hab hab') (lt_min ha'b ha'b')
  have hm0 : 0 ≤ max a a' := le_trans ha (le_max_left _ _)
  have hm1 : min b b' ≤ 1 := le_trans (min_le_left _ _) hb
  have hxsub : ∀ y ∈ Set.Ioo (max a a') (min b b'), Irrational y → y ∈ cfCylinder wx := by
    intro y hy hyirr
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy
    exact hxint y (Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_left _ _) h1,
      lt_of_lt_of_le h2 (min_le_left _ _)⟩) hyirr
  obtain ⟨ux, n₁x, huxL, huxne, huxpos, huxsubcd, hn₁xsq, huxfreq, px, hpxmem, hpxirr, hpxcd⟩ :=
    exists_uniformly_freq_good_block_steer_len wx hwx hwxpos F hF hFne hδ hm0 hmax hm1 hxsub L
  set wx' := wx ++ ux with hwx'def
  have hwx'ne : wx' ≠ [] := by simp [hwx'def, huxne]
  have hwx'pos : ∀ c ∈ wx', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (hwxpos c) (huxpos c)
  have htakex : wx'.take wx.length = wx := by rw [hwx'def, List.take_left]
  have hdropx : wx'.drop wx.length = ux := by rw [hwx'def, List.drop_left]
  have hxgt : wx.length < wx'.length := by
    rw [hwx'def, List.length_append]
    have : 0 < ux.length := List.length_pos_of_ne_nil huxne
    omega
  have hsubx : cfCylinder wx' ⊆ cfCylinder wx := by
    rw [hwx'def]; exact cfCylinder_append_subset wx ux
  have hxL : L ≤ wx'.length := by rw [hwx'def, List.length_append]; omega
  have hinv' : cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo e' f' := by
    rw [preimage_affineMap_Ioo hq]
    intro y hy
    have hy2 := huxsubcd hy
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 hy2
    exact Set.mem_Ioo.2 ⟨lt_of_le_of_lt (le_max_right _ _) h1,
      lt_of_lt_of_le h2 (min_le_right _ _)⟩
  refine ⟨wx', wz', e', f',
    ⟨hwz'ne, hwz'pos, htakez, hzgt, hzL, hsubz, ?_, n₁z, ?_, ?_⟩,
    ⟨hwx'ne, hwx'pos, htakex, hxgt, hxL, hsubx, ?_, n₁x, ?_, ?_⟩,
    ⟨he'0, he'f', hf'1, hz'int, hz'Icc⟩, hinv'⟩
  · rw [hdropz]; exact huzL
  · rw [hdropz]; exact hn₁zsq
  · rw [hdropz]; exact huzfreq
  · rw [hdropx]; exact huxL
  · rw [hdropx]; exact hn₁xsq
  · rw [hdropx]; exact huxfreq

/-- **Every genuine pattern is eventually in `wordFamily`.**  For a genuine word
`v` (nonempty, digits `≥ 1`), `v ∈ wordFamily t` for all `t ≥ max |v| (v.sum)`.
The coverage fact the two-stream recursion needs so that fixing `v` and taking
`s` large enough puts `v` in every stage family (via `wordFamily_mono`). -/
theorem mem_wordFamily_eventually (v : List ℕ) (hvne : v ≠ [])
    (hvpos : ∀ a ∈ v, 1 ≤ a) :
    ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → v ∈ wordFamily t := by
  refine ⟨max v.length v.sum, fun t ht => mem_wordFamily.2 ⟨⟨?_, ?_⟩, fun a ha => ⟨hvpos a ha, ?_⟩⟩⟩
  · exact List.length_pos_of_ne_nil hvne
  · exact le_trans (le_max_left _ _) ht
  · exact le_trans (le_trans (List.le_sum_of_mem ha) (le_max_right _ _)) ht

/-- **Abstract `hslack` telescoping** (the `o(word)` slack the hdom-free
`chain_orbit_equidist_uniform` demands).  For accumulated `word`, per-stage block
length `blk` (`word (s+1) = word s + blk s`), and slack `C` with `C =o[atTop] blk`
(each block's slack is sublinear in its length) and `blk → ∞`, plus the geometric
bound `blk s ≤ ρ · word s` (word grows at most geometrically — supplied by the
schedule's promotion rule), the shifted partial slack sums stay `< ε · word`:
`∀ ε>0, ∀ s₀, ∃ K, ∀ k≥K, ∑_{i≤k}(C(s₀+i)+c) < ε · word (s₀+k)`.  This is EXACTLY
the `hslack` conjunct of `chain_orbit_equidist_uniform` (with `c = |v|−1`).
Proof: `Asymptotics.IsLittleO.sum_range` gives `∑(C+c) =o ∑blk = word−word₀`;
the off-by-one (`range (k+1)` vs the `k`-block word) is absorbed by `blk ≤ ρ·word`
(so `word (s₀+k+1) ≤ (1+ρ)·word (s₀+k)`).  Schedule discharges: `C_s/|u_s|→0`
from `n₁²≤|u|·√|u|`; `blk→∞` from `|u_s|≥L_s→∞`; `blk≤ρ·word` from promotion. -/
theorem slack_telescoping
    (word blk C : ℕ → ℝ) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hword0 : 0 ≤ word 0)
    (hC : ∀ s, 0 ≤ C s) (hblk : ∀ s, 0 ≤ blk s)
    (hword : ∀ s, word (s + 1) = word s + blk s)
    (hgeom : ∀ s, blk s ≤ ρ * word s)
    (hClit : (fun s => C s) =o[atTop] fun s => blk s)
    (hblktop : Tendsto blk atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ s₀ : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (∑ i ∈ Finset.range (k + 1), (C (s₀ + i) + c)) < ε * word (s₀ + k) := by
  have hpsum : ∀ s₀ n : ℕ, ∑ i ∈ Finset.range n, blk (s₀ + i) = word (s₀ + n) - word s₀ := by
    intro s₀ n; induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih, Nat.add_succ, hword]; ring
  have hwordmono : ∀ a b, a ≤ b → word a ≤ word b := by
    intro a b hab
    induction b with
    | zero => interval_cases a; rfl
    | succ m ih =>
      rcases Nat.lt_or_ge a (m+1) with h | h
      · have := ih (Nat.lt_succ_iff.1 h); rw [hword m]; linarith [hblk m]
      · have hEq : a = m + 1 := le_antisymm hab h; rw [hEq]
  have hword_nonneg : ∀ n, 0 ≤ word n := fun n => le_trans hword0 (hwordmono 0 n (Nat.zero_le n))
  have hwordtop : Tendsto word atTop atTop := by
    have hsumtop : Tendsto (fun n => ∑ i ∈ Finset.range n, blk i) atTop atTop := by
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hblktop.eventually_ge_atTop 1)
      apply tendsto_atTop_mono' _ _ (tendsto_atTop_add_const_right atTop (-(N:ℝ))
        (tendsto_natCast_atTop_atTop))
      filter_upwards [Ici_mem_atTop N] with n hn
      calc ((n:ℝ) + -(N:ℝ)) = ((n - N : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; ring
        _ = ∑ _i ∈ Finset.Ico N n, (1:ℝ) := by rw [Finset.sum_const, Nat.card_Ico]; simp
        _ ≤ ∑ i ∈ Finset.Ico N n, blk i := Finset.sum_le_sum (fun i hi => hN i (Finset.mem_Ico.1 hi).1)
        _ ≤ ∑ i ∈ Finset.range n, blk i := by
            rw [← Finset.sum_range_add_sum_Ico blk hn]
            have : 0 ≤ ∑ i ∈ Finset.range N, blk i := Finset.sum_nonneg (fun i _ => hblk i)
            linarith
    have heq : word = fun n => (∑ i ∈ Finset.range n, blk i) + word 0 := by
      funext n; have := hpsum 0 n; simp only [Nat.zero_add] at this; rw [this]; ring
    rw [heq]; exact tendsto_atTop_add_const_right _ _ hsumtop
  intro ε hε s₀
  have hshift : Tendsto (fun i => s₀ + i) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat s₀
  have hCshift : (fun i => C (s₀ + i)) =o[atTop] fun i => blk (s₀ + i) :=
    hClit.comp_tendsto hshift
  have hblkshift_top : Tendsto (fun i => blk (s₀ + i)) atTop atTop := hblktop.comp hshift
  have hcshift : (fun _ : ℕ => c) =o[atTop] fun i => blk (s₀ + i) := by
    rw [isLittleO_const_left]
    refine Or.inr ?_
    simp only [Function.comp_def, Real.norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp hblkshift_top
  have hflit : (fun i => C (s₀ + i) + c) =o[atTop] fun i => blk (s₀ + i) := hCshift.add hcshift
  have hgshift_nonneg : (0 : ℕ → ℝ) ≤ fun i => blk (s₀ + i) := fun i => hblk _
  have hgshift_sumtop : Tendsto (fun n => ∑ i ∈ Finset.range n, blk (s₀ + i)) atTop atTop := by
    have : (fun n => ∑ i ∈ Finset.range n, blk (s₀ + i)) = fun n => word (s₀ + n) - word s₀ := by
      funext n; exact hpsum s₀ n
    rw [this]; exact tendsto_atTop_add_const_right _ _ (hwordtop.comp hshift)
  have hsum_o := hflit.sum_range hgshift_nonneg hgshift_sumtop
  set ε' : ℝ := ε / (2 * (1 + ρ)) with hε'def
  have h1ρ : (0:ℝ) < 1 + ρ := by linarith
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  rw [isLittleO_iff] at hsum_o
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hsum_o hε')
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hwordtop.eventually_gt_atTop 0)
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hkN₁ : N₁ ≤ k + 1 := le_trans (le_trans (le_max_left _ _) hk) (Nat.le_succ k)
  have hkN₂ : N₂ ≤ s₀ + k := le_trans (le_max_right _ _) (le_trans hk (Nat.le_add_left k s₀))
  have hbound := hN₁ (k + 1) hkN₁
  have hSf_nonneg : 0 ≤ ∑ i ∈ Finset.range (k+1), (C (s₀+i) + c) :=
    Finset.sum_nonneg (fun i _ => add_nonneg (hC _) hc)
  have hSg_nonneg : 0 ≤ ∑ i ∈ Finset.range (k+1), blk (s₀ + i) :=
    Finset.sum_nonneg (fun i _ => hblk _)
  rw [Real.norm_of_nonneg hSf_nonneg, Real.norm_of_nonneg hSg_nonneg] at hbound
  have hSg_eq : ∑ i ∈ Finset.range (k+1), blk (s₀ + i) = word (s₀ + (k+1)) - word s₀ := hpsum s₀ (k+1)
  have hword_step : word (s₀ + (k+1)) = word (s₀ + k) + blk (s₀ + k) := by
    rw [Nat.add_succ, hword]
  have hgeom_k : blk (s₀ + k) ≤ ρ * word (s₀ + k) := hgeom _
  have hwordpos : 0 < word (s₀ + k) := hN₂ (s₀ + k) hkN₂
  have hword_s0 : 0 ≤ word s₀ := hword_nonneg s₀
  have hfin : ε' * (1 + ρ) = ε / 2 := by rw [hε'def]; field_simp
  calc ∑ i ∈ Finset.range (k+1), (C (s₀+i) + c)
      ≤ ε' * ∑ i ∈ Finset.range (k+1), blk (s₀ + i) := hbound
    _ = ε' * (word (s₀ + (k+1)) - word s₀) := by rw [hSg_eq]
    _ ≤ ε' * word (s₀ + (k+1)) := by
        apply mul_le_mul_of_nonneg_left _ hε'.le; linarith
    _ = ε' * (word (s₀ + k) + blk (s₀ + k)) := by rw [hword_step]
    _ ≤ ε' * (word (s₀ + k) + ρ * word (s₀ + k)) := by
        apply mul_le_mul_of_nonneg_left _ hε'.le; linarith
    _ = (ε' * (1 + ρ)) * word (s₀ + k) := by ring
    _ = (ε / 2) * word (s₀ + k) := by rw [hfin]
    _ < ε * word (s₀ + k) := by nlinarith [hwordpos, hε]

/-! ## The two-stream interleaved recursion

The crux `exists_interleaved_affine_witness` is assembled from the ψ-round step
`exists_freq_good_extend_affine_steer_uniform` by a `Nat.rec` choice recursion,
exactly mirroring `CFSchedule.sched`.  The state `SchedStateA` carries both
streams' current genuine words `wx, wz`, the wz-interval `(e,f)`, the invariant
`cfCylinder wx ⊆ ψ⁻¹(Ioo e f)`, and `hzint` (`(e,f)` lives inside `cfCylinder
wz`'s hull).  Stage `s` refines at family `wordFamily s`, tolerance `schedEps s =
1/(s+1) → 0`, depth `L = s → ∞`.  The two chains `wxSeq`, `wzSeq` strictly extend
genuine chains, pinning limit points `xA` (and, via the shrinking interval,
`ψ(xA)`); feeding each into `chain_orbit_equidist_uniform` yields both orbit
equidistributions. -/

/-- The interleaved schedule's state: both streams' genuine words, the
wz-interval and the two coupling invariants. -/
structure SchedStateA (q r : ℝ) where
  wx : List ℕ
  wz : List ℕ
  e : ℝ
  f : ℝ
  hwxne : wx ≠ []
  hwxpos : ∀ c ∈ wx, 1 ≤ c
  hwzne : wz ≠ []
  hwzpos : ∀ c ∈ wz, 1 ≤ c
  he0 : 0 ≤ e
  hef : e < f
  hf1 : f ≤ 1
  hzint : ∀ x ∈ Set.Ioo e f, Irrational x → x ∈ cfCylinder wz
  hzhull : cfCylinder wz ⊆ Set.Icc e f
  hinv : cfCylinder wx ⊆ affineMap q r ⁻¹' Set.Ioo e f

/-- **The single-stream L4 schedule state (route B).**  Carries ONLY the `x`-stream's
genuine word `wx` and an interval `(e,f) ⊆ (0,1)` with `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)` — NO
`wz` stream (route B reads `ψ(x)`'s z-frequency statistically via pullback bad-zone
avoidance, never nesting a z-cylinder).  The step (`schedStepL4_exists`, TODO) extends `wx`
by a relative-regularization freq-good block (`exists_uniformly_freq_good_block_steer_len_rel`,
LINEAR by the crux resolution) steering into the CURRENT cylinder's own hull, and refines the
interval; the per-stage brick-3′ selection point supplies the z-avoidance record transferred
to the chain limit `ψ(xA)` via the (already axiom-clean) brick-4a transfer lemmas.  `zA :=
ψ(xA)` is DEFINITIONAL — no gluing/squeeze. -/
structure SchedStateL4 (q r : ℝ) where
  wx : List ℕ
  e : ℝ
  f : ℝ
  hwxne : wx ≠ []
  hwxpos : ∀ c ∈ wx, 1 ≤ c
  he0 : 0 ≤ e
  hef : e < f
  hf1 : f ≤ 1
  hinv : cfCylinder wx ⊆ affineMap q r ⁻¹' Set.Ioo e f

/-- The per-stage step relation: `S'` is a joint freq-good refinement of `S` at
stage `s`, recording (for both streams) that the appended block is a strict
genuine extension, reaches depth `s`, and is uniformly prefix-good for
`wordFamily s` at tolerance `schedEps s` with slack `4√|blk| + 2|v| + n₁`
(`n₁ = o(|blk|)` via `n₁² ≤ |blk|·√|blk|`).  This is exactly the conclusion of
`exists_freq_good_extend_affine_steer_uniform` with `L := s`, `δ := schedEps s`,
`F := wordFamily s`. -/
def StepSpecA {q r : ℝ} (S S' : SchedStateA q r) (s : ℕ) : Prop :=
  (S'.wz.take S.wz.length = S.wz ∧ S.wz.length < S'.wz.length ∧
      s ≤ (S'.wz.drop S.wz.length).length ∧ ∃ n₁ : ℕ,
        n₁ ^ 2 ≤ (S'.wz.drop S.wz.length).length * Nat.sqrt (S'.wz.drop S.wz.length).length ∧
        (∀ k, k ≤ (S'.wz.drop S.wz.length).length → ∀ v ∈ wordFamily s,
          |(countOccurrences v ((S'.wz.drop S.wz.length).take k) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * k|
              < schedEps s * k
                + (4 * Nat.sqrt (S'.wz.drop S.wz.length).length + 2 * v.length + n₁))) ∧
  (S'.wx.take S.wx.length = S.wx ∧ S.wx.length < S'.wx.length ∧
      s ≤ (S'.wx.drop S.wx.length).length ∧ ∃ n₁ : ℕ,
        n₁ ^ 2 ≤ (S'.wx.drop S.wx.length).length * Nat.sqrt (S'.wx.drop S.wx.length).length ∧
        (∀ k, k ≤ (S'.wx.drop S.wx.length).length → ∀ v ∈ wordFamily s,
          |(countOccurrences v ((S'.wx.drop S.wx.length).take k) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * k|
              < schedEps s * k
                + (4 * Nat.sqrt (S'.wx.drop S.wx.length).length + 2 * v.length + n₁)))

/-- Every state steps (the ψ-round step applied at stage `s`). -/
theorem schedStepA_exists {q : ℝ} (hq : 0 < q) {r : ℝ} (S : SchedStateA q r) (s : ℕ) :
    ∃ S' : SchedStateA q r, StepSpecA S S' s := by
  obtain ⟨wx', wz', e', f', hz, hx, hint, hinv'⟩ :=
    exists_freq_good_extend_affine_steer_uniform hq r S.wx S.wz S.hwxne S.hwxpos
      S.hwzne S.hwzpos S.he0 S.hef S.hf1 S.hzint S.hinv
      (wordFamily s) (wordFamily_pos s) (wordFamily_ne s) (schedEps_pos s) s
  obtain ⟨hz'ne, hz'pos, hztake, hzgt, _hzL, _hzsub, hzdropL, n₁z, hz'sq, hz'freq⟩ := hz
  obtain ⟨hx'ne, hx'pos, hxtake, hxgt, _hxL, _hxsub, hxdropL, n₁x, hx'sq, hx'freq⟩ := hx
  obtain ⟨he'0, he'f', hf'1, hz'int, hz'hull⟩ := hint
  exact ⟨⟨wx', wz', e', f', hx'ne, hx'pos, hz'ne, hz'pos, he'0, he'f', hf'1, hz'int, hz'hull, hinv'⟩,
    ⟨hztake, hzgt, hzdropL, n₁z, hz'sq, hz'freq⟩,
    ⟨hxtake, hxgt, hxdropL, n₁x, hx'sq, hx'freq⟩⟩

/-- **The seed state (feasible regime).**  For `-q < r < 1` the feasible z-region
`(max 0 r, min 1 (q+r)) = (0,1) ∩ ψ((0,1))` is a nondegenerate subinterval of
`(0,1)`; place a genuine `wz` inside it, take a small sub-interval `(e,f)` of its
hull that still lies in `[r, q+r]` (so `ψ⁻¹(e,f) ⊆ (0,1)`), and place a genuine
`wx` inside `ψ⁻¹(Ioo e f)`.  All invariants hold by construction. -/
theorem exists_seedStateA {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    Nonempty (SchedStateA q r) := by
  obtain ⟨hr1, hr2⟩ := hr
  set c := max 0 r with hcdef
  set d := min 1 (q + r) with hddef
  have hc0 : 0 ≤ c := le_max_left _ _
  have hd1 : d ≤ 1 := min_le_left _ _
  have hcr : r ≤ c := le_max_right _ _
  have hdqr : d ≤ q + r := min_le_right _ _
  have hcd : c < d := by
    apply max_lt
    · exact lt_min one_pos (by linarith)
    · exact lt_min hr2 (by linarith)
  -- place `wz` inside the feasible z-region
  obtain ⟨wz, hwzne, hwzpos, hwzsub⟩ := exists_cfCylinder_subset_Ioo hc0 hcd hd1
  -- `wz`'s hull interval `(e0,f0)` and its irrational witness `q0`
  obtain ⟨e0, f0, he00, he0f0, hf01, hwzIcc, hwzUIoo⟩ :=
    exists_Ioo_irrational_subset_cfCylinder wz hwzne hwzpos
  obtain ⟨q0, hq0irr, hq0mem⟩ := exists_irrational_mem_cfCylinder wz hwzne hwzpos
  have hq0cd := Set.mem_Ioo.1 (hwzsub hq0mem)
  have hq0Icc := Set.mem_Icc.1 (hwzIcc hq0mem)
  -- `irr(e0,f0) ⊆ cfCylinder wz ⊆ Ioo c d` forces the hull `(e0,f0) ⊆ [c,d] ⊆ [r,q+r]`
  have he0d : e0 < d := lt_of_le_of_lt hq0Icc.1 hq0cd.2
  have hcf0 : c < f0 := lt_of_lt_of_le hq0cd.1 hq0Icc.2
  have hce0 : c ≤ e0 := by
    by_contra h; push_neg at h
    obtain ⟨y, hyirr, hy1, hy2⟩ := exists_irrational_btwn h
    have hymem : y ∈ cfCylinder wz :=
      hwzUIoo y (Set.mem_Ioo.2 ⟨hy1, lt_trans hy2 hcf0⟩) hyirr
    exact absurd (Set.mem_Ioo.1 (hwzsub hymem)).1 (not_lt.2 hy2.le)
  have hf0d : f0 ≤ d := by
    by_contra h; push_neg at h
    obtain ⟨y, hyirr, hy1, hy2⟩ := exists_irrational_btwn h
    have hymem : y ∈ cfCylinder wz :=
      hwzUIoo y (Set.mem_Ioo.2 ⟨lt_trans he0d hy1, hy2⟩) hyirr
    exact absurd hy1 (not_lt.2 (Set.mem_Ioo.1 (hwzsub hymem)).2.le)
  have hre : r ≤ e0 := le_trans hcr hce0
  have hf0qr : f0 ≤ q + r := le_trans hf0d hdqr
  -- place `wx` inside `ψ⁻¹(Ioo e0 f0)`
  have hpre0 : 0 ≤ (e0 - r) / q := div_nonneg (by linarith) hq.le
  have hprelt : (e0 - r) / q < (f0 - r) / q := by
    have h : (0:ℝ) < (f0 - e0) / q := div_pos (by linarith [he0f0]) hq
    have e2 : (f0 - r) / q - (e0 - r) / q = (f0 - e0) / q := by rw [div_sub_div_same]; ring_nf
    linarith [e2, h]
  have hpre1 : (f0 - r) / q ≤ 1 := by rw [div_le_one hq]; linarith
  obtain ⟨wx, hwxne, hwxpos, hwxsub⟩ :=
    exists_cfCylinder_subset_affine_preimage hq r e0 f0 hpre0 hprelt hpre1
  exact ⟨⟨wx, wz, e0, f0, hwxne, hwxpos, hwzne, hwzpos, he00, he0f0, hf01,
    hwzUIoo, hwzIcc, hwxsub⟩⟩

/-- **The interleaved schedule** (feasible regime): the state sequence produced by
seeding with `exists_seedStateA` and iterating the choice step. -/
noncomputable def schedA {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    ℕ → SchedStateA q r
  | 0 => (exists_seedStateA hq hr).some
  | s + 1 => (schedStepA_exists hq (schedA hq hr s) s).choose

theorem schedA_step {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    StepSpecA (schedA hq hr s) (schedA hq hr (s + 1)) s :=
  (schedStepA_exists hq (schedA hq hr s) s).choose_spec

/-- The x-stream chain. -/
noncomputable def wxSeq {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) : List ℕ :=
  (schedA hq hr s).wx

/-- The z-stream chain. -/
noncomputable def wzSeq {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) : List ℕ :=
  (schedA hq hr s).wz

theorem wxSeq_ne {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    wxSeq hq hr s ≠ [] := (schedA hq hr s).hwxne

theorem wxSeq_pos {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∀ a ∈ wxSeq hq hr s, 1 ≤ a := (schedA hq hr s).hwxpos

theorem wzSeq_ne {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    wzSeq hq hr s ≠ [] := (schedA hq hr s).hwzne

theorem wzSeq_pos {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∀ a ∈ wzSeq hq hr s, 1 ≤ a := (schedA hq hr s).hwzpos

/-- The x-chain strictly extends by a nonempty block each stage. -/
theorem wxSeq_ext {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∃ u, u ≠ [] ∧ wxSeq hq hr (s + 1) = wxSeq hq hr s ++ u := by
  obtain ⟨-, hxtake, hxgt, -⟩ := schedA_step hq hr s
  refine ⟨(schedA hq hr (s + 1)).wx.drop (schedA hq hr s).wx.length, ?_, ?_⟩
  · rw [← List.length_pos_iff_ne_nil, List.length_drop]; omega
  · show (schedA hq hr (s + 1)).wx = (schedA hq hr s).wx ++ _
    conv_lhs => rw [← List.take_append_drop (schedA hq hr s).wx.length (schedA hq hr (s + 1)).wx]
    rw [hxtake]

/-- The z-chain strictly extends by a nonempty block each stage. -/
theorem wzSeq_ext {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∃ u, u ≠ [] ∧ wzSeq hq hr (s + 1) = wzSeq hq hr s ++ u := by
  obtain ⟨⟨hztake, hzgt, -⟩, -⟩ := schedA_step hq hr s
  refine ⟨(schedA hq hr (s + 1)).wz.drop (schedA hq hr s).wz.length, ?_, ?_⟩
  · rw [← List.length_pos_iff_ne_nil, List.length_drop]; omega
  · show (schedA hq hr (s + 1)).wz = (schedA hq hr s).wz ++ _
    conv_lhs => rw [← List.take_append_drop (schedA hq hr s).wz.length (schedA hq hr (s + 1)).wz]
    rw [hztake]

/-- **Interval width ≤ cylinder volume.**  If every irrational of `(e,f)` lies in
`cfCylinder w`, then `(e,f) ⊆ closure(cfCylinder w)`, so its width is at most the
cylinder volume.  Feeds the shrinking-`Icc` squeeze that pins `ψ(xA)` to the
z-chain limit. -/
theorem Ioo_sub_le_volume_cfCylinder (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) {e f : ℝ} (hef : e < f)
    (hsub : ∀ x ∈ Set.Ioo e f, Irrational x → x ∈ cfCylinder w) :
    f - e ≤ (volume (cfCylinder w)).toReal := by
  obtain ⟨a, c, hac, hlen⟩ := cfCylinder_subset_Icc_length w hw hpos
  have hae : a ≤ e := by
    by_contra h; push_neg at h
    have hlt : e < min a f := lt_min h hef
    obtain ⟨y, hyirr, hy1, hy2⟩ := exists_irrational_btwn hlt
    have hyf : y < f := lt_of_lt_of_le hy2 (min_le_right _ _)
    have hymem := hac (hsub y (Set.mem_Ioo.2 ⟨hy1, hyf⟩) hyirr)
    exact absurd hymem.1 (not_le.2 (lt_of_lt_of_le hy2 (min_le_left _ _)))
  have hfc : f ≤ c := by
    by_contra h; push_neg at h
    have hlt : max c e < f := max_lt h hef
    obtain ⟨y, hyirr, hy1, hy2⟩ := exists_irrational_btwn hlt
    have hey : e < y := lt_of_le_of_lt (le_max_right _ _) hy1
    have hymem := hac (hsub y (Set.mem_Ioo.2 ⟨hey, hy2⟩) hyirr)
    exact absurd hymem.2 (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hy1))
  linarith [hlen]

/-- **Slack is sublinear in the block length** (DISCLOSED `sorry`, dischargeable
leaf).  For a chain whose per-stage slack is `C s = 4√|blk s| + 2|v| + n₁ s` with
`n₁ s² ≤ |blk s|·√|blk s|` (so `n₁ s ≤ |blk s|^{3/4}`) and `|blk s| ≥ 1`, the slack
is `o(|blk s|)`.  Pure real-analysis (each term `√blk, const, blk^{3/4}` is
`o(blk)`); no schedule coupling.  Isolated so the crux rests only on the
route-decisive geometric bound. -/
theorem chain_slack_littleO {blk : ℕ → ℕ} (n₁ : ℕ → ℕ) (L : ℝ)
    (hblk1 : ∀ s, 1 ≤ blk s) (hn₁ : ∀ s, n₁ s ^ 2 ≤ blk s * Nat.sqrt (blk s))
    (hblktop : Filter.Tendsto (fun s => (blk s : ℝ)) Filter.atTop Filter.atTop) :
    (fun s => 4 * (Nat.sqrt (blk s) : ℝ) + L + (n₁ s : ℝ)) =o[Filter.atTop]
      fun s => (blk s : ℝ) := by
  have hbpos : ∀ s, (0 : ℝ) < blk s := fun s => by exact_mod_cast hblk1 s
  have hinv : Filter.Tendsto (fun s => ((blk s : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    hblktop.inv_tendsto_atTop
  -- `P s → 0` whenever `0 ≤ P s` and `(P s)² ≤ G s → 0` (squaring dodges `Real.sqrt`)
  have key : ∀ (P G : ℕ → ℝ), (∀ s, 0 ≤ P s) → (∀ s, (P s) ^ 2 ≤ G s) →
      Filter.Tendsto G Filter.atTop (nhds 0) → Filter.Tendsto P Filter.atTop (nhds 0) := by
    intro P G hP hle hG
    have hP2 : Filter.Tendsto (fun s => (P s) ^ 2) Filter.atTop (nhds 0) :=
      squeeze_zero (fun s => sq_nonneg _) hle hG
    have h := hP2.sqrt
    rw [Real.sqrt_zero] at h
    exact h.congr (fun s => Real.sqrt_sq (hP s))
  have hq : Filter.Tendsto (fun s => (Nat.sqrt (blk s) : ℝ) / (blk s)) Filter.atTop (nhds 0) := by
    refine key _ (fun s => ((blk s : ℝ))⁻¹) (fun s => by positivity) (fun s => ?_) hinv
    have hbp := hbpos s
    have h1 : (Nat.sqrt (blk s) : ℝ) ^ 2 ≤ (blk s : ℝ) := by exact_mod_cast Nat.sqrt_le' (blk s)
    rw [div_pow]
    calc (Nat.sqrt (blk s) : ℝ) ^ 2 / (blk s : ℝ) ^ 2
        ≤ (blk s : ℝ) / (blk s : ℝ) ^ 2 := by gcongr
      _ = ((blk s : ℝ))⁻¹ := by rw [sq, ← div_div, div_self hbp.ne', one_div]
  have hp : Filter.Tendsto (fun s => (n₁ s : ℝ) / (blk s)) Filter.atTop (nhds 0) := by
    refine key _ (fun s => (Nat.sqrt (blk s) : ℝ) / (blk s)) (fun s => by positivity)
      (fun s => ?_) hq
    have hbp := hbpos s
    have h2 : (n₁ s : ℝ) ^ 2 ≤ (blk s : ℝ) * (Nat.sqrt (blk s) : ℝ) := by exact_mod_cast hn₁ s
    rw [div_pow]
    calc (n₁ s : ℝ) ^ 2 / (blk s : ℝ) ^ 2
        ≤ ((blk s : ℝ) * (Nat.sqrt (blk s) : ℝ)) / (blk s : ℝ) ^ 2 := by gcongr
      _ = (Nat.sqrt (blk s) : ℝ) / (blk s : ℝ) := by rw [sq, mul_div_mul_left _ _ hbp.ne']
  rw [isLittleO_iff_tendsto (fun s h => absurd h (hbpos s).ne')]
  have hsum : Filter.Tendsto
      (fun s => 4 * ((Nat.sqrt (blk s) : ℝ) / blk s) + L * ((blk s : ℝ))⁻¹ + (n₁ s : ℝ) / blk s)
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = 4 * 0 + L * 0 + 0 := by ring
    rw [h0]
    exact ((hq.const_mul 4).add (hinv.const_mul L)).add hp
  refine hsum.congr (fun s => ?_)
  have hb := (hbpos s).ne'
  field_simp

/-- **Cylinder volume lower bound via `cfK`.**  `|I_w| = 1/(K(K+K')) ≥ 1/(2K²)`
(`K = cfK w`, `K' = cfK w.dropLast ≤ K`).  The rigorous link the geometric
block-length bound needs: a target interval `⊆ cfCylinder w` has width `≳ 1/cfK²`,
so the resolution length is `Nfib ≈ log_φ(1/width) ≲ log cfK`.  ⇒ the steer block
resolves in `O(log cfK w)` digits, which is `O(|w|)` ONLY IF `cfK w ≤ e^{O(|w|)}`,
i.e. the block digits are controlled (the B5′ `cfK u ≤ exp(goodC·n)` mechanism the
affine steer block currently LACKS — see `schedA_block_linear` docstring). -/
theorem volume_cfCylinder_ge_inv (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    1 / (2 * (cfK w : ℝ) ^ 2) ≤ (volume (cfCylinder w)).toReal := by
  have hK1 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hKd : (cfK w.dropLast : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast cfK_dropLast_le w hpos
  have hKd0 : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  rw [volume_cfCylinder w hw hpos, ENNReal.toReal_ofReal (by positivity)]
  apply one_div_le_one_div_of_le
  · nlinarith [hK1, hKd0]
  · nlinarith [hK1, hKd, hKd0]

/-- **A genuine cylinder has strictly positive Gauss mass.**  `γ(cfCylinder w) > 0` for a
genuine word `w`: the cylinder has positive Lebesgue volume (`volume_cfCylinder_ge_inv`,
`≥ 1/(2·cfK²)`) and the Gauss density is bounded below (`volume_le_gaussMeasure`).  The
`γwx > 0` fact the relative block-parameter regularization `S + γwx` needs to be a valid
(nonzero) denominator. -/
theorem gaussMeasure_cfCylinder_toReal_pos (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : 0 < (gaussMeasure (cfCylinder w)).toReal := by
  have hsub : cfCylinder w ⊆ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo w
  have hmeas : MeasurableSet (cfCylinder w) := measurableSet_cfCylinder w
  have hK1 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hvolpos : 0 < (volume (cfCylinder w)).toReal :=
    lt_of_lt_of_le (by positivity) (volume_cfCylinder_ge_inv w hw hpos)
  have hle := volume_le_gaussMeasure (cfCylinder w) hmeas hsub
  have hγfin : gaussMeasure (cfCylinder w) ≠ ⊤ := measure_ne_top _ _
  have hmono := ENNReal.toReal_mono hγfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hmono
  refine lt_of_lt_of_le ?_ hmono
  exact mul_pos (by positivity) hvolpos

/-- **Hull-width reciprocal ≤ `8·cfK²` (resolution input for the self-hull steer).**  For a
genuine word `w`, `4 / vol(cfCylinder w) ≤ 8·cfK(w)²`: the cylinder width is
`≥ 1/(2·cfK²)` (`volume_cfCylinder_ge_inv`).  When the L4 steer targets the cylinder's own
hull `(c,d)` with `d−c = vol(cfCylinder w)`, this is exactly the `a = 4/(d−c) ≤ 8·cfK²`
hypothesis of `exists_fib_threshold_linear_of_cfK` — so with the cfK-cap the resolution
`Nfib` is AFFINE in `|w|`. -/
theorem four_div_volume_cfCylinder_le (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    4 / (volume (cfCylinder w)).toReal ≤ 8 * (cfK w : ℝ) ^ 2 := by
  have hK1 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hge := volume_cfCylinder_ge_inv w hw hpos
  have hvolpos : 0 < (volume (cfCylinder w)).toReal :=
    lt_of_lt_of_le (by positivity) hge
  rw [div_le_iff₀ hvolpos]
  -- 4 ≤ 8·cfK²·vol, from vol ≥ 1/(2 cfK²)
  have hcfKsq : 0 < (cfK w : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hge (by positivity : (0:ℝ) ≤ 8 * (cfK w : ℝ) ^ 2)
  calc (4 : ℝ) = 8 * (cfK w : ℝ) ^ 2 * (1 / (2 * (cfK w : ℝ) ^ 2)) := by
        rw [mul_one_div, eq_div_iff (by positivity)]; ring
    _ ≤ 8 * (cfK w : ℝ) ^ 2 * (volume (cfCylinder w)).toReal := this

/-- A cylinder inside a hull `Icc a b` has `toReal`-volume at most the hull width `b−a`. -/
theorem cfCylinder_volume_toReal_le_width (w : List ℕ) {a b : ℝ}
    (hab : a ≤ b) (hsub : cfCylinder w ⊆ Set.Icc a b) :
    (volume (cfCylinder w)).toReal ≤ b - a := by
  have hmono : volume (cfCylinder w) ≤ volume (Set.Icc a b) := measure_mono hsub
  rw [Real.volume_Icc] at hmono
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
  rwa [ENNReal.toReal_ofReal (by linarith)] at h

/-- **Hull-width resolution bound.**  For a genuine cylinder sitting inside a hull `Icc a b`,
the width reciprocal `4/(b−a)` is at most `8·cfK(w)²`.  Composes
`four_div_volume_cfCylinder_le` (`4/vol ≤ 8cfK²`) with `vol ≤ b−a`
(`cfCylinder_volume_toReal_le_width`).  This is the shape
`exists_fib_threshold_linear_of_cfK` consumes (`a := 4/(b−a)`), turning the L4 self-hull
target width into the affine-in-`|w|` Fibonacci resolution once the cfK cap is threaded. -/
theorem four_div_width_le_cfK (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    {a b : ℝ} (hab : a < b) (hsub : cfCylinder w ⊆ Set.Icc a b) :
    4 / (b - a) ≤ 8 * (cfK w : ℝ) ^ 2 := by
  have hc0 : (0 : ℝ) < (cfK w : ℝ) := by
    have : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
    linarith
  have hvolpos : 0 < (volume (cfCylinder w)).toReal :=
    lt_of_lt_of_le (by positivity) (volume_cfCylinder_ge_inv w hw hpos)
  have hvolw : (volume (cfCylinder w)).toReal ≤ b - a :=
    cfCylinder_volume_toReal_le_width w hab.le hsub
  calc 4 / (b - a) ≤ 4 / (volume (cfCylinder w)).toReal := by
        rw [div_le_div_iff₀ (by linarith) hvolpos]; nlinarith [hvolw]
    _ ≤ 8 * (cfK w : ℝ) ^ 2 := four_div_volume_cfCylinder_le w hw hpos

/-- **Logarithmic fib threshold (bounded form).**  A resolution threshold `N` with
`a < fib(n+1)²` for all `n ≥ N`, AND `N ≤ log_φ(√5·√a + 1) + 1` — logarithmic in
`a`.  Packages `exists_nat_goldenRatio_pow_gt` (log-exponent solvability) with
`fib_sq_gt_of_goldenRatio` (Binet lower bound).  The prerequisite the tight
steer-block length needs: a target of width `d−c` is resolved with `Nfib ≈
log_φ(1/(d−c))` digits (not the crude `1/(d−c)`), so `Nfib ≲ |w_s|` when the
target width is `≳ φ^{−c|w_s|}` — the resolution half of `schedA_block_linear`. -/
theorem exists_fib_threshold_log (a : ℝ) :
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → a < (Nat.fib (n + 1) : ℝ) ^ 2) ∧
      (N : ℝ) ≤ Real.logb Real.goldenRatio (Real.sqrt 5 * Real.sqrt a + 1) + 1 := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_goldenRatio_pow_gt (Real.sqrt 5 * Real.sqrt a + 1)
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
  have hy1 : (1 : ℝ) ≤ Real.sqrt 5 * Real.sqrt a + 1 := by
    have : 0 ≤ Real.sqrt 5 * Real.sqrt a := by positivity
    linarith
  have hmax : max (Real.sqrt 5 * Real.sqrt a + 1) 1 = Real.sqrt 5 * Real.sqrt a + 1 :=
    max_eq_left hy1
  refine ⟨n, fun k hk => ?_, ?_⟩
  · apply fib_sq_gt_of_goldenRatio k a
    calc Real.sqrt 5 * Real.sqrt a + 1 < Real.goldenRatio ^ n := hn1
      _ ≤ Real.goldenRatio ^ (k + 1) := pow_le_pow_right₀ hφ1 (by omega)
  · rw [hmax] at hn2; exact hn2

set_option maxHeartbeats 1000000 in
/-- **Relative-regularization uniform steer block — WORD-INDEPENDENT linear length
(block-linear crux resolution).**  Identical to `exists_uniformly_freq_good_block_steer_len`
but the internal block parameter uses the RELATIVE regularizer `β_rel = γtar·δ²/(S+γwx)`
(valid since `γwx > 0`, `gaussMeasure_cfCylinder_toReal_pos`) with the TIGHT param
(`exists_uniform_block_param_tight`), and the conclusion EXPOSES the block length
`|u| = n₁ + m²` together with the tight upper bound `m² ≤ 6(L+Nfib)+2+2(⌈2/β_rel⌉+1)⁴`
and the LOGARITHMIC resolution bound `Nfib ≤ log_φ(√5·√(4/(d−c))+1)+1`
(`exists_fib_threshold_log`).  These two exposures are exactly the ingredients the L4
schedule folds — via `two_div_beta_rel_le` (`⌈2/β_rel⌉` word-independent for the self-hull
steer, `γtar ≥ γwx/8` by `gaussMeasure_middle_half_ge`) and the hull-width lower bound
(`Nfib ≲ |wx|`) — into `schedL4_block_linear`, closing the B6 crux. -/
theorem exists_uniformly_freq_good_block_steer_len_rel (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx) (L : ℕ) :
    ∃ (u : List ℕ) (n₁ m Nfib : ℕ), L ≤ u.length ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      n₁ ^ 2 ≤ u.length * Nat.sqrt u.length ∧
      (∀ k, k ≤ u.length → ∀ v ∈ F,
        |(countOccurrences v (u.take k) : ℝ) - (gaussMeasure (cfCylinder v)).toReal * k|
          < δ * k + (4 * Nat.sqrt u.length + 2 * v.length + n₁)) ∧
      (∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d) ∧
      u.length = n₁ + m ^ 2 ∧
      m ^ 2 ≤ 6 * (L + Nfib) + 2 + 2 * (Nat.ceil (2 / ((gaussMeasure
          (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal * δ ^ 2
        / (∑ v ∈ F, 7 * (8 * (v.length : ℝ) + 80) * (gaussMeasure (cfCylinder v)).toReal
            * (gaussMeasure (cfCylinder wx)).toReal
          + (gaussMeasure (cfCylinder wx)).toReal))) + 1) ^ 4 ∧
      (Nfib : ℝ) ≤ Real.logb Real.goldenRatio (Real.sqrt 5 * Real.sqrt (4 / (d - c)) + 1) + 1 := by
  have hu0v0 : c + (d - c) / 4 < d - (d - c) / 4 := by nlinarith [hcd]
  have hu00 : 0 ≤ c + (d - c) / 4 := by nlinarith [hc0, hcd]
  have hv01 : d - (d - c) / 4 ≤ 1 := by nlinarith [hd1, hcd]
  have hposreal : 0 < (Real.log (1 + (d - (d - c) / 4)) - Real.log (1 + (c + (d - c) / 4)))
      / Real.log 2 := by
    apply div_pos
    · rw [sub_pos]; apply Real.log_lt_log (by nlinarith [hu00]) (by linarith [hu0v0])
    · exact Real.log_pos (by norm_num)
  have hγtar : 0 < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
    rw [gaussMeasure_Ioo hu00 hu0v0.le hv01, ENNReal.toReal_ofReal hposreal.le]; exact hposreal
  set γtar := (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal with hγtardef
  set γwx := (gaussMeasure (cfCylinder wx)).toReal with hγwxdef
  have hγwx0 : 0 < γwx := gaussMeasure_cfCylinder_toReal_pos wx hwx hwxpos
  set S := ∑ v ∈ F, 7 * (8 * (v.length : ℝ) + 80)
      * (gaussMeasure (cfCylinder v)).toReal * γwx with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]; refine Finset.sum_nonneg fun v _ => ?_
    have : 0 ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ γwx := ENNReal.toReal_nonneg
    positivity
  set β := γtar * δ ^ 2 / (S + γwx) with hβdef
  have hSγ0 : 0 < S + γwx := by linarith [hS0, hγwx0]
  have hβ : 0 < β := by rw [hβdef]; exact div_pos (mul_pos hγtar (by positivity)) hSγ0
  obtain ⟨Nfib, hNfib, hNfiblog⟩ := exists_fib_threshold_log (4 / (d - c))
  obtain ⟨m, hm0, hLm, hNfibm, hfrac, hm2ub⟩ := exists_uniform_block_param_tight β hβ L Nfib
  have hsqrtm1 : 1 ≤ Nat.sqrt m := by
    have h := Nat.sqrt_le_sqrt (show 1 ≤ m by omega); simpa using h
  set n₁ := m * Nat.sqrt m with hn₁def
  have hn₁0 : 0 < n₁ := by rw [hn₁def]; exact Nat.mul_pos hm0 hsqrtm1
  have hn₁R : (n₁ : ℝ) = (m : ℝ) * (Nat.sqrt m : ℝ) := by rw [hn₁def]; push_cast; ring
  have hbound : ((m + 1 : ℕ) : ℝ) * (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ)))
        * γwx) < γtar := by
    have hsumeq : (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ))) * γwx)
        = S / (δ ^ 2 * (n₁ : ℝ)) := by
      rw [hSdef, Finset.sum_div]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsumeq]
    have hfrac2 : ((m : ℝ) + 1) / (n₁ : ℝ) < γtar * δ ^ 2 / (S + γwx) := by
      rw [hn₁R]; rw [hβdef] at hfrac; exact hfrac
    rw [div_lt_div_iff₀ (by rw [hn₁R]; positivity) hSγ0] at hfrac2
    -- hfrac2 : (m+1)*(S+γwx) < γtar*δ²*n₁
    have hden : (0 : ℝ) < δ ^ 2 * (n₁ : ℝ) := by rw [hn₁R]; positivity
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    push_cast
    push_cast at hfrac2
    nlinarith [hfrac2, hm1R, hγwx0, mul_pos hm1R hγwx0]
  have hres : 4 / (d - c) < (Nat.fib (wx.length + (n₁ + m ^ 2) + 1) : ℝ) ^ 2 :=
    hNfib (wx.length + (n₁ + m ^ 2)) (by omega)
  obtain ⟨u, hulen, hune, hupos, hsubcd, hufreq, x, hxcyl, hxirr, hxcd⟩ :=
    exists_uniformly_freq_good_block_steer wx hwx hwxpos F hF hFne hδ hc0 hcd hd1 hsub
      m (n₁ := n₁) hn₁0 hbound hres
  have hn₁sq : n₁ ^ 2 ≤ u.length * Nat.sqrt u.length := by
    rw [hulen]
    have hsm : Nat.sqrt m ^ 2 ≤ m := Nat.sqrt_le' m
    have h1 : n₁ ^ 2 ≤ m ^ 3 := by
      have he : n₁ ^ 2 = m ^ 2 * Nat.sqrt m ^ 2 := by rw [hn₁def]; ring
      rw [he]; nlinarith [hsm, Nat.zero_le (m ^ 2)]
    have hge : m ^ 2 ≤ n₁ + m ^ 2 := by omega
    have hsq : m ≤ Nat.sqrt (n₁ + m ^ 2) := by
      have h := Nat.sqrt_le_sqrt hge; rwa [Nat.sqrt_eq'] at h
    have h2 : m ^ 3 ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := by
      calc m ^ 3 = m ^ 2 * m := by ring
        _ ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := Nat.mul_le_mul hge hsq
    exact le_trans h1 h2
  have hfolded : ∀ k, k ≤ u.length → ∀ v ∈ F,
      |(countOccurrences v (u.take k) : ℝ) - (gaussMeasure (cfCylinder v)).toReal * k|
        < δ * k + (4 * Nat.sqrt u.length + 2 * v.length + n₁) := by
    intro k hk v hv
    set γv := (gaussMeasure (cfCylinder v)).toReal with hγvdef
    obtain ⟨hγ0v, hγ1v⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
    have hsqle : (Nat.sqrt k : ℝ) ≤ (Nat.sqrt u.length : ℝ) := by
      exact_mod_cast Nat.sqrt_le_sqrt hk
    have hn₁nn : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    by_cases hkn₁ : n₁ ≤ k
    · have hb := hufreq k hkn₁ hk v hv
      have : δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length)
          ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := by
        push_cast; nlinarith [hsqle, hn₁nn]
      calc |(countOccurrences v (u.take k) : ℝ) - γv * k|
          < δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length) := hb
        _ ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := this
    · push_neg at hkn₁
      have hvne := hFne v hv
      have hcnt : (countOccurrences v (u.take k) : ℝ) ≤ (k : ℝ) := by
        have h1 := countOccurrences_le_length hvne (u.take k)
        have h2 : (u.take k).length ≤ k := by rw [List.length_take]; exact min_le_left _ _
        exact_mod_cast le_trans h1 h2
      have hccnn : (0 : ℝ) ≤ (countOccurrences v (u.take k) : ℝ) := Nat.cast_nonneg _
      have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hcrude : |(countOccurrences v (u.take k) : ℝ) - γv * k| ≤ (k : ℝ) := by
        rw [abs_le]; constructor <;> nlinarith [hcnt, hccnn, hγ0v, hγ1v, hkR]
      have hklt : (k : ℝ) < (n₁ : ℝ) := by exact_mod_cast hkn₁
      have hδk : (0 : ℝ) ≤ δ * k := by positivity
      have hrest : (0 : ℝ) ≤ 4 * (Nat.sqrt u.length : ℝ) + 2 * v.length := by positivity
      linarith [hcrude, hklt, hδk, hrest]
  refine ⟨u, n₁, m, Nfib, by rw [hulen]; omega, hune, hupos, hsubcd, hn₁sq, hfolded,
    ⟨x, hxcyl, hxirr, hxcd⟩, hulen, ?_, hNfiblog⟩
  -- the tight m² bound: after the `set`s the goal is folded to β's components
  rw [hβdef] at hm2ub
  exact hm2ub

set_option maxHeartbeats 1000000 in
/-- **Relative-regularization uniform steer block WITH the cfK cap** (cfK-graft layer 3 —
the block builder `schedL4_block_linear` calls).  Mirror of
`exists_uniformly_freq_good_block_steer_len_rel` calling the layer-2 cfK builder.  Because
the freq measure budget (`(m+1)·A₁`) and the cfK-large mass must BOTH fit under `γtar` and
`m` is chosen internally, the relative regularizer is HALVED (`β = γtar·δ²/(2(S+γwx))`,
`⌈4/β_rel⌉` in the `m²` bound — still word-independent) so the freq budget targets `γtar/2`;
the caller supplies the UNIFORM cfK-mass room `hcfK : ∀ n, γ(cfKbadExtSet wx κ n) ≤ γtar/2`
(dischargeable at the self-hull via `exists_rate_gaussMeasure_cfKbadExtSet_le` +
`gaussMeasure_middle_half_ge` + the Gauss density bounds).  Exposes `cfK u ≤ e^{κ|u|}`
alongside the length data. -/
theorem exists_uniformly_freq_good_block_steer_len_rel_cfK (wx : List ℕ) (hwx : wx ≠ [])
    (hwxpos : ∀ a ∈ wx, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hsub : ∀ y ∈ Set.Ioo c d, Irrational y → y ∈ cfCylinder wx) (L : ℕ) (κ : ℝ)
    (hcfK : ∀ n : ℕ, (gaussMeasure (cfKbadExtSet wx κ n)).toReal
      ≤ (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal / 2) :
    ∃ (u : List ℕ) (n₁ m Nfib : ℕ), L ≤ u.length ∧ u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) ∧
      cfCylinder (wx ++ u) ⊆ Set.Ioo c d ∧
      n₁ ^ 2 ≤ u.length * Nat.sqrt u.length ∧
      (∀ k, k ≤ u.length → ∀ v ∈ F,
        |(countOccurrences v (u.take k) : ℝ) - (gaussMeasure (cfCylinder v)).toReal * k|
          < δ * k + (4 * Nat.sqrt u.length + 2 * v.length + n₁)) ∧
      (∃ x : ℝ, x ∈ cfCylinder (wx ++ u) ∧ Irrational x ∧ x ∈ Set.Ioo c d) ∧
      (cfK u : ℝ) ≤ Real.exp (κ * (u.length : ℝ)) ∧
      u.length = n₁ + m ^ 2 ∧
      m ^ 2 ≤ 6 * (L + Nfib) + 2 + 2 * (Nat.ceil (2 / ((gaussMeasure
          (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal * δ ^ 2
        / (2 * (∑ v ∈ F, 7 * (8 * (v.length : ℝ) + 80) * (gaussMeasure (cfCylinder v)).toReal
            * (gaussMeasure (cfCylinder wx)).toReal
          + (gaussMeasure (cfCylinder wx)).toReal)))) + 1) ^ 4 ∧
      (Nfib : ℝ) ≤ Real.logb Real.goldenRatio (Real.sqrt 5 * Real.sqrt (4 / (d - c)) + 1) + 1 := by
  have hu0v0 : c + (d - c) / 4 < d - (d - c) / 4 := by nlinarith [hcd]
  have hu00 : 0 ≤ c + (d - c) / 4 := by nlinarith [hc0, hcd]
  have hv01 : d - (d - c) / 4 ≤ 1 := by nlinarith [hd1, hcd]
  have hposreal : 0 < (Real.log (1 + (d - (d - c) / 4)) - Real.log (1 + (c + (d - c) / 4)))
      / Real.log 2 := by
    apply div_pos
    · rw [sub_pos]; apply Real.log_lt_log (by nlinarith [hu00]) (by linarith [hu0v0])
    · exact Real.log_pos (by norm_num)
  have hγtar : 0 < (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal := by
    rw [gaussMeasure_Ioo hu00 hu0v0.le hv01, ENNReal.toReal_ofReal hposreal.le]; exact hposreal
  set γtar := (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal with hγtardef
  set γwx := (gaussMeasure (cfCylinder wx)).toReal with hγwxdef
  have hγwx0 : 0 < γwx := gaussMeasure_cfCylinder_toReal_pos wx hwx hwxpos
  set S := ∑ v ∈ F, 7 * (8 * (v.length : ℝ) + 80)
      * (gaussMeasure (cfCylinder v)).toReal * γwx with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]; refine Finset.sum_nonneg fun v _ => ?_
    have : 0 ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ γwx := ENNReal.toReal_nonneg
    positivity
  set β := γtar * δ ^ 2 / (2 * (S + γwx)) with hβdef
  have hSγ0 : 0 < S + γwx := by linarith [hS0, hγwx0]
  have hβ : 0 < β := by rw [hβdef]; exact div_pos (mul_pos hγtar (by positivity)) (by linarith [hSγ0])
  obtain ⟨Nfib, hNfib, hNfiblog⟩ := exists_fib_threshold_log (4 / (d - c))
  obtain ⟨m, hm0, hLm, hNfibm, hfrac, hm2ub⟩ := exists_uniform_block_param_tight β hβ L Nfib
  have hsqrtm1 : 1 ≤ Nat.sqrt m := by
    have h := Nat.sqrt_le_sqrt (show 1 ≤ m by omega); simpa using h
  set n₁ := m * Nat.sqrt m with hn₁def
  have hn₁0 : 0 < n₁ := by rw [hn₁def]; exact Nat.mul_pos hm0 hsqrtm1
  have hn₁R : (n₁ : ℝ) = (m : ℝ) * (Nat.sqrt m : ℝ) := by rw [hn₁def]; push_cast; ring
  -- freq mass < γtar/2
  have hfreqhalf : ((m + 1 : ℕ) : ℝ) * (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ)))
        * γwx) < γtar / 2 := by
    have hsumeq : (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ))) * γwx)
        = S / (δ ^ 2 * (n₁ : ℝ)) := by
      rw [hSdef, Finset.sum_div]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsumeq]
    have hfrac2 : ((m : ℝ) + 1) / (n₁ : ℝ) < γtar * δ ^ 2 / (2 * (S + γwx)) := by
      rw [hn₁R]; rw [hβdef] at hfrac; exact hfrac
    rw [div_lt_div_iff₀ (by rw [hn₁R]; positivity) (by linarith [hSγ0])] at hfrac2
    -- hfrac2 : (m+1)*(2*(S+γwx)) < γtar*δ²*n₁
    have hden : (0 : ℝ) < δ ^ 2 * (n₁ : ℝ) := by rw [hn₁R]; positivity
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    push_cast
    push_cast at hfrac2
    nlinarith [hfrac2, hm1R, hγwx0, mul_pos hm1R hγwx0]
  -- combined budget for layer 2 cfK: freq + cfK mass < γtar
  have hbound : ((m + 1 : ℕ) : ℝ) * (∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
        * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * (n₁ : ℝ)))
        * γwx)
        + (gaussMeasure (cfKbadExtSet wx κ (n₁ + m ^ 2))).toReal < γtar := by
    have hc2 := hcfK (n₁ + m ^ 2)
    linarith [hfreqhalf, hc2]
  have hres : 4 / (d - c) < (Nat.fib (wx.length + (n₁ + m ^ 2) + 1) : ℝ) ^ 2 :=
    hNfib (wx.length + (n₁ + m ^ 2)) (by omega)
  obtain ⟨u, hulen, hune, hupos, hsubcd, hufreq, hcfKu, x, hxcyl, hxirr, hxcd⟩ :=
    exists_uniformly_freq_good_block_steer_cfK wx hwx hwxpos F hF hFne hδ hc0 hcd hd1 hsub
      m (n₁ := n₁) hn₁0 κ hbound hres
  have hn₁sq : n₁ ^ 2 ≤ u.length * Nat.sqrt u.length := by
    rw [hulen]
    have hsm : Nat.sqrt m ^ 2 ≤ m := Nat.sqrt_le' m
    have h1 : n₁ ^ 2 ≤ m ^ 3 := by
      have he : n₁ ^ 2 = m ^ 2 * Nat.sqrt m ^ 2 := by rw [hn₁def]; ring
      rw [he]; nlinarith [hsm, Nat.zero_le (m ^ 2)]
    have hge : m ^ 2 ≤ n₁ + m ^ 2 := by omega
    have hsq : m ≤ Nat.sqrt (n₁ + m ^ 2) := by
      have h := Nat.sqrt_le_sqrt hge; rwa [Nat.sqrt_eq'] at h
    have h2 : m ^ 3 ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := by
      calc m ^ 3 = m ^ 2 * m := by ring
        _ ≤ (n₁ + m ^ 2) * Nat.sqrt (n₁ + m ^ 2) := Nat.mul_le_mul hge hsq
    exact le_trans h1 h2
  have hfolded : ∀ k, k ≤ u.length → ∀ v ∈ F,
      |(countOccurrences v (u.take k) : ℝ) - (gaussMeasure (cfCylinder v)).toReal * k|
        < δ * k + (4 * Nat.sqrt u.length + 2 * v.length + n₁) := by
    intro k hk v hv
    set γv := (gaussMeasure (cfCylinder v)).toReal with hγvdef
    obtain ⟨hγ0v, hγ1v⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
    have hsqle : (Nat.sqrt k : ℝ) ≤ (Nat.sqrt u.length : ℝ) := by
      exact_mod_cast Nat.sqrt_le_sqrt hk
    have hn₁nn : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    by_cases hkn₁ : n₁ ≤ k
    · have hb := hufreq k hkn₁ hk v hv
      have : δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length)
          ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := by
        push_cast; nlinarith [hsqle, hn₁nn]
      calc |(countOccurrences v (u.take k) : ℝ) - γv * k|
          < δ * k + (4 * (Nat.sqrt k : ℝ) + 2 * v.length) := hb
        _ ≤ δ * k + (4 * (Nat.sqrt u.length : ℝ) + 2 * v.length + n₁) := this
    · push_neg at hkn₁
      have hvne := hFne v hv
      have hcnt : (countOccurrences v (u.take k) : ℝ) ≤ (k : ℝ) := by
        have h1 := countOccurrences_le_length hvne (u.take k)
        have h2 : (u.take k).length ≤ k := by rw [List.length_take]; exact min_le_left _ _
        exact_mod_cast le_trans h1 h2
      have hccnn : (0 : ℝ) ≤ (countOccurrences v (u.take k) : ℝ) := Nat.cast_nonneg _
      have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hcrude : |(countOccurrences v (u.take k) : ℝ) - γv * k| ≤ (k : ℝ) := by
        rw [abs_le]; constructor <;> nlinarith [hcnt, hccnn, hγ0v, hγ1v, hkR]
      have hklt : (k : ℝ) < (n₁ : ℝ) := by exact_mod_cast hkn₁
      have hδk : (0 : ℝ) ≤ δ * k := by positivity
      have hrest : (0 : ℝ) ≤ 4 * (Nat.sqrt u.length : ℝ) + 2 * v.length := by positivity
      linarith [hcrude, hklt, hδk, hrest]
  refine ⟨u, n₁, m, Nfib, by rw [hulen]; omega, hune, hupos, hsubcd, hn₁sq, hfolded,
    ⟨x, hxcyl, hxirr, hxcd⟩, hcfKu, hulen, ?_, hNfiblog⟩
  rw [hβdef] at hm2ub
  exact hm2ub

/-- **Global cfK rate discharging the layer-3 `hcfK`** (the route-decisive feasibility
of the cfK cap, settled in-kernel).  There is a WORD-INDEPENDENT rate `κ` so that for
every genuine cylinder inside a hull `Icc c d ⊆ [0,1]`, the cfK-large extension mass is
`≤ ½·γtar` (γtar = middle-half of the hull) — exactly layer 3's `hcfK` hypothesis.
`ε := 1/32` suffices: `γ(cfKbad) ≤ vol(wx)/(32 ln2) ≤ (d−c)/(32 ln2)` (rate lemma +
`vol(wx) ≤ d−c` since the cylinder sits in the hull), while `γtar ≥ ¼·γ(c,d) ≥
(d−c)/(8 ln2)` (`gaussMeasure_middle_half_ge` + the lower Gauss density), so `γtar/2 ≥
(d−c)/(16 ln2) ≥ (d−c)/(32 ln2)`.  NB the bound goes THROUGH the hull width `d−c`, never
`γwx` — so no cylinder/hull atom bookkeeping is needed. -/
theorem exists_kappa_cfKbadExtSet_le_half_middle :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (wx : List ℕ), wx ≠ [] → (∀ a ∈ wx, 1 ≤ a) →
      ∀ (c d : ℝ), 0 ≤ c → c < d → d ≤ 1 → cfCylinder wx ⊆ Set.Icc c d →
      ∀ n : ℕ, (gaussMeasure (cfKbadExtSet wx κ n)).toReal
        ≤ (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal / 2 := by
  obtain ⟨κ, hκ, hrate⟩ := exists_rate_gaussMeasure_cfKbadExtSet_le (1/32) (by norm_num)
  refine ⟨κ, hκ, fun wx hwx hpos c d hc0 hcd hd1 hhull n => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := hrate wx hwx hpos n
  have hvfin : volume (cfCylinder wx) ≠ ⊤ := by
    have h1 : volume (cfCylinder wx) ≤ volume (Set.Ioo (0:ℝ) 1) :=
      measure_mono (cfCylinder_subset_Ioo wx)
    rw [Real.volume_Ioo] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hcfKbadReal : (gaussMeasure (cfKbadExtSet wx κ n)).toReal
      ≤ (Real.log 2)⁻¹ * (1/32) * (volume (cfCylinder wx)).toReal := by
    have hfin : ENNReal.ofReal ((Real.log 2)⁻¹ * (1/32)) * volume (cfCylinder wx) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvfin
    have hmono := ENNReal.toReal_mono hfin hr
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hmono
  have hV0 : 0 ≤ (volume (cfCylinder wx)).toReal := ENNReal.toReal_nonneg
  have hvolle : (volume (cfCylinder wx)).toReal ≤ d - c := by
    have hm : volume (cfCylinder wx) ≤ volume (Set.Icc c d) := measure_mono hhull
    rw [Real.volume_Icc] at hm
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rwa [ENNReal.toReal_ofReal (by linarith)] at hmono
  have hmid := gaussMeasure_middle_half_ge hc0 hcd.le hd1
  have hlow := gaussMeasure_Ioo_toReal_ge hc0 hcd.le hd1
  set γtar := (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal with hγtardef
  set G := (gaussMeasure (Set.Ioo c d)).toReal with hGdef
  have hcfKbad2 : (gaussMeasure (cfKbadExtSet wx κ n)).toReal
      ≤ (Real.log 2)⁻¹ * (1/32) * (d - c) := by
    have hcoef : 0 ≤ (Real.log 2)⁻¹ * (1/32) := by positivity
    calc (gaussMeasure (cfKbadExtSet wx κ n)).toReal
        ≤ (Real.log 2)⁻¹ * (1/32) * (volume (cfCylinder wx)).toReal := hcfKbadReal
      _ ≤ (Real.log 2)⁻¹ * (1/32) * (d - c) := mul_le_mul_of_nonneg_left hvolle hcoef
  have hγtar0 : 0 ≤ γtar := ENNReal.toReal_nonneg
  have hGlow : (d - c) ≤ 2 * Real.log 2 * G := by
    rw [div_le_iff₀ (by positivity)] at hlow; linarith [hlow]
  have hγtar_ge : (d - c) ≤ 8 * Real.log 2 * γtar := by
    nlinarith [hGlow, mul_le_mul_of_nonneg_left hmid (show (0:ℝ) ≤ 8 * Real.log 2 by positivity)]
  have hkey : (Real.log 2)⁻¹ * (1/32) * (d - c) ≤ γtar / 2 := by
    have hcoef : 0 ≤ (Real.log 2)⁻¹ * (1/32) := by positivity
    calc (Real.log 2)⁻¹ * (1/32) * (d - c)
        ≤ (Real.log 2)⁻¹ * (1/32) * (8 * Real.log 2 * γtar) :=
          mul_le_mul_of_nonneg_left hγtar_ge hcoef
      _ = (1/4) * γtar := by
          rw [show (Real.log 2)⁻¹ * (1/32) * (8 * Real.log 2 * γtar)
              = (1/4) * γtar * ((Real.log 2)⁻¹ * Real.log 2) by ring,
            inv_mul_cancel₀ (ne_of_gt hl2), mul_one]
      _ ≤ γtar / 2 := by linarith [hγtar0]
  linarith [hcfKbad2, hkey]

/-- The globally-fixed cfK rate for the L4 schedule (from
`exists_kappa_cfKbadExtSet_le_half_middle`).  Fixed once so every step's block carries
`cfK u ≤ exp(schedKappaL4·|u|)` with the SAME rate, which the recursion accumulates via
`cfK_append_le`. -/
noncomputable def schedKappaL4 : ℝ := (exists_kappa_cfKbadExtSet_le_half_middle).choose

theorem schedKappaL4_pos : 0 < schedKappaL4 :=
  (exists_kappa_cfKbadExtSet_le_half_middle).choose_spec.1

theorem schedKappaL4_spec (wx : List ℕ) (hwx : wx ≠ []) (hpos : ∀ a ∈ wx, 1 ≤ a)
    (c d : ℝ) (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) (hhull : cfCylinder wx ⊆ Set.Icc c d)
    (n : ℕ) : (gaussMeasure (cfKbadExtSet wx schedKappaL4 n)).toReal
      ≤ (gaussMeasure (Set.Ioo (c + (d - c) / 4) (d - (d - c) / 4))).toReal / 2 :=
  (exists_kappa_cfKbadExtSet_le_half_middle).choose_spec.2 wx hwx hpos c d hc0 hcd hd1 hhull n

/-- **The single-stream L4 step relation.**  `S'` extends `S`'s word by a strict genuine
block reaching depth `s`, uniformly prefix-good for `wordFamily s` at tolerance `schedEps s`
(slack `4√|blk|+2|v|+n₁`, `n₁²≤|blk|·√|blk|`).  Same shape as `StepSpecA`'s x-half — the
x-side chain frequency (`chain_hfreq_of_uniform_blocks`) consumes exactly this.  The
appended block comes from the RELATIVE-regularization steer into the current cylinder's own
hull (`exists_uniformly_freq_good_block_steer_len_rel`), which additionally exposes the
LINEAR length bound feeding `schedL4_block_linear` (recorded separately, needs the cfK-cap). -/
def StepSpecL4 {q r : ℝ} (S S' : SchedStateL4 q r) (s : ℕ) : Prop :=
  S'.wx.take S.wx.length = S.wx ∧ S.wx.length < S'.wx.length ∧
    s ≤ (S'.wx.drop S.wx.length).length ∧
    ∃ (a b : ℝ) (n₁ m Nfib : ℕ),
      0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ cfCylinder S.wx ⊆ Set.Icc a b ∧
      (S'.wx.drop S.wx.length).length = n₁ + m ^ 2 ∧
      n₁ ^ 2 ≤ (S'.wx.drop S.wx.length).length * Nat.sqrt (S'.wx.drop S.wx.length).length ∧
      (∀ k, k ≤ (S'.wx.drop S.wx.length).length → ∀ v ∈ wordFamily s,
        |(countOccurrences v ((S'.wx.drop S.wx.length).take k) : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * k|
            < schedEps s * k
              + (4 * Nat.sqrt (S'.wx.drop S.wx.length).length + 2 * v.length + n₁)) ∧
      (cfK (S'.wx.drop S.wx.length) : ℝ)
          ≤ Real.exp (schedKappaL4 * ((S'.wx.drop S.wx.length).length : ℝ)) ∧
      m ^ 2 ≤ 6 * (s + Nfib) + 2 + 2 * (Nat.ceil (2 / ((gaussMeasure
          (Set.Ioo (a + (b - a) / 4) (b - (b - a) / 4))).toReal * schedEps s ^ 2
        / (2 * (∑ v ∈ wordFamily s, 7 * (8 * (v.length : ℝ) + 80)
              * (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure (cfCylinder S.wx)).toReal
          + (gaussMeasure (cfCylinder S.wx)).toReal)))) + 1) ^ 4 ∧
      (Nfib : ℝ) ≤ Real.logb Real.goldenRatio (Real.sqrt 5 * Real.sqrt (4 / (b - a)) + 1) + 1

/-- **Every L4 state steps** (single-stream, route B).  Extend `wx` by a
relative-regularization freq-good block steering into the cylinder's OWN hull (so the block
is LINEAR by the crux resolution), keeping the interval `(e,f)` FIXED — legitimate because
`cfCylinder (wx++u) ⊆ cfCylinder wx ⊆ ψ⁻¹(Ioo e f)`, so `hinv` is preserved.  (Route B does
NOT nest the interval; `ψ(xA)` is pinned by the cylinder shrinking, not the interval.) -/
theorem schedStepL4_exists {q : ℝ} (hq : 0 < q) {r : ℝ} (S : SchedStateL4 q r) (s : ℕ) :
    ∃ S' : SchedStateL4 q r, StepSpecL4 S S' s := by
  obtain ⟨a, b, ha, hab, hb, hIcc, hIoo⟩ :=
    exists_Ioo_irrational_subset_cfCylinder S.wx S.hwxne S.hwxpos
  obtain ⟨u, n₁, m, Nfib, huL, hune, hupos, hsubcd, hn₁sq, hufreq, _hwit, hcfKu, hlen, hm2, hNf⟩ :=
    exists_uniformly_freq_good_block_steer_len_rel_cfK S.wx S.hwxne S.hwxpos
      (wordFamily s) (wordFamily_pos s) (wordFamily_ne s) (schedEps_pos s)
      ha hab hb hIoo s schedKappaL4
      (schedKappaL4_spec S.wx S.hwxne S.hwxpos a b ha hab hb hIcc)
  set wx' := S.wx ++ u with hwx'def
  have hwx'ne : wx' ≠ [] := by rw [hwx'def]; simp [hune]
  have hwx'pos : ∀ c ∈ wx', 1 ≤ c := fun c hc =>
    (List.mem_append.1 hc).elim (S.hwxpos c) (hupos c)
  have htake : wx'.take S.wx.length = S.wx := by rw [hwx'def, List.take_left]
  have hdrop : wx'.drop S.wx.length = u := by rw [hwx'def, List.drop_left]
  have hsub : cfCylinder wx' ⊆ cfCylinder S.wx := by
    rw [hwx'def]; exact cfCylinder_append_subset S.wx u
  have hinv' : cfCylinder wx' ⊆ affineMap q r ⁻¹' Set.Ioo S.e S.f :=
    hsub.trans S.hinv
  have hgt : S.wx.length < wx'.length := by
    rw [hwx'def, List.length_append]
    have : 0 < u.length := List.length_pos_of_ne_nil hune
    omega
  refine ⟨⟨wx', S.e, S.f, hwx'ne, hwx'pos, S.he0, S.hef, S.hf1, hinv'⟩, htake, hgt, ?_,
    a, b, n₁, m, Nfib, ha, hab, hb, hIcc, ?_, ?_, ?_, ?_, hm2, hNf⟩
  · rw [hdrop]; exact huL
  · rw [hdrop]; exact hlen
  · rw [hdrop]; exact hn₁sq
  · rw [hdrop]; exact hufreq
  · rw [hdrop]; exact hcfKu

/-- **The single-stream L4 seed.**  Reuse the two-stream feasible seed's x-side data
(`exists_seedStateA` already places `wx` inside `ψ⁻¹(Ioo e f)`); drop the `wz` stream. -/
theorem exists_seedStateL4 {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    Nonempty (SchedStateL4 q r) := by
  obtain ⟨S⟩ := exists_seedStateA hq hr
  exact ⟨⟨S.wx, S.e, S.f, S.hwxne, S.hwxpos, S.he0, S.hef, S.hf1, S.hinv⟩⟩

/-- **The single-stream L4 schedule**: seed with `exists_seedStateL4`, iterate the
choice step `schedStepL4_exists`. -/
noncomputable def schedL4 {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    ℕ → SchedStateL4 q r
  | 0 => (exists_seedStateL4 hq hr).some
  | s + 1 => (schedStepL4_exists hq (schedL4 hq hr s) s).choose

theorem schedL4_step {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    StepSpecL4 (schedL4 hq hr s) (schedL4 hq hr (s + 1)) s :=
  (schedStepL4_exists hq (schedL4 hq hr s) s).choose_spec

/-- The L4 x-chain. -/
noncomputable def wxSeq_L4 {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    List ℕ := (schedL4 hq hr s).wx

theorem wxSeq_L4_ne {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    wxSeq_L4 hq hr s ≠ [] := (schedL4 hq hr s).hwxne

theorem wxSeq_L4_pos {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∀ a ∈ wxSeq_L4 hq hr s, 1 ≤ a := (schedL4 hq hr s).hwxpos

/-- The L4 x-chain strictly extends by a nonempty block each stage. -/
theorem wxSeq_L4_ext {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    ∃ u, u ≠ [] ∧ wxSeq_L4 hq hr (s + 1) = wxSeq_L4 hq hr s ++ u := by
  obtain ⟨hxtake, hxgt, -⟩ := schedL4_step hq hr s
  refine ⟨(schedL4 hq hr (s + 1)).wx.drop (schedL4 hq hr s).wx.length, ?_, ?_⟩
  · rw [← List.length_pos_iff_ne_nil, List.length_drop]; omega
  · show (schedL4 hq hr (s + 1)).wx = (schedL4 hq hr s).wx ++ _
    conv_lhs => rw [← List.take_append_drop (schedL4 hq hr s).wx.length (schedL4 hq hr (s + 1)).wx]
    rw [hxtake]

/-- **Block length is at most `2m²+7`** (the `n₁` burn-in is dominated by `m²`).  From
`|b| = n₁ + m²` and the sublinear-slack witness `n₁² ≤ |b|·√|b|`: either `n₁ ≤ m²`
(so `|b| ≤ 2m²`), or `m² < n₁`, forcing `|b| < 2n₁` and hence — via `n₁² ≤ |b|·√|b|` —
`n₁ ≤ 7`, so `|b| = n₁+m² ≤ m²+7`.  Either way `|b| ≤ 2m²+7`, i.e. the block length is
controlled by the tight parameter `m²` alone (word-independent up to the `m²` bound). -/
theorem block_len_le {b n₁ m : ℕ} (hlen : b = n₁ + m ^ 2)
    (hsq : n₁ ^ 2 ≤ b * Nat.sqrt b) : b ≤ 2 * m ^ 2 + 7 := by
  by_cases hnm : n₁ ≤ m ^ 2
  · omega
  · push_neg at hnm
    set t := Nat.sqrt b with htdef
    have ht2 : t ^ 2 ≤ b := Nat.sqrt_le' b
    have hb2 : b < 2 * n₁ := by omega
    have hn1pos : 1 ≤ n₁ := by omega
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h
      · exfalso; rw [h0, Nat.mul_zero] at hsq; nlinarith [hsq, hn1pos]
      · exact h
    have hlt : n₁ < 2 * t := by nlinarith [hsq, hb2, hn1pos, ht1]
    have ht3 : t ≤ 3 := by nlinarith [ht2, hb2, hlt, ht1]
    omega

/-- **Accumulated cfK bound along the L4 chain** (recursion of the per-block cfK cap).
Each step's block carries `cfK u ≤ exp(schedKappaL4·|u|)` (`StepSpecL4`); the append law
`cfK_append_le` (factor 2) folds these into a SINGLE exponential in the whole word length,
absorbing the `2^s` into the rate via `s ≤ |wxSeq_L4 s|` (⇒ `2 ≤ 2^{|blockₛ|}` since blocks
are nonempty).  This is the log-cfK linear bound that makes the Fibonacci resolution `Nfib`
affine in `|wx|` — the recursion input to `schedL4_block_linear`. -/
theorem cfK_wxSeq_L4_le {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) (s : ℕ) :
    (cfK (wxSeq_L4 hq hr s) : ℝ)
      ≤ (cfK (wxSeq_L4 hq hr 0) : ℝ)
        * Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ)) := by
  have hκ : 0 ≤ schedKappaL4 := schedKappaL4_pos.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ schedKappaL4 + Real.log 2 := by linarith
  induction s with
  | zero =>
    have h1 : (1 : ℝ) ≤ Real.exp ((schedKappaL4 + Real.log 2)
        * ((wxSeq_L4 hq hr 0).length : ℝ)) :=
      Real.one_le_exp (by positivity)
    exact le_mul_of_one_le_right (by positivity) h1
  | succ s ih =>
    set block := (schedL4 hq hr (s + 1)).wx.drop (schedL4 hq hr s).wx.length with hblockdef
    obtain ⟨htake, _hgt, _hslen, a, b, n₁, m, Nfib, _ha, _hab, _hb, _hIcc,
      _hlen, _hn₁sq, _hfreq, hcfKb, _hm2, _hNf⟩ := schedL4_step hq hr s
    -- the chain splits `W(s+1) = W s ++ block`
    have hWeq : wxSeq_L4 hq hr (s + 1) = wxSeq_L4 hq hr s ++ block := by
      show (schedL4 hq hr (s + 1)).wx = (schedL4 hq hr s).wx ++ block
      conv_lhs =>
        rw [← List.take_append_drop (schedL4 hq hr s).wx.length (schedL4 hq hr (s + 1)).wx]
      rw [htake]
    have hWne : wxSeq_L4 hq hr s ≠ [] := wxSeq_L4_ne hq hr s
    have hbne : block ≠ [] := by
      rw [hblockdef, ← List.length_pos_iff_ne_nil, List.length_drop]; omega
    have hbpos : ∀ c ∈ block, 1 ≤ c := fun c hc =>
      (schedL4 hq hr (s + 1)).hwxpos c (List.mem_of_mem_drop hc)
    have hb1 : 1 ≤ block.length := List.length_pos_of_ne_nil hbne
    -- lengths add
    have hlenadd : ((wxSeq_L4 hq hr (s + 1)).length : ℝ)
        = ((wxSeq_L4 hq hr s).length : ℝ) + (block.length : ℝ) := by
      rw [hWeq, List.length_append]; push_cast; ring
    -- cfK append law
    have happ : (cfK (wxSeq_L4 hq hr (s + 1)) : ℝ)
        ≤ 2 * ((cfK (wxSeq_L4 hq hr s) : ℝ) * (cfK block : ℝ)) := by
      have h := cfK_append_le (wxSeq_L4 hq hr s) block hWne hbne (wxSeq_L4_pos hq hr s) hbpos
      rw [← hWeq] at h
      exact_mod_cast h
    -- the per-block cfK cap (from the step); note the drop is defeq to `block`
    have hcap : (cfK block : ℝ) ≤ Real.exp (schedKappaL4 * (block.length : ℝ)) := hcfKb
    have hcfK0 : (0 : ℝ) ≤ (cfK (wxSeq_L4 hq hr s) : ℝ) := by positivity
    have hcfKb0 : (0 : ℝ) ≤ (cfK block : ℝ) := by positivity
    -- assemble
    calc (cfK (wxSeq_L4 hq hr (s + 1)) : ℝ)
        ≤ 2 * ((cfK (wxSeq_L4 hq hr s) : ℝ) * (cfK block : ℝ)) := happ
      _ ≤ 2 * (((cfK (wxSeq_L4 hq hr 0) : ℝ)
            * Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ)))
          * Real.exp (schedKappaL4 * (block.length : ℝ))) := by
        gcongr
      _ ≤ (cfK (wxSeq_L4 hq hr 0) : ℝ)
            * Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr (s + 1)).length : ℝ)) := by
        rw [hlenadd]
        rw [show (schedKappaL4 + Real.log 2)
              * ((wxSeq_L4 hq hr s).length + (block.length : ℝ))
            = ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ))
              + (schedKappaL4 * (block.length : ℝ) + Real.log 2 * (block.length : ℝ)) by ring,
          Real.exp_add, Real.exp_add]
        have hle : (2 : ℝ) ≤ Real.exp (Real.log 2 * (block.length : ℝ)) := by
          have hb1R : (1 : ℝ) ≤ (block.length : ℝ) := by exact_mod_cast hb1
          have hmono : Real.exp (Real.log 2 * 1) ≤ Real.exp (Real.log 2 * (block.length : ℝ)) :=
            Real.exp_le_exp.2 (by nlinarith [hl2.le, hb1R])
          rwa [mul_one, Real.exp_log (by norm_num)] at hmono
        set P := (cfK (wxSeq_L4 hq hr 0) : ℝ)
            * Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ))
            * Real.exp (schedKappaL4 * (block.length : ℝ)) with hPdef
        have hAX : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
        calc 2 * ((cfK (wxSeq_L4 hq hr 0) : ℝ)
              * Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ))
              * Real.exp (schedKappaL4 * (block.length : ℝ)))
            = P * 2 := by rw [hPdef]; ring
          _ ≤ P * Real.exp (Real.log 2 * (block.length : ℝ)) :=
              mul_le_mul_of_nonneg_left hle hAX
          _ = (cfK (wxSeq_L4 hq hr 0) : ℝ)
              * (Real.exp ((schedKappaL4 + Real.log 2) * ((wxSeq_L4 hq hr s).length : ℝ))
                * (Real.exp (schedKappaL4 * (block.length : ℝ))
                  * Real.exp (Real.log 2 * (block.length : ℝ)))) := by rw [hPdef]; ring

/-- **cfK-controlled resolution is AFFINE in `|w|`** (resolution half of
`schedA_block_linear`, discharged CONDITIONALLY on the B5′ log-cfK bound).  If the
target-width reciprocal `a = 4/(d−c)` is at most `8·cfK(w)²` (which holds when the
target is a fixed fraction of the cylinder, `d−c ≥ 1/(2·cfK w²)` via
`volume_cfCylinder_ge_inv`) AND the word carries the log-cfK bound
`cfK w ≤ exp(κ·|w|)` (the B5′ `goodExtSet goodC` mechanism, `CFSchedule`
`SchedStep`), then the Fibonacci resolution threshold `N` (with `a < fib(n+1)²` for
all `n ≥ N`) is bounded by an AFFINE function of `|w|`:
`N ≤ (κ/log φ)·|w| + (log_φ(√5·√8+1)+1)`.

**ROUTE CORRECTION (2026-08-28, this lap).**  The current directive's *digit-cap*
route (`digits ≤ D`) is FATAL: a FIXED cap `D` makes the limit badly approximable
(no digit `> D`), hence NOT CF-normal; a GROWING cap `D_s→∞` makes `log cfK`
super-linear (`≈ ∑ block_t·log D_t`), breaking the very geometric bound it was
meant to secure.  The correct control is the B5′ `cfK u ≤ exp(goodC·|u|)` bound
(full Gauss measure via `goodExtSet`, compatible with normality — it is the Lévy
constant `(1/n)log q_n → π²/(12ln2)` made uniform, NOT a support restriction).
This lemma isolates exactly the arithmetic that bound buys.  The remaining open
work is grafting `exp(goodC·n)` onto the steer block
(`exists_multiscale_freq_good_block_steer_len`) — intersect the multiscale
selection set with `goodExtSet w goodC ·`, which keeps positive measure. -/
theorem exists_fib_threshold_linear_of_cfK {κ : ℝ} (hκ : 0 ≤ κ)
    (w : List ℕ) (a : ℝ) (ha : a ≤ 8 * (cfK w : ℝ) ^ 2)
    (hK : (cfK w : ℝ) ≤ Real.exp (κ * (w.length : ℝ))) :
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → a < (Nat.fib (n + 1) : ℝ) ^ 2) ∧
      (N : ℝ) ≤ (κ / Real.log Real.goldenRatio) * (w.length : ℝ)
        + (Real.logb Real.goldenRatio (Real.sqrt 5 * Real.sqrt 8 + 1) + 1) := by
  obtain ⟨N, hN1, hN2⟩ := exists_fib_threshold_log a
  refine ⟨N, hN1, ?_⟩
  have hlogφ : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hcfK0 : (0 : ℝ) ≤ (cfK w : ℝ) := by positivity
  have hexp1 : (1 : ℝ) ≤ Real.exp (κ * (w.length : ℝ)) := Real.one_le_exp (by positivity)
  have hexp0 : (0 : ℝ) < Real.exp (κ * (w.length : ℝ)) := Real.exp_pos _
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  -- `√a ≤ √8 · cfK`
  have hsqa : Real.sqrt a ≤ Real.sqrt 8 * (cfK w : ℝ) := by
    have h1 : Real.sqrt a ≤ Real.sqrt (8 * (cfK w : ℝ) ^ 2) := Real.sqrt_le_sqrt ha
    rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq hcfK0] at h1
  -- `√5·√a + 1 ≤ (√5·√8 + 1)·exp(κ|w|)`
  have hkey : Real.sqrt 5 * Real.sqrt a + 1
      ≤ (Real.sqrt 5 * Real.sqrt 8 + 1) * Real.exp (κ * (w.length : ℝ)) := by
    have hb : Real.sqrt 5 * Real.sqrt a
        ≤ Real.sqrt 5 * Real.sqrt 8 * Real.exp (κ * (w.length : ℝ)) := by
      calc Real.sqrt 5 * Real.sqrt a
          ≤ Real.sqrt 5 * (Real.sqrt 8 * (cfK w : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqa h5
        _ = Real.sqrt 5 * Real.sqrt 8 * (cfK w : ℝ) := by ring
        _ ≤ Real.sqrt 5 * Real.sqrt 8 * Real.exp (κ * (w.length : ℝ)) :=
            mul_le_mul_of_nonneg_left hK (by positivity)
    have hexpand : (Real.sqrt 5 * Real.sqrt 8 + 1) * Real.exp (κ * (w.length : ℝ))
        = Real.sqrt 5 * Real.sqrt 8 * Real.exp (κ * (w.length : ℝ))
          + Real.exp (κ * (w.length : ℝ)) := by ring
    rw [hexpand]; linarith [hb, hexp1]
  -- push through `log`
  have hpos1 : (0 : ℝ) < Real.sqrt 5 * Real.sqrt a + 1 := by positivity
  have hpos2 : (0 : ℝ) < (Real.sqrt 5 * Real.sqrt 8 + 1) * Real.exp (κ * (w.length : ℝ)) := by
    positivity
  have hlogle : Real.log (Real.sqrt 5 * Real.sqrt a + 1)
      ≤ Real.log ((Real.sqrt 5 * Real.sqrt 8 + 1) * Real.exp (κ * (w.length : ℝ))) :=
    (Real.log_le_log_iff hpos1 hpos2).mpr hkey
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlogle
  have hlogle' : Real.log (Real.sqrt 5 * Real.sqrt a + 1)
      ≤ κ * (w.length : ℝ) + Real.log (Real.sqrt 5 * Real.sqrt 8 + 1) := by linarith [hlogle]
  have hsub : Real.log (Real.sqrt 5 * Real.sqrt a + 1) / Real.log Real.goldenRatio
      ≤ κ / Real.log Real.goldenRatio * (w.length : ℝ)
        + Real.log (Real.sqrt 5 * Real.sqrt 8 + 1) / Real.log Real.goldenRatio := by
    have heq : κ / Real.log Real.goldenRatio * (w.length : ℝ)
        + Real.log (Real.sqrt 5 * Real.sqrt 8 + 1) / Real.log Real.goldenRatio
        = (κ * (w.length : ℝ) + Real.log (Real.sqrt 5 * Real.sqrt 8 + 1))
          / Real.log Real.goldenRatio := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hlogle' hlogφ.le
  simp only [Real.logb] at hN2 ⊢
  linarith [hN2, hsub]

/-- **Linear block-length bound** (route-decisive core, DISCLOSED `sorry`).  The
sharp form of the geometric bound: the steer-block length is bounded by an AFFINE
function of the accumulated word length, `|chainApp w s| ≤ K₁·|w s| + K₂`.  With
the tight block parameter (`exists_uniform_block_param_tight`) the block length is
`n₁ + m² ≤ 2m²` with `m² ≤ 6(L + Nfib) + 2 + 2⌈2/β⌉⁴` LINEAR in `L = s ≤ |w s|`,
in the resolution length `Nfib ≈ log_φ(1/(d−c))` (target width `d−c ≳ φ^{−c|w s|}`
⇒ `Nfib ≲ |w s|`), and in the word-independent `β`-constant (`γtar/γwx = Θ(q)` by
the Gauss-density ratio bounds, so `⌈2/β⌉` is a per-level constant `≤ |w s|`
eventually).  The three sub-bounds (tight length exposure through the ψ-step,
resolution `Nfib ≲ |w|`, word-independent `β`) are `PENDING_WORK.md` item (ii)/(iii)
— the remaining coupled bookkeeping.  Isolated here as the single genuinely-open
math obligation the B6 crux rests on. -/
theorem schedA_block_linear {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1)
    (w : ℕ → List ℕ) (hw : w = wxSeq hq hr ∨ w = wzSeq hq hr) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ s, ((chainApp w s).length : ℝ) ≤ K₁ * (w s).length + K₂ := by
  sorry

/-- **Geometric block-length bound** (route-decisive).  `∃ ρ ≥ 0, ∀ s, |chainApp w
s| ≤ ρ·|w s|`.  Follows from the affine bound `schedA_block_linear` because
`|w s| ≥ 1` (genuine nonempty chain), so `K₁·|w| + K₂ ≤ (K₁+K₂)·|w|`. -/
theorem schedA_block_geom {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1)
    (w : ℕ → List ℕ) (hw : w = wxSeq hq hr ∨ w = wzSeq hq hr) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ s, ((chainApp w s).length : ℝ) ≤ ρ * (w s).length := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hlin⟩ := schedA_block_linear hq hr w hw
  refine ⟨K₁ + K₂, by positivity, fun s => ?_⟩
  have hne : w s ≠ [] := by
    rcases hw with h | h <;> rw [h]
    · exact wxSeq_ne hq hr s
    · exact wzSeq_ne hq hr s
  have hw1 : (1 : ℝ) ≤ ((w s).length : ℝ) := by
    have := List.length_pos_of_ne_nil hne; exact_mod_cast this
  calc ((chainApp w s).length : ℝ) ≤ K₁ * (w s).length + K₂ := hlin s
    _ ≤ (K₁ + K₂) * (w s).length := by nlinarith [hK₂, hw1]

/-- **Abstract chain frequency obligation from per-stage uniform block goodness.**
Given a strictly-extending chain whose stage-`s` block `chainApp w s` reaches
depth `s` and is uniformly prefix-good for `wordFamily s` at tolerance `schedEps
s` (slack `4√|blk|+2|v|+n₁`, `n₁²≤|blk|·√|blk|`), plus the geometric bound
`schedA_block_geom`, produce the `chain_orbit_equidist_uniform` hypothesis.
`hblock`: schedule `schedEps s→0` beats any `ε` past `s_v`; `hslack`:
`slack_telescoping` with `c=|v|−1`, `C=o(blk)` (`chain_slack_littleO`), `blk→∞`,
`blk≤ρ·word`. -/
theorem chain_hfreq_of_uniform_blocks (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    (hgood : ∀ s, s ≤ (chainApp w s).length ∧ ∃ n₁ : ℕ,
        n₁ ^ 2 ≤ (chainApp w s).length * Nat.sqrt (chainApp w s).length ∧
        (∀ k, k ≤ (chainApp w s).length → ∀ v ∈ wordFamily s,
          |(countOccurrences v ((chainApp w s).take k) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * k|
              < schedEps s * k
                + (4 * Nat.sqrt (chainApp w s).length + 2 * v.length + n₁)))
    (hgeom : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ s, ((chainApp w s).length : ℝ) ≤ ρ * (w s).length) :
    ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
        (∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s → ∀ p, p ≤ (chainApp w s).length →
          |(countOccurrences v ((chainApp w s).take p) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * p| < ε * p + C s) ∧
        (∀ ε : ℝ, 0 < ε → ∀ s₀, ∃ K, ∀ k, K ≤ k →
          (∑ i ∈ Finset.range (k + 1), (C (s₀ + i) + ((v.length : ℝ) - 1)))
            < ε * (w (s₀ + k)).length) := by
  intro v hvne hvpos
  choose n₁ hn₁sq hn₁good using fun s => (hgood s).2
  have hblk1 : ∀ s, 1 ≤ (chainApp w s).length :=
    fun s => List.length_pos_of_ne_nil (chainApp_eq w hext s).2
  set C : ℕ → ℝ := fun s => 4 * Nat.sqrt (chainApp w s).length + 2 * v.length + n₁ s with hCdef
  refine ⟨C, fun s => by rw [hCdef]; positivity, ?_, ?_⟩
  · -- hblock
    intro ε hε
    obtain ⟨t₀, ht₀⟩ := mem_wordFamily_eventually v hvne hvpos
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
    refine ⟨max t₀ Nε, fun s hs p hp => ?_⟩
    have hvfam : v ∈ wordFamily s := ht₀ s (le_trans (le_max_left _ _) hs)
    have hsEps : schedEps s ≤ ε := by
      have hsNε : Nε ≤ s := le_trans (le_max_right _ _) hs
      have hNεs : (Nε : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsNε
      have h1 : (1 : ℝ) / ε < (s : ℝ) + 1 := lt_of_lt_of_le hNε (by linarith)
      rw [schedEps, div_le_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) + 1)]
      rw [div_lt_iff₀ hε] at h1
      nlinarith [h1]
    have hb := hn₁good s p hp v hvfam
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have hmul : schedEps s * p ≤ ε * p := mul_le_mul_of_nonneg_right hsEps hp0
    rw [hCdef]
    calc |(countOccurrences v ((chainApp w s).take p) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * p|
        < schedEps s * p
            + (4 * Nat.sqrt (chainApp w s).length + 2 * v.length + n₁ s) := hb
      _ ≤ ε * p + (4 * Nat.sqrt (chainApp w s).length + 2 * v.length + n₁ s) := by linarith
  · -- hslack via slack_telescoping
    obtain ⟨ρ, hρ0, hgeomρ⟩ := hgeom
    have hvlen1 : 1 ≤ v.length := List.length_pos_of_ne_nil hvne
    have hblktop : Filter.Tendsto (fun s => ((chainApp w s).length : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_atTop_mono (fun s => by exact_mod_cast (hgood s).1) tendsto_natCast_atTop_atTop
    have hClit : (fun s => C s) =o[Filter.atTop]
        fun s => ((chainApp w s).length : ℝ) := by
      have := chain_slack_littleO (blk := fun s => (chainApp w s).length) n₁ (2 * v.length)
        hblk1 (fun s => hn₁sq s) hblktop
      simpa [hCdef, add_assoc, add_left_comm, add_comm] using this
    have hslk := slack_telescoping (fun s => ((w s).length : ℝ))
      (fun s => ((chainApp w s).length : ℝ)) C ((v.length : ℝ) - 1) ρ
      (by simp; exact_mod_cast hvlen1) hρ0 (by positivity)
      (fun s => by rw [hCdef]; positivity)
      (fun s => by positivity)
      (fun s => by
        have h := (chainApp_eq w hext s).1
        rw [h, List.length_append]; push_cast; ring)
      hgeomρ hClit hblktop
    exact hslk

/-- x-stream frequency obligation (instantiates `chain_hfreq_of_uniform_blocks`). -/
theorem schedA_hfreq_x {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
        (∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s → ∀ p, p ≤ (chainApp (wxSeq hq hr) s).length →
          |(countOccurrences v ((chainApp (wxSeq hq hr) s).take p) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * p| < ε * p + C s) ∧
        (∀ ε : ℝ, 0 < ε → ∀ s₀, ∃ K, ∀ k, K ≤ k →
          (∑ i ∈ Finset.range (k + 1), (C (s₀ + i) + ((v.length : ℝ) - 1)))
            < ε * (wxSeq hq hr (s₀ + k)).length) :=
  chain_hfreq_of_uniform_blocks (wxSeq hq hr) (wxSeq_ext hq hr)
    (fun s => (schedA_step hq hr s).2.2.2) (schedA_block_geom hq hr _ (Or.inl rfl))

/-- z-stream frequency obligation (instantiates `chain_hfreq_of_uniform_blocks`). -/
theorem schedA_hfreq_z {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : -q < r ∧ r < 1) :
    ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
        (∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s → ∀ p, p ≤ (chainApp (wzSeq hq hr) s).length →
          |(countOccurrences v ((chainApp (wzSeq hq hr) s).take p) : ℝ)
            - (gaussMeasure (cfCylinder v)).toReal * p| < ε * p + C s) ∧
        (∀ ε : ℝ, 0 < ε → ∀ s₀, ∃ K, ∀ k, K ≤ k →
          (∑ i ∈ Finset.range (k + 1), (C (s₀ + i) + ((v.length : ℝ) - 1)))
            < ε * (wzSeq hq hr (s₀ + k)).length) :=
  chain_hfreq_of_uniform_blocks (wzSeq hq hr) (wzSeq_ext hq hr)
    (fun s => (schedA_step hq hr s).1.2.2) (schedA_block_geom hq hr _ (Or.inr rfl))

/-- **THE B6 CRUX (interleaved-schedule witness), FEASIBLE REGIME.**  For `q > 0`
and `r ∈ (-q, 1)` — exactly the range in which the feasible set
`(0,1) ∩ ψ⁻¹(0,1)` is nonempty — there is a single real `x` such that both `x`
and `ψ(x) = q·x + r` are irrational in `(0,1)` with equidistributing Gauss
orbits.  Disclosed `sorry`: this is the interleaved schedule (module docstring +
`PENDING_WORK.md`); the metric substrate it consumes (L1–L3, the pullback
measure, the orbit-frequency interface) is all proved and axiom-clean.

**Feasibility hypothesis `hr` is MANDATORY** (added 2026-08-24): without it the
conclusion is outright FALSE — e.g. `(q,r) = (1,5)` makes `x ∈ (0,1) ∧ x+5 ∈
(0,1)` contradictory.  `-q < r < 1 ⟺ (0,1) ∩ ψ⁻¹(0,1) ≠ ∅`, which is precisely
what seeding the two-stream recursion needs.  The unconditional deliverable
`exists_cfNormal_and_affine_cfNormal` reduces the general `r` to this regime via
integer-shift invariance of CF-normality (asymptotic; the Gauss orbit ignores
the integer part). -/
theorem exists_interleaved_affine_witness {q : ℝ} (hq : 0 < q) (r : ℝ)
    (hr : -q < r ∧ r < 1) :
    ∃ x : ℝ,
      (Irrational x ∧ x ∈ Set.Ioo (0 : ℝ) 1 ∧ CFOrbitEquidist x) ∧
      (Irrational (affineMap q r x) ∧ affineMap q r x ∈ Set.Ioo (0 : ℝ) 1
        ∧ CFOrbitEquidist (affineMap q r x)) := by
  have hxne := wxSeq_ne hq hr
  have hxpos := wxSeq_pos hq hr
  have hxext := wxSeq_ext hq hr
  have hzne := wzSeq_ne hq hr
  have hzpos := wzSeq_pos hq hr
  have hzext := wzSeq_ext hq hr
  -- the two chain limit points
  obtain ⟨xA, hxAirr, hxAmem⟩ :=
    exists_irrational_mem_iInter_cfCylinder (wxSeq hq hr) hxne hxpos hxext
  have hxA01 : xA ∈ Set.Ioo (0 : ℝ) 1 :=
    (irrational_mem_Ioo_of_mem_iInter_cfCylinder (wxSeq hq hr) hxne hxpos hxext hxAmem).2
  obtain ⟨zA, hzAirr, hzAmem⟩ :=
    exists_irrational_mem_iInter_cfCylinder (wzSeq hq hr) hzne hzpos hzext
  have hzA01 : zA ∈ Set.Ioo (0 : ℝ) 1 :=
    (irrational_mem_Ioo_of_mem_iInter_cfCylinder (wzSeq hq hr) hzne hzpos hzext hzAmem).2
  -- ψ(xA) and zA both live in every shrinking wz-interval, so they coincide
  have hpsiIcc : ∀ s, affineMap q r xA ∈ Set.Icc (schedA hq hr s).e (schedA hq hr s).f := by
    intro s
    have hmem := (schedA hq hr s).hinv (hxAmem s)
    rw [Set.mem_preimage] at hmem
    exact Set.Ioo_subset_Icc_self hmem
  have hzAIcc : ∀ s, zA ∈ Set.Icc (schedA hq hr s).e (schedA hq hr s).f :=
    fun s => (schedA hq hr s).hzhull (hzAmem s)
  have hdiam : Filter.Tendsto (fun s => (schedA hq hr s).f - (schedA hq hr s).e)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun s => by linarith [(schedA hq hr s).hef]) (fun s => ?_)
      (cfCylinder_chain_volume_tendsto hzne hzpos hzext)
    exact Ioo_sub_le_volume_cfCylinder (wzSeq hq hr s) (hzne s) (hzpos s)
      (schedA hq hr s).hef (schedA hq hr s).hzint
  have hpsi_eq : affineMap q r xA = zA := eq_of_mem_iInter_Icc hdiam hpsiIcc hzAIcc
  -- orbit equidistribution for both streams
  have hox : CFOrbitEquidist xA :=
    chain_orbit_equidist_uniform (wxSeq hq hr) hxext hxAirr hxA01 hxAmem (schedA_hfreq_x hq hr)
  have hoz : CFOrbitEquidist zA :=
    chain_orbit_equidist_uniform (wzSeq hq hr) hzext hzAirr hzA01 hzAmem (schedA_hfreq_z hq hr)
  refine ⟨xA, ⟨hxAirr, hxA01, hox⟩, ?_⟩
  rw [hpsi_eq]
  exact ⟨hzAirr, hzA01, hoz⟩

/-- **Signpost (necessity of the feasibility hypothesis `-q < r < 1`).**  The
interleaving target `x ∈ (0,1) ∧ ψ(x) ∈ (0,1)` that
`exists_interleaved_affine_witness` delivers under `-q < r < 1` is genuinely
EMPTY for some `r ∉ (-q,1)`: with `q = 1, r = 1` no `x ∈ (0,1)` maps into `(0,1)`
under `ψ(x) = x + 1` (it lands in `(1,2)`).  So the hypothesis cannot be dropped —
the general-`r` headline (`exists_cfNormal_and_affine_cfNormal`) instead routes
through the integer-shift reduction (`isCFNormal_add_nat`), never through this
witness in the infeasible regime. -/
theorem interleaved_affine_target_not_always_nonempty :
    ¬ ∀ (q : ℝ), 0 < q → ∀ r : ℝ,
      ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ affineMap q r x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro h
  obtain ⟨x, ⟨hx0, _⟩, _, hy1⟩ := h 1 one_pos 1
  simp only [affineMap_apply, one_mul] at hy1
  linarith

/-- **Window-frequency limit is invariant under a fixed digit shift.**  If the
digit sequence `d'` is `d` shifted right by `m` (`d' (k + m) = d k`; the first `m`
entries are arbitrary), then the length-`p` window frequency of any pattern `v`
has the same limit for `d'` as for `d`.  The reusable core of the integer-shift
invariance of CF-normality (`IsCFNormal_add_int`): `digits(y+n) = [0,n] ++
digits(y)` is the `m = 2` case, so prepending finitely many CF digits — as an
integer shift does — cannot change any pattern's asymptotic frequency. -/
theorem cfFreq_tendsto_of_digit_shift (d d' : ℕ → ℕ) (m : ℕ)
    (hshift : ∀ k, d' (k + m) = d k) (v : List ℕ) (hv : v ≠ []) {γ : ℝ}
    (h : Filter.Tendsto (fun p => (countOccurrences v ((List.range p).map d) : ℝ) / p)
      Filter.atTop (nhds γ)) :
    Filter.Tendsto (fun p => (countOccurrences v ((List.range p).map d') : ℝ) / p)
      Filter.atTop (nhds γ) := by
  have hvlen : 1 ≤ v.length := List.length_pos_of_ne_nil hv
  -- split: for `p ≥ m`, `(range p).map d' = pre ++ (range (p-m)).map d`
  have hsplit : ∀ p, m ≤ p → (List.range p).map d'
      = (List.range m).map d' ++ (List.range (p - m)).map d := by
    intro p hp
    conv_lhs => rw [show p = m + (p - m) by omega, range_add_eq, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [add_comm m i]; exact hshift i
  -- `count_d p-m ≤ count_{d'} p ≤ count_d (p-m) + (m + v.length)`
  have hlo : ∀ p, m ≤ p →
      (countOccurrences v ((List.range (p - m)).map d) : ℝ)
        ≤ (countOccurrences v ((List.range p).map d') : ℝ) := by
    intro p hp
    rw [hsplit p hp]
    exact_mod_cast countOccurrences_le_append_left v ((List.range m).map d')
      ((List.range (p - m)).map d)
  have hhi : ∀ p, m ≤ p →
      (countOccurrences v ((List.range p).map d') : ℝ)
        ≤ (countOccurrences v ((List.range (p - m)).map d) : ℝ) + (m + v.length) := by
    intro p hp
    rw [hsplit p hp]
    have hup := countOccurrences_append_le hv ((List.range m).map d')
      ((List.range (p - m)).map d)
    have hpre : countOccurrences v ((List.range m).map d') ≤ m := by
      have := countOccurrences_le_length hv ((List.range m).map d')
      simpa using this
    have hnat : countOccurrences v ((List.range m).map d' ++ (List.range (p - m)).map d)
        ≤ m + countOccurrences v ((List.range (p - m)).map d) + v.length := by omega
    calc (countOccurrences v ((List.range m).map d' ++ (List.range (p - m)).map d) : ℝ)
        ≤ ((m + countOccurrences v ((List.range (p - m)).map d) + v.length : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = (countOccurrences v ((List.range (p - m)).map d) : ℝ) + (m + v.length) := by
          push_cast; ring
  have hshiftTop : Filter.Tendsto (fun p : ℕ => p - m) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.2
    intro N
    exact ⟨N + m, fun p hp => by omega⟩
  -- `count_d (p-m) / p → γ`
  have hcp : Filter.Tendsto
      (fun p => (countOccurrences v ((List.range (p - m)).map d) : ℝ) / (p : ℝ))
      Filter.atTop (nhds γ) := by
    have hcomp : Filter.Tendsto
        (fun p => (countOccurrences v ((List.range (p - m)).map d) : ℝ) / ((p - m : ℕ) : ℝ))
        Filter.atTop (nhds γ) := h.comp hshiftTop
    have hmdiv : Filter.Tendsto (fun p : ℕ => (m : ℝ) / (p : ℝ)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
    have hratio : Filter.Tendsto (fun p : ℕ => ((p - m : ℕ) : ℝ) / (p : ℝ))
        Filter.atTop (nhds 1) := by
      have hbase : Filter.Tendsto (fun p : ℕ => 1 - (m : ℝ) / (p : ℝ)) Filter.atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub hmdiv
      refine hbase.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (max m 1)] with p hp
      have hpm : m ≤ p := le_trans (le_max_left _ _) hp
      have hp1 : 1 ≤ p := le_trans (le_max_right _ _) hp
      have hp0 : (p : ℝ) ≠ 0 := by
        have : (0 : ℝ) < p := by exact_mod_cast hp1
        exact this.ne'
      rw [Nat.cast_sub hpm]; field_simp
    have hprod := hcomp.mul hratio
    rw [mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop m] with p hp
    have hpmR : ((p - m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  -- squeeze `count_{d'} p / p` between `count_d (p-m)/p` and `count_d (p-m)/p + (m+v.length)/p`
  have herr : Filter.Tendsto
      (fun p : ℕ => (countOccurrences v ((List.range (p - m)).map d) : ℝ) / (p : ℝ)
        + ((m : ℝ) + v.length) / (p : ℝ)) Filter.atTop (nhds γ) := by
    have hz : Filter.Tendsto (fun p : ℕ => ((m : ℝ) + v.length) / (p : ℝ))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
    have h2 := hcp.add hz
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hcp herr ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max m 1)] with p hp
    have hpm : m ≤ p := le_trans (le_max_left _ _) hp
    have hp1 : 1 ≤ p := le_trans (le_max_right _ _) hp
    have hpR : (0 : ℝ) ≤ p := by positivity
    exact div_le_div_of_nonneg_right (hlo p hpm) hpR
  · filter_upwards [Filter.eventually_ge_atTop (max m 1)] with p hp
    have hpm : m ≤ p := le_trans (le_max_left _ _) hp
    have hp1 : 1 ≤ p := le_trans (le_max_right _ _) hp
    have hpR : (0 : ℝ) ≤ p := by positivity
    have hthis := div_le_div_of_nonneg_right (hhi p hpm) hpR
    rwa [add_div] at hthis

/-- Gauss orbit of `y + n` returns to `y` after exactly two steps
(`n ≥ 1` a natural, `y ∈ (0,1)`): `g(y+n) = 1/(n+y)`, `g²(y+n) = y`. -/
lemma gaussMap_iter_two_add_nat {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) : gaussMap^[2] (y + (n : ℝ)) = y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgt1 : (1 : ℝ) < y + (n : ℝ) := by linarith
  have hpos : (0 : ℝ) < y + (n : ℝ) := by linarith
  -- step 1: gaussMap (y+n) = (y+n)⁻¹  (its inverse lies in (0,1))
  have hstep1 : gaussMap (y + (n : ℝ)) = (y + (n : ℝ))⁻¹ := by
    unfold gaussMap
    rw [if_neg (ne_of_gt hpos)]
    apply Int.fract_eq_self.mpr
    constructor
    · positivity
    · exact inv_lt_one_of_one_lt₀ hgt1
  have h2 : gaussMap^[2] (y + (n : ℝ)) = gaussMap (gaussMap (y + (n : ℝ))) := rfl
  rw [h2, hstep1]
  -- step 2: gaussMap ((y+n)⁻¹) = Int.fract (y+n) = y
  unfold gaussMap
  rw [if_neg (by positivity), inv_inv, Int.fract_add_natCast,
    Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1⟩]

/-- Digit shift under integer translation: `cfDigit (y+n) (k+2) = cfDigit y k`
for `y ∈ (0,1)`, `n ≥ 1`.  Concretely `digits(y+n) = [0, n] ++ digits(y)`. -/
lemma cfDigit_add_nat_shift {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : cfDigit (y + (n : ℝ)) (k + 2) = cfDigit y k := by
  unfold cfDigit
  rw [Function.iterate_add_apply, gaussMap_iter_two_add_nat hy hn]

/-- **Integer-shift invariance of CF-normality (natural, `n ≥ 1`).**  If
`y ∈ (0,1)` is CF-normal then so is `y + n`: the first two CF digits change
(`[0, n]`) but every pattern's asymptotic window frequency is preserved. -/
lemma isCFNormal_add_nat {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) (hyn : IsCFNormal y) : IsCFNormal (y + (n : ℝ)) := by
  intro v hv hpos
  exact cfFreq_tendsto_of_digit_shift (cfDigit y) (cfDigit (y + (n : ℝ))) 2
    (fun k => cfDigit_add_nat_shift hy hn k) v hv (hyn v hv hpos)

/-- **B6 target (single affine map).**  There is a real `x` with both `x` and
its affine image `q·x + r` CF-normal — a constructive data point on Vandehey
(Compositio 2017) §7 problem 1 for `q > 0`.  Reduced to the interleaved-schedule
witness via the orbit-frequency interface. -/
theorem exists_cfNormal_and_affine_cfNormal {q : ℝ} (hq : 0 < q) (r : ℝ) :
    ∃ x : ℝ, IsCFNormal x ∧ IsCFNormal (affineMap q r x) := by
  by_cases hr : -q < r ∧ r < 1
  · -- feasible regime: `(0,1) ∩ ψ⁻¹(0,1) ≠ ∅`, the interleaved witness applies directly
    obtain ⟨x, ⟨hx1, hx2, hx3⟩, ⟨hy1, hy2, hy3⟩⟩ := exists_interleaved_affine_witness hq r hr
    exact ⟨x, isCFNormal_of_irrational_orbit_freq x hx1 hx2 hx3,
      isCFNormal_of_irrational_orbit_freq (affineMap q r x) hy1 hy2 hy3⟩
  · -- infeasible regime: `¬(-q < r ∧ r < 1)`.  Split on the sign of the shift.
    by_cases hr1 : 1 ≤ r
    · -- `r ≥ 1`: shift the image UP by `n = ⌊r⌋ ≥ 1`.  Take the feasible witness
      -- at `r₀ = r - n = Int.fract r ∈ [0,1) ⊂ (-q,1)`; then
      -- `ψ(x) = q·x + r = (q·x + r₀) + n = y + n`, and `IsCFNormal (y+n)` follows
      -- from `IsCFNormal y` by the integer-shift lemma.
      set m : ℤ := ⌊r⌋ with hm_def
      have hm1 : 1 ≤ m := Int.le_floor.mpr (by exact_mod_cast hr1)
      set n : ℕ := m.toNat with hn_def
      have hnm : (n : ℤ) = m := Int.toNat_of_nonneg (by omega)
      have hn1 : 1 ≤ n := by omega
      have hcast : (n : ℝ) = (m : ℝ) := by exact_mod_cast hnm
      have hmle : (m : ℝ) ≤ r := by rw [hm_def]; exact Int.floor_le r
      have hltm : r < (m : ℝ) + 1 := by rw [hm_def]; exact Int.lt_floor_add_one r
      set r₀ : ℝ := r - (n : ℝ) with hr0_def
      have hr0 : -q < r₀ ∧ r₀ < 1 := by
        rw [hr0_def, hcast]; constructor <;> [linarith; linarith]
      obtain ⟨x, ⟨hx1, hx2, hx3⟩, ⟨hy1, hy2, hy3⟩⟩ :=
        exists_interleaved_affine_witness hq r₀ hr0
      -- `affineMap q r x = affineMap q r₀ x + n`
      have hy0 : IsCFNormal (affineMap q r₀ x) :=
        isCFNormal_of_irrational_orbit_freq (affineMap q r₀ x) hy1 hy2 hy3
      have heq : affineMap q r x = affineMap q r₀ x + (n : ℝ) := by
        simp only [affineMap_apply, hr0_def]; ring
      refine ⟨x, isCFNormal_of_irrational_orbit_freq x hx1 hx2 hx3, ?_⟩
      rw [heq]
      exact isCFNormal_add_nat hy2 hn1 hy0
    · -- `r ≤ -q`: shift the DOMAIN up instead.  Choose natural `M ≥ 1` with
      -- `r₁ = q·M + r ∈ (-q,1)`; the admissible `M`-interval
      -- `((-q-r)/q, (1-r)/q)` has length `1 + 1/q > 1`, so it contains an integer,
      -- and `(-q-r)/q ≥ 0` (as `r ≤ -q`) forces `M ≥ 1`.  Feasible witness at `r₁`
      -- gives `x` with `x` and `y = q·x + r₁ ∈ (0,1)` CF-normal; then `x' = x + M`
      -- is CF-normal (up-shift) and `ψ(x') = q·x' + r = q·x + r₁ = y`.
      have hrle : r ≤ -q := by
        rcases (not_and_or.mp hr) with h | h
        · linarith [not_lt.mp h]
        · exact absurd (not_lt.mp h) (by linarith [not_le.mp hr1])
      set L : ℝ := (-q - r) / q with hL_def
      set U : ℝ := (1 - r) / q with hU_def
      have hLnonneg : 0 ≤ L := by rw [hL_def]; apply div_nonneg (by linarith) (le_of_lt hq)
      set M : ℤ := ⌊L⌋ + 1 with hM_def
      have hMgtL : L < (M : ℝ) := by rw [hM_def]; push_cast; exact Int.lt_floor_add_one L
      have hMltU : (M : ℝ) < U := by
        have h1 : (M : ℝ) ≤ L + 1 := by rw [hM_def]; push_cast; linarith [Int.floor_le L]
        have hUL : U - L = 1 + 1 / q := by
          rw [hU_def, hL_def]; field_simp; ring
        have hq' : 0 < 1 / q := one_div_pos.mpr hq
        linarith
      have hMge1 : 1 ≤ M := by
        have : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt hLnonneg hMgtL
        have : (0 : ℤ) < M := by exact_mod_cast this
        omega
      set nn : ℕ := M.toNat with hnn_def
      have hnnM : (nn : ℤ) = M := Int.toNat_of_nonneg (by omega)
      have hnn1 : 1 ≤ nn := by omega
      have hnncast : (nn : ℝ) = (M : ℝ) := by exact_mod_cast hnnM
      set r₁ : ℝ := q * (M : ℝ) + r with hr1_def
      have hmc : (M : ℝ) * q = q * (M : ℝ) := mul_comm _ _
      have hr1feas : -q < r₁ ∧ r₁ < 1 := by
        constructor
        · have hlow : -q - r < (M : ℝ) * q := by
            rw [hL_def] at hMgtL; exact (div_lt_iff₀ hq).mp hMgtL
          rw [hr1_def]; linarith [hlow, hmc]
        · have hhi : (M : ℝ) * q < 1 - r := by
            rw [hU_def] at hMltU; exact (lt_div_iff₀ hq).mp hMltU
          rw [hr1_def]; linarith [hhi, hmc]
      obtain ⟨x, ⟨hx1, hx2, hx3⟩, ⟨hy1, hy2, hy3⟩⟩ :=
        exists_interleaved_affine_witness hq r₁ hr1feas
      have hxN : IsCFNormal x := isCFNormal_of_irrational_orbit_freq x hx1 hx2 hx3
      have hyN : IsCFNormal (affineMap q r₁ x) :=
        isCFNormal_of_irrational_orbit_freq (affineMap q r₁ x) hy1 hy2 hy3
      refine ⟨x + (nn : ℝ), isCFNormal_add_nat hx2 hnn1 hxN, ?_⟩
      have heq : affineMap q r (x + (nn : ℝ)) = affineMap q r₁ x := by
        simp only [affineMap_apply, hr1_def, hnncast]; ring
      rw [heq]; exact hyN

end NormalNumbers
