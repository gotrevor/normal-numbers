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
