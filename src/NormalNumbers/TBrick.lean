/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TBrickDefs
import NormalNumbers.CFWordBridge
import NormalNumbers.CFDigitLaw

/-!
# W5 — the t-brick structure and the d-ary side of the Lemma-13 balance

This file starts the assembly of Becher–Yuhjtman's main refinement lemma
(Lemma 13).  All of its *inputs* are proved elsewhere in the repo:

* the Lemma-5 substitute `half_mass_long_extensions` (≥ ½ the mass of a
  genuine cylinder is in good-length CF extensions);
* the KPW-Lemma-6 substitute `chebyshev_blockCount_brick` (the CF
  discrepancy bad zone inside a brick has γ-measure `O(1/n)·γ(I_w)`);
* the d-ary bad-zone machinery in `TBrickDefs` (Lemma 8 + Prop 12).

The route-decisive step for the whole W5/W6 expedition is the **measure
balance**: inside `I_w`, the good-length mass strictly exceeds the sum of the
CF bad zone and the per-base d-ary bad zones for large refinement order `n`.
This file discharges the **d-ary half** of that balance:

* `TBrick` (Defs 10–11) — a t-brick: a genuine CF word `w` nested (with
  relative length `≥ 1/(2d)`, the repo's Prop-12 route replacing B–Y's
  `1/(16 e^{4c} d)`) inside one-or-two adjacent order-`m_d` cells per base
  `2 ≤ d ≤ t`.
* `volume_aggregate_daryBadZoneWide_le` — the aggregate wide d-ary bad zone
  over all bases and all block lengths `k ≥ kmin` has measure at most a
  finite sum of geometric-in-`kmin` terms.
* `TBrick.volume_aggregate_bad_le` — specialised to a brick: that aggregate
  bad zone has measure `≤ C(t,ε,kmin)·|I_w|` with `C(t,ε,kmin) → 0` as
  `kmin → ∞`.  This is the d-ary side of the balance, fully in hand.

The downstream CF discrepancy aggregation and its combination with
`half_mass_long_extensions` are also complete; this file's declarations are
the d-ary half consumed by that finished refinement chain.
-/

namespace NormalNumbers

open MeasureTheory

/-- A **t-brick** (Becher–Yuhjtman Defs 10–11), the repo's Prop-12 variant.
A genuine CF word `w` together with, for each integer base `2 ≤ d ≤ t`, an
order-`m d` d-ary cell block of `r d ∈ {1,2}` consecutive cells that
*contains* `cfCylinder w`, with the brick ratio `d^{-m d} ≤ 2d·|I_w|` (the
repo's `1/(2d)` relative-length bound from Prop 12, in place of B–Y's
`1/(16 e^{4c} d)`). -/
structure TBrick (t : ℕ) where
  /-- The continued-fraction word. -/
  w : List ℕ
  /-- `w` is nonempty (a genuine cylinder). -/
  hw_ne : w ≠ []
  /-- Every CF digit of `w` is `≥ 1` (digit `0` is the junk marker). -/
  hw_pos : ∀ a ∈ w, 1 ≤ a
  /-- Per base `d`, the order of the containing d-ary cell block. -/
  m : ℕ → ℕ
  /-- Per base `d`, the left index of the containing d-ary cell block. -/
  j : ℕ → ℤ
  /-- Per base `d`, the number of consecutive cells (`1` or `2`). -/
  r : ℕ → ℕ
  /-- `r d ≥ 1`. -/
  hr1 : ∀ d, 2 ≤ d → d ≤ t → 1 ≤ r d
  /-- `r d ≤ 2` (Prop 12). -/
  hr2 : ∀ d, 2 ≤ d → d ≤ t → r d ≤ 2
  /-- Containment: `cfCylinder w ⊆` the d-ary cell block. -/
  hsub : ∀ d, 2 ≤ d → d ≤ t → cfCylinder w ⊆ daryCell d (m d) (j d) (r d)
  /-- Brick ratio (Prop-12 route): `d^{-m d} ≤ 2d·|I_w|`. -/
  hratio : ∀ d, 2 ≤ d → d ≤ t →
    ENNReal.ofReal ((d : ℝ) ^ (m d))⁻¹
      ≤ ENNReal.ofReal (2 * d) * volume (cfCylinder w)

/-- The geometric ratio governing the wide d-ary bad zone at base `d`. -/
noncomputable def daryBadRatio (d : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-((d : ℝ) * ε ^ 2) / 6)

lemma daryBadRatio_pos (d : ℕ) (ε : ℝ) : 0 < daryBadRatio d ε :=
  Real.exp_pos _

lemma daryBadRatio_lt_one {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 < ε) :
    daryBadRatio d ε < 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [daryBadRatio, Real.exp_lt_one_iff]
  have : 0 < (d : ℝ) * ε ^ 2 := by positivity
  linarith

/-- **Aggregate wide d-ary bad zone bound.** Over all bases `2 ≤ d ≤ t`, both
possible base cells `j0 d` and `j0 d + 1` (a brick's `σ_d` may be two
consecutive cells and the surviving point may lie in either), and all block
lengths `k ≥ kmin`, the union of wide d-ary bad zones has measure at most a
finite sum of geometric-in-`kmin` terms — one per base. -/
theorem volume_aggregate_daryBadZoneWide_le
    (t kmin : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1)
    (m0 : ℕ → ℕ) (j0 : ℕ → ℤ) :
    volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
        ⋃ (_ : kmin ≤ k), daryBadZoneWide d (m0 d) (j0 d + i) ε k)
      ≤ ∑ d ∈ Finset.Icc 2 t, ENNReal.ofReal
          (12 * d / d ^ (m0 d) * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) := by
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum ?_)
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
  have hdε : (d : ℝ) * ε ≤ 1 := by
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast hd.2
    calc (d : ℝ) * ε ≤ (t : ℝ) * ε := by gcongr
      _ ≤ 1 := hεt
  have hone : ∀ i : ℕ,
      volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k),
          daryBadZoneWide d (m0 d) (j0 d + i) ε k)
        ≤ ENNReal.ofReal (6 * d / d ^ (m0 d) * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) := fun i =>
    volume_iUnion_daryBadZoneWide_le d (m0 d) hd1 (j0 d + i) hε0 hdε kmin
  calc volume (⋃ i ∈ Finset.range 2, ⋃ k : ℕ, ⋃ (_ : kmin ≤ k),
        daryBadZoneWide d (m0 d) (j0 d + i) ε k)
      ≤ ∑ i ∈ Finset.range 2, volume (⋃ k : ℕ, ⋃ (_ : kmin ≤ k),
          daryBadZoneWide d (m0 d) (j0 d + i) ε k) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range 2, ENNReal.ofReal
          (6 * d / d ^ (m0 d) * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) :=
        Finset.sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal (12 * d / d ^ (m0 d) * daryBadRatio d ε ^ kmin
          / (1 - daryBadRatio d ε)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show ((2 : ℕ) : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **The d-ary side of the Lemma-13 balance.** For a t-brick `B`, the
aggregate wide d-ary bad zone (all bases `2 ≤ d ≤ t`, all block lengths
`k ≥ kmin`, in the brick's own cells) has measure at most
`C(t,ε,kmin)·|I_w|`, where the constant is a finite sum of geometric-in-`kmin`
terms.  Since each term `→ 0` as `kmin → ∞`, so does the constant: the d-ary
bad mass is eventually an arbitrarily small fraction of `|I_w|`. -/
theorem TBrick.volume_aggregate_bad_le {t : ℕ} (B : TBrick t)
    {ε : ℝ} (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1) (kmin : ℕ) :
    volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
        ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
      ≤ (∑ d ∈ Finset.Icc 2 t, ENNReal.ofReal
          (24 * d ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε)))
        * volume (cfCylinder B.w) := by
  refine (volume_aggregate_daryBadZoneWide_le t kmin hε0 hεt B.m B.j).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hρpos : 0 < daryBadRatio d ε := daryBadRatio_pos d ε
  have hρ1 : daryBadRatio d ε < 1 := daryBadRatio_lt_one hd1 hε0
  have hden : 0 < 1 - daryBadRatio d ε := by linarith
  -- split the per-base bound as `(12 d² ρ^kmin/(1−ρ)) · d^{-m_d}`, then use
  -- the brick ratio `d^{-m_d} ≤ 2d·|I_w|`.
  have hsplit : (12 * (d : ℝ) / d ^ (B.m d) * daryBadRatio d ε ^ kmin
        / (1 - daryBadRatio d ε))
      = (12 * d * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
        * ((d : ℝ) ^ (B.m d))⁻¹ := by
    ring
  have hcoef_nonneg : 0 ≤ 12 * (d : ℝ) * daryBadRatio d ε ^ kmin
      / (1 - daryBadRatio d ε) := by positivity
  calc ENNReal.ofReal (12 * d / d ^ (B.m d) * daryBadRatio d ε ^ kmin
          / (1 - daryBadRatio d ε))
      = ENNReal.ofReal (12 * d * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε))
          * ENNReal.ofReal ((d : ℝ) ^ (B.m d))⁻¹ := by
        rw [hsplit, ENNReal.ofReal_mul hcoef_nonneg]
    _ ≤ ENNReal.ofReal (12 * d * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε))
          * (ENNReal.ofReal (2 * d) * volume (cfCylinder B.w)) := by
        gcongr
        exact B.hratio d hd.1 hd.2
    _ = ENNReal.ofReal (24 * d ^ 2 * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) * volume (cfCylinder B.w) := by
        have hreal : (12 * (d : ℝ) * daryBadRatio d ε ^ kmin
              / (1 - daryBadRatio d ε)) * (2 * d)
            = 24 * d ^ 2 * daryBadRatio d ε ^ kmin
              / (1 - daryBadRatio d ε) := by
          ring
        rw [← mul_assoc, ← ENNReal.ofReal_mul hcoef_nonneg, hreal]

/-- The **CF discrepancy bad zone** of a word `v` inside the brick `I_w`:
points of `I_w` whose orbit block-count of `v` over the next `n` steps
deviates from `γ(I_v)` by at least `δ`.  This is exactly the set controlled
by `chebyshev_blockCount_brick`. -/
def cfBadZone (w v : List ℕ) (n : ℕ) (δ : ℝ) : Set ℝ :=
  cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹'
    {x ∈ Set.Ioo (0 : ℝ) 1 | δ ≤ |blockCount (cfCylinder v) n x / n -
      (gaussMeasure (cfCylinder v)).toReal|}

/-- **The CF side of the Lemma-13 balance.** For a *finite* family `F` of
genuine CF words (at each construction stage only finitely many blocks — those
of length ≤ t with digits ≤ t — need good frequency), the union of the CF
discrepancy bad zones has γ-measure at most a finite sum of the per-word
`chebyshev_blockCount_brick` bounds — i.e. `O(1/n)·γ(I_w)`. -/
theorem gaussMeasure_aggregate_cfBadZone_le
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal
      ≤ ∑ v ∈ F, 7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
          / (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal := by
  calc (gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ)).toReal
      ≤ (∑ v ∈ F, gaussMeasure (cfBadZone w v n δ)).toReal := by
        refine ENNReal.toReal_mono ?_ (measure_biUnion_finset_le F _)
        exact (ENNReal.sum_lt_top.2 (fun v _ => measure_lt_top _ _)).ne
    _ = ∑ v ∈ F, (gaussMeasure (cfBadZone w v n δ)).toReal :=
        ENNReal.toReal_sum (fun v _ => measure_ne_top _ _)
    _ ≤ ∑ v ∈ F, 7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
          / (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal := by
        refine Finset.sum_le_sum fun v hv => ?_
        exact chebyshev_blockCount_brick w v hposw (hF v hv) n hn hδ

/-- **The combine core** (logical heart of the Lemma-13 balance). If the good
set `G` has measure at least `M`, the bad set `B` has measure at most `a`, and
`a < M`, then some point of `G` avoids `B`.  Instantiated in Lemma 13 with
`G` = good-length extensions (`≥ ½|I_w|`), `B` = CF bad zone ∪ d-ary bad zones
(`< ½|I_w|` for large `n`, `kmin`). -/
theorem exists_mem_notMem_of_measure_lt {μ : Measure ℝ} {G B : Set ℝ}
    {M a : ENNReal} (hG : M ≤ μ G) (hB : μ B ≤ a) (hlt : a < M) :
    ∃ x ∈ G, x ∉ B := by
  have hsub : μ G ≤ μ (G \ B) + μ B := by
    have hcov : G ⊆ (G \ B) ∪ B := by
      intro x hx
      by_cases h : x ∈ B
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    exact (measure_mono hcov).trans (measure_union_le _ _)
  have hne : μ (G \ B) ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hsub
    exact absurd (hG.trans (hsub.trans hB)) (not_le.2 hlt)
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨x, hx.1, hx.2⟩

/-- **Combine two bad zones against a good set.** If a good set `G` carries at
least half of `vol0`, and two bad sets `B₁,B₂` have measure `≤ p·vol0` and
`≤ q·vol0` with `p+q < ½`, then some point of `G` avoids both.  This packages
the ENNReal arithmetic of the Lemma-13 balance. -/
theorem exists_mem_notMem_union_of_bounds
    {G B₁ B₂ : Set ℝ} {vol0 : ENNReal} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q < 1 / 2)
    (hvol0 : vol0 ≠ 0) (hvoltop : vol0 ≠ ⊤)
    (hG : vol0 ≤ 2 * volume G)
    (hB₁ : volume B₁ ≤ ENNReal.ofReal p * vol0)
    (hB₂ : volume B₂ ≤ ENNReal.ofReal q * vol0) :
    ∃ x ∈ G, x ∉ B₁ ∪ B₂ := by
  have hB : volume (B₁ ∪ B₂) ≤ ENNReal.ofReal (p + q) * vol0 := by
    calc volume (B₁ ∪ B₂) ≤ volume B₁ + volume B₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal p * vol0 + ENNReal.ofReal q * vol0 := add_le_add hB₁ hB₂
      _ = ENNReal.ofReal (p + q) * vol0 := by rw [ENNReal.ofReal_add hp hq, add_mul]
  have hpq2 : ENNReal.ofReal (p + q) < 2⁻¹ := by
    have hhalf_eq : ENNReal.ofReal (1 / 2 : ℝ) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    rw [← hhalf_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hpq
  have hlt : ENNReal.ofReal (p + q) * vol0 < volume G := by
    have h1 : ENNReal.ofReal (p + q) * vol0 < vol0 / 2 := by
      rw [ENNReal.div_eq_inv_mul]
      exact ENNReal.mul_lt_mul_left hvol0 hvoltop hpq2
    have h2 : vol0 / 2 ≤ volume G :=
      ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact hG)
    exact lt_of_lt_of_le h1 h2
  exact exists_mem_notMem_of_measure_lt (le_refl (volume G)) hB hlt

/-- The **good-length extension set**: the union of the order-`n` CF extensions
`cfCylinder (w ++ u)` whose continuant is short (`K(u) ≤ e^{Cn}`, i.e.
relative length `≥ e^{-2Cn}/2`).  Encoded as a biUnion over *all* genuine
`n`-words with the bad ones sent to `∅`, so its measure matches
`half_mass_long_extensions`'s tsum verbatim (no subtype reindexing). -/
noncomputable def goodExtSet (w : List ℕ) (C : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ u ∈ genWords n,
    (if (cfK u : ℝ) ≤ Real.exp (C * n) then cfCylinder (w ++ u) else ∅)

/-- The good-length extensions are pairwise disjoint (distinct same-length
words) and measurable, so their measure is exactly the good-length tsum. -/
theorem volume_goodExtSet (w : List ℕ) (C : ℝ) (n : ℕ) :
    volume (goodExtSet w C n)
      = ∑' u : genWords n,
          (if (cfK (u : List ℕ) : ℝ) ≤ Real.exp (C * n)
            then volume (cfCylinder (w ++ (u : List ℕ))) else 0) := by
  have hcount : (genWords n).Countable :=
    Set.Countable.mono (Set.subset_univ _) (Set.countable_univ)
  have hle : ∀ u : List ℕ,
      (if (cfK u : ℝ) ≤ Real.exp (C * n) then cfCylinder (w ++ u) else ∅)
        ⊆ cfCylinder (w ++ u) := by
    intro u; split
    · exact subset_rfl
    · exact Set.empty_subset _
  have hdisj : (genWords n).PairwiseDisjoint
      fun u : List ℕ => (if (cfK u : ℝ) ≤ Real.exp (C * n)
        then cfCylinder (w ++ u) else ∅) := by
    intro u hu u' hu' hne
    exact (cfCylinder_disjoint (by simp [hu.1, hu'.1])
      (fun heq => hne (List.append_cancel_left heq))).mono (hle u) (hle u')
  have hmeas : ∀ u ∈ genWords n, MeasurableSet
      (if (cfK u : ℝ) ≤ Real.exp (C * n) then cfCylinder (w ++ u) else ∅) := by
    intro u _; split
    · exact measurableSet_cfCylinder _
    · exact MeasurableSet.empty
  rw [goodExtSet, measure_biUnion hcount hdisj hmeas]
  refine tsum_congr fun u => ?_
  split
  · rfl
  · exact measure_empty

/-- Lebesgue ≤ `2 log 2 · γ` on `(0,1)` (invert the density-window lower
bound `1/(2 log 2) ≤` density). -/
lemma volume_le_ofReal_mul_gaussMeasure (s : Set ℝ) (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo (0 : ℝ) 1) :
    volume s ≤ ENNReal.ofReal (2 * Real.log 2) * gaussMeasure s := by
  have hpos : (0 : ℝ) < 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have h := volume_le_gaussMeasure s hs hsub
  calc volume s
      = ENNReal.ofReal (2 * Real.log 2)
          * (ENNReal.ofReal (2 * Real.log 2)⁻¹ * volume s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le,
          mul_inv_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (2 * Real.log 2) * gaussMeasure s := by gcongr

/-- The CF discrepancy bad zone is measurable (`blockCount` is measurable). -/
lemma measurableSet_cfBadZone (w v : List ℕ) (n : ℕ) (δ : ℝ) :
    MeasurableSet (cfBadZone w v n δ) := by
  have hg : Measurable (fun x => |blockCount (cfCylinder v) n x / n
      - (gaussMeasure (cfCylinder v)).toReal|) :=
    (((measurable_blockCount (cfCylinder v) (measurableSet_cfCylinder v) n).div_const
      _).sub_const _).abs
  have hset : MeasurableSet {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧
      δ ≤ |blockCount (cfCylinder v) n x / n
        - (gaussMeasure (cfCylinder v)).toReal|} := by
    rw [Set.setOf_and]
    exact measurableSet_Ioo.inter (measurableSet_le measurable_const hg)
  exact (measurableSet_cfCylinder w).inter
    ((measurable_gaussMap.iterate w.length) hset)

/-- **Step (α): the CF bad zone in Lebesgue.** The union of CF discrepancy bad
zones over a finite word family has *Lebesgue* measure at most `2 log 2` times
its γ-bound — i.e. still `O(1/n)`, now in the same measure as the good mass
and d-ary bad zones. -/
theorem volume_iUnion_cfBadZone_le
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    volume (⋃ v ∈ F, cfBadZone w v n δ)
      ≤ ENNReal.ofReal (2 * Real.log 2 *
          ∑ v ∈ F, 7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal
            / (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal) := by
  have hmeas : MeasurableSet (⋃ v ∈ F, cfBadZone w v n δ) :=
    Finset.measurableSet_biUnion F (fun v _ => measurableSet_cfBadZone w v n δ)
  have hsub : (⋃ v ∈ F, cfBadZone w v n δ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    refine Set.iUnion₂_subset fun v _ x hx => ?_
    exact hx.1.1
  set Sbd : ℝ := ∑ v ∈ F, 7 * ((8 * v.length + 80)
    * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n))
    * (gaussMeasure (cfCylinder w)).toReal with hSbd
  have hlog0 : (0 : ℝ) ≤ 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hγle : gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ) ≤ ENNReal.ofReal Sbd := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top gaussMeasure _)]
    exact ENNReal.ofReal_le_ofReal
      (gaussMeasure_aggregate_cfBadZone_le w hposw F hF n hn hδ)
  calc volume (⋃ v ∈ F, cfBadZone w v n δ)
      ≤ ENNReal.ofReal (2 * Real.log 2)
          * gaussMeasure (⋃ v ∈ F, cfBadZone w v n δ) :=
        volume_le_ofReal_mul_gaussMeasure _ hmeas hsub
    _ ≤ ENNReal.ofReal (2 * Real.log 2) * ENNReal.ofReal Sbd := by gcongr
    _ = ENNReal.ofReal (2 * Real.log 2 * Sbd) :=
        (ENNReal.ofReal_mul hlog0).symm

/-- **Step (γ-CF): the CF bad zone as a fraction of `|I_w|`.** Bounding
`γ(I_v) ≤ 1` and converting `γ(I_w) ≤ (log 2)⁻¹·|I_w|`, the CF bad zone has
Lebesgue measure `≤ (14·Σ_v(8|v|+80)/(δ²n))·|I_w|` — an explicit `O(1/n)`
multiple of `|I_w|`, ready for the combine. -/
theorem volume_iUnion_cfBadZone_le_vol
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    volume (⋃ v ∈ F, cfBadZone w v n δ)
      ≤ ENNReal.ofReal (14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n))
          * volume (cfCylinder w) := by
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hwfin : volume (cfCylinder w) ≠ ⊤ := by
    have h1 : volume (cfCylinder w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono (fun x hx => hx.1)
    rw [Real.volume_Ioo] at h1
    exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
  set μw : ℝ := (volume (cfCylinder w)).toReal with hμw
  have hα := volume_iUnion_cfBadZone_le w hposw F hF n hn hδ
  set S : ℝ := ∑ v ∈ F, 7 * ((8 * (v.length : ℝ) + 80)
    * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n))
    * (gaussMeasure (cfCylinder w)).toReal with hS
  set SL : ℝ := ∑ v ∈ F, (8 * (v.length : ℝ) + 80) with hSL
  have hSL0 : 0 ≤ SL := Finset.sum_nonneg fun v _ => by positivity
  -- γ(I_v) ≤ 1
  have hγv : ∀ v : List ℕ, (gaussMeasure (cfCylinder v)).toReal ≤ 1 := by
    intro v
    have h := ENNReal.toReal_mono (measure_ne_top gaussMeasure Set.univ)
      (measure_mono (Set.subset_univ (cfCylinder v)))
    rwa [gaussMeasure_univ, ENNReal.toReal_one] at h
  -- γ(I_w) ≤ (log 2)⁻¹·|I_w|
  have hγw : (gaussMeasure (cfCylinder w)).toReal ≤ (Real.log 2)⁻¹ * μw := by
    have h := gaussMeasure_le_volume (cfCylinder w) (measurableSet_cfCylinder w)
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← hμw] at h2
  -- S ≤ C0·SL with C0 = 7(log2)⁻¹μw/(δ²n)
  have hSbound : S ≤ (7 * (Real.log 2)⁻¹ * μw / (δ ^ 2 * n)) * SL := by
    rw [hS, hSL, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have hvw : (gaussMeasure (cfCylinder v)).toReal
        * (gaussMeasure (cfCylinder w)).toReal ≤ (Real.log 2)⁻¹ * μw :=
      (mul_le_of_le_one_left ENNReal.toReal_nonneg (hγv v)).trans hγw
    have hpre : (0 : ℝ) ≤ 7 * (8 * (v.length : ℝ) + 80) / (δ ^ 2 * n) := by
      positivity
    calc 7 * ((8 * (v.length : ℝ) + 80) * (gaussMeasure (cfCylinder v)).toReal
            / (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal
        = (7 * (8 * (v.length : ℝ) + 80) / (δ ^ 2 * n))
            * ((gaussMeasure (cfCylinder v)).toReal
              * (gaussMeasure (cfCylinder w)).toReal) := by ring
      _ ≤ (7 * (8 * (v.length : ℝ) + 80) / (δ ^ 2 * n))
            * ((Real.log 2)⁻¹ * μw) := mul_le_mul_of_nonneg_left hvw hpre
      _ = 7 * (Real.log 2)⁻¹ * μw / (δ ^ 2 * n) * (8 * (v.length : ℝ) + 80) := by
          ring
  -- 2 log 2 · S ≤ 14·SL/(δ²n)·μw
  have hkey : 2 * Real.log 2 * S ≤ 14 * SL / (δ ^ 2 * n) * μw := by
    have hstep : 2 * Real.log 2 * ((7 * (Real.log 2)⁻¹ * μw / (δ ^ 2 * n)) * SL)
        = 14 * SL / (δ ^ 2 * n) * μw := by
      field_simp [hlog0.ne', hδ.ne', hn0.ne']
      ring
    calc 2 * Real.log 2 * S
        ≤ 2 * Real.log 2 * ((7 * (Real.log 2)⁻¹ * μw / (δ ^ 2 * n)) * SL) :=
          mul_le_mul_of_nonneg_left hSbound (mul_nonneg (by norm_num) hlog0.le)
      _ = 14 * SL / (δ ^ 2 * n) * μw := hstep
  have hcoef0 : (0 : ℝ) ≤ 14 * SL / (δ ^ 2 * n) :=
    div_nonneg (mul_nonneg (by norm_num) hSL0) (by positivity)
  calc volume (⋃ v ∈ F, cfBadZone w v n δ)
      ≤ ENNReal.ofReal (2 * Real.log 2 * S) := hα
    _ ≤ ENNReal.ofReal (14 * SL / (δ ^ 2 * n) * μw) :=
        ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal (14 * SL / (δ ^ 2 * n)) * volume (cfCylinder w) := by
        rw [ENNReal.ofReal_mul hcoef0, hμw,
          ENNReal.ofReal_toReal hwfin]

/-- **The good-mass side of the Lemma-13 balance.** At least half the mass of
a genuine cylinder `I_w` lies in its good-length order-`n` extensions.  (The
constant `C` is the one from `half_mass_long_extensions`.) -/
theorem exists_C_half_le_volume_goodExtSet :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤ 2 * volume (goodExtSet w C n) := by
  obtain ⟨C, hC, hbound⟩ := half_mass_long_extensions
  refine ⟨C, hC, fun w hw hpos n => ?_⟩
  rw [volume_goodExtSet]
  exact hbound w hw hpos n

/-- **The Lemma-13 measure core.** Given a t-brick `B`, a finite CF word family
`F`, and thresholds `n, kmin` large enough that the CF discrepancy coefficient
`14·Σ(8|v|+80)/(δ²n) < ¼` and the d-ary coefficient
`Σ_d 12d²ρ_d^kmin/(1−ρ_d) < ¼`, some good-length order-`n` extension of `I_w`
avoids BOTH the CF discrepancy bad zone (for every `v ∈ F`) AND the aggregate
wide d-ary bad zone (every base `2 ≤ d ≤ t`, every block length `≥ kmin`).

This is the measure-theoretic heart of Becher–Yuhjtman Lemma 13: a point with
good CF *length*, good CF *block frequencies*, and good *d-ary* digits.  The
outstanding wiring (`kmin(n)` link + choosing `n₀` from the paper's schedule)
only has to make the two coefficient hypotheses hold. -/
theorem exists_good_avoiding_bad {t : ℕ} (B : TBrick t)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a)
    (n kmin : ℕ) (hn : 0 < n) {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε)
    (hεt : (t : ℝ) * ε ≤ 1) (hpos : volume (cfCylinder B.w) ≠ 0)
    {C : ℝ}
    (hhalf : volume (cfCylinder B.w) ≤ 2 * volume (goodExtSet B.w C n))
    (hCF : 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) < 1 / 4)
    (hdary : (∑ d ∈ Finset.Icc 2 t,
        24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
      < 1 / 4) :
    ∃ x ∈ goodExtSet B.w C n, Irrational x ∧
      x ∉ (⋃ v ∈ F, cfBadZone B.w v n δ) ∪
        (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k) := by
  -- finiteness of the base cylinder
  have hwfin : volume (cfCylinder B.w) ≠ ⊤ := by
    have h1 : volume (cfCylinder B.w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono (fun x hx => hx.1)
    rw [Real.volume_Ioo] at h1
    exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
  -- per-base nonnegativity of the d-ary summand
  have hxd : ∀ d ∈ Finset.Icc 2 t, 0 ≤ 24 * (d : ℝ) ^ 2
      * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
    exact div_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (daryBadRatio_pos d ε).le _))
      (by linarith [daryBadRatio_lt_one hd1 hε0])
  -- d-ary bad in `ofReal (…) * vol` form
  have hB₂ := TBrick.volume_aggregate_bad_le B hε0 hεt kmin
  rw [← ENNReal.ofReal_sum_of_nonneg hxd] at hB₂
  -- the two coefficients are nonnegative and sum below ½
  have hpCF : 0 ≤ 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) :=
    div_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun v _ => by positivity)) (by positivity)
  have hqD : 0 ≤ ∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
      * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) :=
    Finset.sum_nonneg hxd
  -- absorb the (null) rationals into the d-ary bad zone so the survivor is
  -- irrational (`Irrational x` is by definition `x ∉ Set.range ((↑) : ℚ → ℝ)`)
  have hB₂' : volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
        ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
        ∪ Set.range ((↑) : ℚ → ℝ))
      ≤ ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
          * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
        * volume (cfCylinder B.w) := by
    calc volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          ∪ Set.range ((↑) : ℚ → ℝ))
        ≤ volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          + volume (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
      _ = volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k) := by
          rw [(Set.countable_range _).measure_zero, add_zero]
      _ ≤ _ := hB₂
  obtain ⟨x, hxG, hxB⟩ := exists_mem_notMem_union_of_bounds hpCF hqD
    (by linarith) hpos hwfin hhalf
    (volume_iUnion_cfBadZone_le_vol B.w B.hw_pos F hF n hn hδ) hB₂'
  refine ⟨x, hxG, fun hrat => hxB (Or.inr (Or.inr hrat)), fun hmem => ?_⟩
  rcases hmem with h | h
  · exact hxB (Or.inl h)
  · exact hxB (Or.inr (Or.inl h))

/-- The d-ary coefficient `Σ_d 12d²ρ_d^kmin/(1−ρ_d) → 0` as `kmin → ∞`
(finite sum, each `ρ_d < 1`). -/
theorem tendsto_daryCoeff (t : ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    Filter.Tendsto (fun kmin => ∑ d ∈ Finset.Icc 2 t,
        24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
      Filter.atTop (nhds 0) := by
  have h0 : (0 : ℝ) = ∑ _d ∈ Finset.Icc 2 t, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_finsetSum _ fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
  have hρ0 : 0 ≤ daryBadRatio d ε := (daryBadRatio_pos d ε).le
  have hρ1 : daryBadRatio d ε < 1 := daryBadRatio_lt_one hd1 hε0
  have hkey : (fun kmin => 24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin
        / (1 - daryBadRatio d ε))
      = (fun kmin => (24 * (d : ℝ) ^ 2 / (1 - daryBadRatio d ε))
        * daryBadRatio d ε ^ kmin) := by
    funext kmin; ring
  rw [hkey]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
    (24 * (d : ℝ) ^ 2 / (1 - daryBadRatio d ε))

/-- For `kmin` large the d-ary coefficient drops below `¼` (the balance
threshold). -/
theorem exists_kmin_daryCoeff_lt (t : ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ kmin₀ : ℕ, ∀ kmin ≥ kmin₀, (∑ d ∈ Finset.Icc 2 t,
      24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε)) < 1 / 4 := by
  have h := (tendsto_order.1 (tendsto_daryCoeff t hε0)).2 (1 / 4) (by norm_num)
  exact Filter.eventually_atTop.1 h

/-- For `n` large the CF discrepancy coefficient `14·SL/(δ²n)` drops below `¼`. -/
theorem exists_N_cfCoeff_lt (SL : ℝ) (hSL : 0 ≤ SL) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → 14 * SL / (δ ^ 2 * n) < 1 / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (56 * SL / δ ^ 2)
  refine ⟨N, fun n hn hn0 => ?_⟩
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNn : (56 * SL / δ ^ 2) < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have h56 : 56 * SL < δ ^ 2 * n := by
    rw [div_lt_iff₀ hδ2] at hNn; linarith
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < δ ^ 2 * n)]
  linarith

/-- A genuine cylinder has positive Lebesgue measure (discharges the `hpos`
hypothesis of `exists_good_avoiding_bad*`). -/
theorem volume_cfCylinder_ne_zero (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : volume (cfCylinder w) ≠ 0 := by
  rw [volume_cfCylinder w hw hpos]
  have hK : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hK' : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

/-- **Lemma-13 measure core, unconditional for large `n`, `kmin`.** For every
t-brick (uniformly), there exist thresholds `N`, `kmin₀` beyond which a
good-length order-`n` extension of `I_w` avoids both the CF discrepancy bad
zone and the wide d-ary bad zone.  (The construction's schedule supplies `n`,
`kmin` past these thresholds; the thresholds depend only on `t, F, δ, ε`.) -/
theorem exists_good_avoiding_bad_of_large (t : ℕ)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ ε : ℝ}
    (hδ : 0 < δ) (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1)
    {C : ℝ}
    (hhalf : ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤ 2 * volume (goodExtSet w C n)) :
    ∃ N kmin₀ : ℕ, ∀ (B : TBrick t), ∀ n, N ≤ n → 0 < n → ∀ kmin ≥ kmin₀,
      ∃ x ∈ goodExtSet B.w C n, Irrational x ∧
        x ∉ (⋃ v ∈ F, cfBadZone B.w v n δ) ∪
          (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k) := by
  obtain ⟨N, hN⟩ := exists_N_cfCoeff_lt (∑ v ∈ F, (8 * (v.length : ℝ) + 80))
    (Finset.sum_nonneg fun v _ => by positivity) hδ
  obtain ⟨kmin₀, hkmin⟩ := exists_kmin_daryCoeff_lt t hε0
  refine ⟨N, kmin₀, fun B n hn hn0 kmin hk => ?_⟩
  exact exists_good_avoiding_bad B F hF n kmin hn0 hδ hε0 hεt
    (volume_cfCylinder_ne_zero B.w B.hw_ne B.hw_pos)
    (hhalf B.w B.hw_ne B.hw_pos n) (hN n hn hn0) (hkmin kmin hk)

end NormalNumbers
