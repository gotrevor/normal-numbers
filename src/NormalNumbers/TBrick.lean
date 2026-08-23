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

Remaining for the balance (next laps): the CF discrepancy side (aggregate
`chebyshev_blockCount_brick` across CF words via `CFDiscLt`), then combine
with `half_mass_long_extensions` to get a surviving good extension.
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

/-- **Aggregate wide d-ary bad zone bound.** Over all bases `2 ≤ d ≤ t` and
all block lengths `k ≥ kmin`, the union of wide d-ary bad zones (each inside
its own order-`m0 d` cell at index `j0 d`) has measure at most a finite sum
of geometric-in-`kmin` terms — one per base. -/
theorem volume_aggregate_daryBadZoneWide_le
    (t kmin : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1)
    (m0 : ℕ → ℕ) (j0 : ℕ → ℤ) :
    volume (⋃ d ∈ Finset.Icc 2 t, ⋃ k : ℕ, ⋃ (_ : kmin ≤ k),
        daryBadZoneWide d (m0 d) (j0 d) ε k)
      ≤ ∑ d ∈ Finset.Icc 2 t, ENNReal.ofReal
          (6 * d / d ^ (m0 d) * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) := by
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum ?_)
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
  have hdε : (d : ℝ) * ε ≤ 1 := by
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast hd.2
    calc (d : ℝ) * ε ≤ (t : ℝ) * ε := by gcongr
      _ ≤ 1 := hεt
  exact volume_iUnion_daryBadZoneWide_le d (m0 d) hd1 (j0 d) hε0 hdε kmin

/-- **The d-ary side of the Lemma-13 balance.** For a t-brick `B`, the
aggregate wide d-ary bad zone (all bases `2 ≤ d ≤ t`, all block lengths
`k ≥ kmin`, in the brick's own cells) has measure at most
`C(t,ε,kmin)·|I_w|`, where the constant is a finite sum of geometric-in-`kmin`
terms.  Since each term `→ 0` as `kmin → ∞`, so does the constant: the d-ary
bad mass is eventually an arbitrarily small fraction of `|I_w|`. -/
theorem TBrick.volume_aggregate_bad_le {t : ℕ} (B : TBrick t)
    {ε : ℝ} (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1) (kmin : ℕ) :
    volume (⋃ d ∈ Finset.Icc 2 t, ⋃ k : ℕ, ⋃ (_ : kmin ≤ k),
        daryBadZoneWide d (B.m d) (B.j d) ε k)
      ≤ (∑ d ∈ Finset.Icc 2 t, ENNReal.ofReal
          (12 * d ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε)))
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
  have hsplit : (6 * (d : ℝ) / d ^ (B.m d) * daryBadRatio d ε ^ kmin
        / (1 - daryBadRatio d ε))
      = (6 * d * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
        * ((d : ℝ) ^ (B.m d))⁻¹ := by
    ring
  have hcoef_nonneg : 0 ≤ 6 * (d : ℝ) * daryBadRatio d ε ^ kmin
      / (1 - daryBadRatio d ε) := by positivity
  calc ENNReal.ofReal (6 * d / d ^ (B.m d) * daryBadRatio d ε ^ kmin
          / (1 - daryBadRatio d ε))
      = ENNReal.ofReal (6 * d * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε))
          * ENNReal.ofReal ((d : ℝ) ^ (B.m d))⁻¹ := by
        rw [hsplit, ENNReal.ofReal_mul hcoef_nonneg]
    _ ≤ ENNReal.ofReal (6 * d * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε))
          * (ENNReal.ofReal (2 * d) * volume (cfCylinder B.w)) := by
        gcongr
        exact B.hratio d hd.1 hd.2
    _ = ENNReal.ofReal (12 * d ^ 2 * daryBadRatio d ε ^ kmin
            / (1 - daryBadRatio d ε)) * volume (cfCylinder B.w) := by
        have hreal : (6 * (d : ℝ) * daryBadRatio d ε ^ kmin
              / (1 - daryBadRatio d ε)) * (2 * d)
            = 12 * d ^ 2 * daryBadRatio d ε ^ kmin
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

end NormalNumbers
