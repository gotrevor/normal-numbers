/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-EQ: a CF-normal orbit equidistributes for INTERVALS, not only for cylinders

`IsCFNormal x` is a statement about cylinder frequencies.  Route A's architecture (S7-BF) needs
more: the Cesàro average of the reference block observable, which is an interval-step function of
the orbit point (the state-dependent target `s⁻¹(I_w)` is an interval, not a cylinder).  This
module closes that gap unconditionally:

    tendsto_blockCount_Ioo :  blockCount (Ioo α β) p x / p  →  γ (Ioo α β)

for every CF-normal `x` whose orbit stays in `(0,1)` and every `0 ≤ α ≤ β ≤ 1`.

## The proof

A two-sided cylinder squeeze at level `M`, with `δ = 2/2^M` the level-`M` diameter bound
(S7-CV `dist_le_of_mem_cfCylinder`):

* **Outer.**  Every orbit point in `(α,β)` lies in some level-`M` cylinder; if its digits are
  bounded by `B` that cylinder MEETS `(α,β)`, so it belongs to `meetWords`.  The exceptional mass
  (unbounded digits) is paid once by `exists_boundedWords_sum_gt`.  The cover's mass is at most
  `γ(α−δ, β+δ)` by the sharp form of S7-CV, and thickening costs `2δ/log 2`.
* **Inner.**  Every level-`M`, digit-`≤B` cylinder meeting `(α+δ, β−δ)` is CONTAINED in `(α,β)`,
  so `insideWords` covers `(α+δ, β−δ)` up to the same exceptional mass; thinning costs `2δ/log 2`.

Both families are finite, so S7-WN (`tendsto_windowFreq`) evaluates their frequencies exactly, and
`δ → 0`, exceptional mass `→ 0` closes the squeeze.  No absolute continuity, no ergodic theorem,
no hypothesis beyond CF-normality of `x`.

## Guard rule

Content locator: the two `2δ/log 2` terms are where the discreteness of the cylinder partition is
paid; with `δ = 0` the argument would be the trivial "a set is covered by the cylinders it meets".
Degenerate cases: `β ≤ α` gives `Ioo α β = ∅`, `blockCount = 0` and `γ = 0`, and every bound above
is `0 ≤ 0`; `M = 0` is excluded (the empty word is not a genuine cylinder), and the exceptional
family is never empty because the digit bound `B` is chosen after `ε`.
-/
import NormalNumbers.VandeheyS7Cover
import NormalNumbers.VandeheyS7WindowFreq
import NormalNumbers.VandeheyOutputFreq

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

attribute [local instance] Classical.propDecidable

/-! ## Edge mass: thickening or thinning an interval costs `2δ/log 2` -/

lemma gaussMeasure_ne_top (s : Set ℝ) : gaussMeasure s ≠ ⊤ := (measure_lt_top gaussMeasure s).ne

lemma gaussMeasure_Icc_toReal_le {u v δ : ℝ} (hδ : 0 ≤ δ) (h : v - u ≤ δ) :
    (gaussMeasure (Set.Icc u v)).toReal ≤ δ / Real.log 2 := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (gaussMeasure_le_volume _ measurableSet_Icc).trans ?_
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- A set split into a main part and two edges. -/
lemma gaussMeasure_toReal_le_add_edges {A B C D : Set ℝ} (hsub : A ⊆ B ∪ (C ∪ D)) {c d : ℝ}
    (hC : (gaussMeasure C).toReal ≤ c) (hD : (gaussMeasure D).toReal ≤ d) :
    (gaussMeasure A).toReal ≤ (gaussMeasure B).toReal + (c + d) := by
  have hstep : gaussMeasure A ≤ gaussMeasure B + (gaussMeasure C + gaussMeasure D) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    gcongr
    exact measure_union_le _ _
  have hfin : gaussMeasure B + (gaussMeasure C + gaussMeasure D) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨gaussMeasure_ne_top _, ENNReal.add_ne_top.2 ⟨?_, ?_⟩⟩
    · exact gaussMeasure_ne_top _
    · exact gaussMeasure_ne_top _
  have h := ENNReal.toReal_mono hfin hstep
  rw [ENNReal.toReal_add (gaussMeasure_ne_top _)
      (ENNReal.add_ne_top.2 ⟨gaussMeasure_ne_top _, gaussMeasure_ne_top _⟩),
    ENNReal.toReal_add (gaussMeasure_ne_top _) (gaussMeasure_ne_top _)] at h
  linarith

lemma gaussMeasure_Ioo_thicken_le {α β a b δ : ℝ} (hδ : 0 ≤ δ)
    (ha : α - δ ≤ a) (hb : b ≤ β + δ) :
    (gaussMeasure (Set.Ioo a b)).toReal
      ≤ (gaussMeasure (Set.Ioo α β)).toReal + 2 * δ / Real.log 2 := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo α β ∪ (Set.Icc a α ∪ Set.Icc β b) := by
    intro z hz
    by_cases h1 : α < z
    · by_cases h2 : z < β
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨not_lt.1 h2, le_of_lt hz.2⟩)
    · exact Or.inr (Or.inl ⟨le_of_lt hz.1, not_lt.1 h1⟩)
  have h := gaussMeasure_toReal_le_add_edges hsub
    (gaussMeasure_Icc_toReal_le hδ (by linarith : α - a ≤ δ))
    (gaussMeasure_Icc_toReal_le hδ (by linarith : b - β ≤ δ))
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : δ / Real.log 2 + δ / Real.log 2 = 2 * δ / Real.log 2 := by ring
  linarith [h, this ▸ h]

lemma gaussMeasure_Ioo_thin_le {α β a b δ : ℝ} (hδ : 0 ≤ δ)
    (ha : a ≤ α + δ) (hb : β - δ ≤ b) :
    (gaussMeasure (Set.Ioo α β)).toReal
      ≤ (gaussMeasure (Set.Ioo a b)).toReal + 2 * δ / Real.log 2 := by
  have hsub : Set.Ioo α β ⊆ Set.Ioo a b ∪ (Set.Icc α a ∪ Set.Icc b β) := by
    intro z hz
    by_cases h1 : a < z
    · by_cases h2 : z < b
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨not_lt.1 h2, le_of_lt hz.2⟩)
    · exact Or.inr (Or.inl ⟨le_of_lt hz.1, not_lt.1 h1⟩)
  have h := gaussMeasure_toReal_le_add_edges hsub
    (gaussMeasure_Icc_toReal_le hδ (by linarith : a - α ≤ δ))
    (gaussMeasure_Icc_toReal_le hδ (by linarith : β - b ≤ δ))
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq : δ / Real.log 2 + δ / Real.log 2 = 2 * δ / Real.log 2 := by ring
  linarith [h, heq ▸ h]

/-! ## The two cylinder families -/

/-- The level-`M`, digit-`≤ B` words whose cylinder MEETS the target interval. -/
noncomputable def meetWords (B M : ℕ) (α β : ℝ) : Finset (List ℕ) :=
  (boundedWords B M).filter fun v => ∃ t ∈ cfCylinder v, t ∈ Set.Ioo α β

/-- The level-`M`, digit-`≤ B` words whose cylinder is CONTAINED in the target interval. -/
noncomputable def insideWords (B M : ℕ) (α β : ℝ) : Finset (List ℕ) :=
  (boundedWords B M).filter fun v => cfCylinder v ⊆ Set.Ioo α β

lemma boundedWords_len {B M : ℕ} {v : List ℕ} (hv : v ∈ boundedWords B M) : v.length = M :=
  (mem_boundedWords.1 hv).1

lemma boundedWords_pos {B M : ℕ} {v : List ℕ} (hv : v ∈ boundedWords B M) : ∀ a ∈ v, 1 ≤ a :=
  fun a ha => ((mem_boundedWords.1 hv).2 a ha).1

lemma boundedWords_ne_nil {B M : ℕ} (hM : 0 < M) {v : List ℕ} (hv : v ∈ boundedWords B M) :
    v ≠ [] := by
  intro h
  have := boundedWords_len hv
  rw [h] at this
  simp at this
  omega

/-- The level-`M` diameter bound, for a bounded-digit word. -/
lemma boundedWords_diam {B M : ℕ} (hM : 0 < M) {v : List ℕ} (hv : v ∈ boundedWords B M)
    {u t : ℝ} (hu : u ∈ cfCylinder v) (ht : t ∈ cfCylinder v) : |u - t| ≤ 2 / 2 ^ M := by
  have h := dist_le_of_mem_cfCylinder (boundedWords_ne_nil hM hv) (boundedWords_pos hv) hu ht
  rwa [boundedWords_len hv] at h

/-! ## Mass of the two families -/

lemma gaussMeasure_biUnion_toReal {S : Finset (List ℕ)} {M : ℕ} (hlen : ∀ v ∈ S, v.length = M) :
    (gaussMeasure (⋃ v ∈ S, cfCylinder v)).toReal
      = ∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal := by
  have hdisj : (S : Set (List ℕ)).PairwiseDisjoint (fun v => cfCylinder v) :=
    fun u hu v hv hne => cfCylinder_disjoint (by rw [hlen u hu, hlen v hv]) hne
  have h := measure_biUnion_finset (μ := gaussMeasure) hdisj
    (fun v _ => measurableSet_cfCylinder v)
  rw [h, ENNReal.toReal_sum (fun v _ => gaussMeasure_ne_top _)]

lemma measurableSet_biUnion_cfCylinder (S : Finset (List ℕ)) :
    MeasurableSet (⋃ v ∈ S, cfCylinder v) :=
  Set.Finite.measurableSet_biUnion S.finite_toSet (fun v _ => measurableSet_cfCylinder v)

/-- The mass missed by the bounded-digit family, as a real number. -/
lemma gaussMeasure_compl_boundedWords_toReal (B M : ℕ) :
    (gaussMeasure ((⋃ v ∈ boundedWords B M, cfCylinder v)ᶜ)).toReal
      = 1 - ∑ v ∈ boundedWords B M, (gaussMeasure (cfCylinder v)).toReal := by
  have hmeas := measurableSet_biUnion_cfCylinder (boundedWords B M)
  have hle : gaussMeasure (⋃ v ∈ boundedWords B M, cfCylinder v) ≤ 1 := by
    rw [← gaussMeasure_univ]
    exact measure_mono (Set.subset_univ _)
  rw [measure_compl hmeas (gaussMeasure_ne_top _), gaussMeasure_univ,
    ENNReal.toReal_sub_of_le hle (by simp), ENNReal.toReal_one,
    gaussMeasure_biUnion_toReal (fun v hv => boundedWords_len hv)]

/-- **Outer bound.**  The cover's mass is at most that of the thickened interval. -/
lemma sum_meetWords_le {B M : ℕ} (hM : 0 < M) (α β : ℝ) :
    (∑ v ∈ meetWords B M α β, (gaussMeasure (cfCylinder v)).toReal)
      ≤ (gaussMeasure (Set.Ioo (max (α - 2 / 2 ^ M) 0) (min (β + 2 / 2 ^ M) 1))).toReal := by
  refine sum_gaussMeasure_cover_le_measure (M := M) (δ := 2 / 2 ^ M) ?_ ?_ ?_
  · intro v hv
    exact boundedWords_len (Finset.mem_filter.1 hv).1
  · intro v hv u hu t ht
    exact boundedWords_diam hM (Finset.mem_filter.1 hv).1 hu ht
  · intro v hv
    exact (Finset.mem_filter.1 hv).2

/-- Every bounded-digit level-`M` cylinder that meets the thinned interval lies inside the
target, so the inside family covers the thinned interval up to the exceptional mass. -/
lemma Ioo_subset_insideWords_union {B M : ℕ} (hM : 0 < M) (α β : ℝ) :
    Set.Ioo (α + 2 / 2 ^ M) (β - 2 / 2 ^ M)
      ⊆ (⋃ v ∈ insideWords B M α β, cfCylinder v)
        ∪ (⋃ v ∈ boundedWords B M, cfCylinder v)ᶜ := by
  intro z hz
  by_cases hw : z ∈ ⋃ v ∈ boundedWords B M, cfCylinder v
  · obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.1 hw
    refine Or.inl (Set.mem_iUnion₂.2 ⟨v, Finset.mem_filter.2 ⟨hv, ?_⟩, hzv⟩)
    intro u hu
    have hd := boundedWords_diam hM hv hu hzv
    rw [abs_le] at hd
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · exact Or.inr hw

/-- **Inner bound.**  The inside family's mass is at least that of the thinned interval, less the
exceptional mass. -/
lemma gaussMeasure_Ioo_thin_le_sum_insideWords {B M : ℕ} (hM : 0 < M) (α β : ℝ) :
    (gaussMeasure (Set.Ioo (α + 2 / 2 ^ M) (β - 2 / 2 ^ M))).toReal
      ≤ (∑ v ∈ insideWords B M α β, (gaussMeasure (cfCylinder v)).toReal)
        + (1 - ∑ v ∈ boundedWords B M, (gaussMeasure (cfCylinder v)).toReal) := by
  have hstep : gaussMeasure (Set.Ioo (α + 2 / 2 ^ M) (β - 2 / 2 ^ M))
      ≤ gaussMeasure (⋃ v ∈ insideWords B M α β, cfCylinder v)
        + gaussMeasure ((⋃ v ∈ boundedWords B M, cfCylinder v)ᶜ) :=
    (measure_mono (Ioo_subset_insideWords_union hM α β)).trans (measure_union_le _ _)
  have hfin : gaussMeasure (⋃ v ∈ insideWords B M α β, cfCylinder v)
      + gaussMeasure ((⋃ v ∈ boundedWords B M, cfCylinder v)ᶜ) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨gaussMeasure_ne_top _, gaussMeasure_ne_top _⟩
  have h := ENNReal.toReal_mono hfin hstep
  have hins : (gaussMeasure (⋃ v ∈ insideWords B M α β, cfCylinder v)).toReal
      = ∑ v ∈ insideWords B M α β, (gaussMeasure (cfCylinder v)).toReal :=
    gaussMeasure_biUnion_toReal (M := M) (fun v hv => boundedWords_len (Finset.mem_filter.1 hv).1)
  rw [ENNReal.toReal_add (gaussMeasure_ne_top _) (gaussMeasure_ne_top _),
    gaussMeasure_compl_boundedWords_toReal, hins] at h
  exact h

/-! ## The orbit count -/

lemma blockIndic_eq_one' {A : Set ℝ} {z : ℝ} (h : z ∈ A) : blockIndic A z = 1 := by
  rw [blockIndic, Set.indicator_of_mem h]
  rfl

lemma blockIndic_eq_zero' {A : Set ℝ} {z : ℝ} (h : z ∉ A) : blockIndic A z = 0 := by
  rw [blockIndic, Set.indicator_of_notMem h]

/-- Pointwise domination: the target's indicator is at most the cover's, plus the indicator of the
bounded-digit family's complement. -/
lemma blockIndic_Ioo_le_cover (B M : ℕ) (α β : ℝ) (z : ℝ) :
    blockIndic (Set.Ioo α β) z
      ≤ blockIndic (⋃ v ∈ meetWords B M α β, cfCylinder v) z
        + (1 - blockIndic (⋃ v ∈ boundedWords B M, cfCylinder v) z) := by
  have hn1 := blockIndic_nonneg (⋃ v ∈ meetWords B M α β, cfCylinder v) z
  have hl2 := blockIndic_le_one (⋃ v ∈ boundedWords B M, cfCylinder v) z
  by_cases hz : z ∈ Set.Ioo α β
  · by_cases hw : z ∈ ⋃ v ∈ boundedWords B M, cfCylinder v
    · obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.1 hw
      have hmem : z ∈ ⋃ u ∈ meetWords B M α β, cfCylinder u :=
        Set.mem_iUnion₂.2 ⟨v, Finset.mem_filter.2 ⟨hv, ⟨z, hzv, hz⟩⟩, hzv⟩
      rw [blockIndic_eq_one' hz, blockIndic_eq_one' hmem]
      linarith
    · rw [blockIndic_eq_one' hz, blockIndic_eq_zero' hw]
      linarith
  · rw [blockIndic_eq_zero' hz]
    linarith

lemma blockCount_Ioo_le_cover (B M : ℕ) (α β : ℝ) (p : ℕ) (x : ℝ) :
    blockCount (Set.Ioo α β) p x
      ≤ blockCount (⋃ v ∈ meetWords B M α β, cfCylinder v) p x
        + ((p : ℝ) - blockCount (⋃ v ∈ boundedWords B M, cfCylinder v) p x) := by
  rw [blockCount_apply, blockCount_apply, blockCount_apply]
  have hp : ((p : ℝ)) = ∑ _k ∈ range p, (1:ℝ) := by simp
  rw [hp, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => blockIndic_Ioo_le_cover B M α β _

/-- A level fine enough that the two edge corrections cost less than `ε`. -/
lemma exists_level {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ 2 * (2 / 2 ^ M) / Real.log 2 ≤ ε := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 / (ε * Real.log 2)) (by norm_num : (1:ℝ) < 2)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hmono : (2:ℝ) ^ n ≤ 2 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ n)
  have hstep : (4:ℝ) / (ε * Real.log 2) < 2 ^ (n + 1) := lt_of_lt_of_le hn hmono
  rw [div_lt_iff₀ (by positivity)] at hstep
  have hkey : (4:ℝ) / 2 ^ (n + 1) ≤ ε * Real.log 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have heq : 2 * (2 / 2 ^ (n + 1)) / Real.log 2 = (4 / 2 ^ (n + 1)) / Real.log 2 := by ring
  rw [heq, div_le_iff₀ hlog]
  linarith

/-- **Upper half of the squeeze.** -/
theorem eventually_blockCount_Ioo_div_le {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {α β : ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (Set.Ioo α β) p x / (p : ℝ) ≤ (gaussMeasure (Set.Ioo α β)).toReal + ε := by
  obtain ⟨M, hM0, hMε⟩ := exists_level (show (0:ℝ) < ε / 3 by linarith)
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt M (show (0:ℝ) < ε / 3 by linarith)
  set δ : ℝ := 2 / 2 ^ M with hδdef
  have hδ0 : (0:ℝ) ≤ δ := by rw [hδdef]; positivity
  set mS := ∑ v ∈ meetWords B M α β, (gaussMeasure (cfCylinder v)).toReal with hmS
  set mG := ∑ v ∈ boundedWords B M, (gaussMeasure (cfCylinder v)).toReal with hmG
  have hmass : mS ≤ (gaussMeasure (Set.Ioo α β)).toReal + ε / 3 := by
    refine le_trans (sum_meetWords_le hM0 α β) ?_
    refine le_trans (gaussMeasure_Ioo_thicken_le (α := α) (β := β) hδ0
      (le_max_left _ _) (min_le_left _ _)) ?_
    linarith
  have hlenS : ∀ v ∈ meetWords B M α β, v.length = M := fun v hv =>
    boundedWords_len (Finset.mem_filter.1 hv).1
  have hposS : ∀ v ∈ meetWords B M α β, ∀ a ∈ v, 1 ≤ a := fun v hv =>
    boundedWords_pos (Finset.mem_filter.1 hv).1
  have hfS := tendsto_windowFreq (S := meetWords B M α β) hx horb hM0 hlenS hposS
  have hfG := tendsto_windowFreq (S := boundedWords B M) hx horb hM0
    (fun v hv => boundedWords_len hv) (fun v hv => boundedWords_pos hv)
  have hone : Tendsto (fun p : ℕ => ((p : ℝ)) / (p : ℝ)) atTop (nhds 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
    rw [div_self hpR.ne']
  have htot : Tendsto (fun p : ℕ =>
      blockCount (⋃ v ∈ meetWords B M α β, cfCylinder v) p x / (p : ℝ)
        + ((p : ℝ) / (p : ℝ)
          - blockCount (⋃ v ∈ boundedWords B M, cfCylinder v) p x / (p : ℝ))) atTop
      (nhds (mS + (1 - mG))) := by
    simpa using (hfS.add (hone.sub hfG))
  have hev := htot.eventually
    (eventually_lt_nhds (show mS + (1 - mG) < mS + (1 - mG) + ε / 3 by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  rw [div_self hpR.ne'] at hp
  have hle := blockCount_Ioo_le_cover B M α β p x
  have hnum : blockCount (Set.Ioo α β) p x / (p : ℝ)
      ≤ blockCount (⋃ v ∈ meetWords B M α β, cfCylinder v) p x / (p : ℝ)
        + (1 - blockCount (⋃ v ∈ boundedWords B M, cfCylinder v) p x / (p : ℝ)) := by
    rw [div_le_iff₀ hpR]
    have heq : (blockCount (⋃ v ∈ meetWords B M α β, cfCylinder v) p x / (p : ℝ)
        + (1 - blockCount (⋃ v ∈ boundedWords B M, cfCylinder v) p x / (p : ℝ))) * (p : ℝ)
        = blockCount (⋃ v ∈ meetWords B M α β, cfCylinder v) p x
          + ((p : ℝ) - blockCount (⋃ v ∈ boundedWords B M, cfCylinder v) p x) := by
      field_simp
    rw [heq]
    exact hle
  linarith

/-- **Lower half of the squeeze.** -/
theorem eventually_le_blockCount_Ioo_div {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {α β : ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      (gaussMeasure (Set.Ioo α β)).toReal - ε ≤ blockCount (Set.Ioo α β) p x / (p : ℝ) := by
  obtain ⟨M, hM0, hMε⟩ := exists_level (show (0:ℝ) < ε / 3 by linarith)
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt M (show (0:ℝ) < ε / 3 by linarith)
  set δ : ℝ := 2 / 2 ^ M with hδdef
  have hδ0 : (0:ℝ) ≤ δ := by rw [hδdef]; positivity
  set mI := ∑ v ∈ insideWords B M α β, (gaussMeasure (cfCylinder v)).toReal with hmI
  set mG := ∑ v ∈ boundedWords B M, (gaussMeasure (cfCylinder v)).toReal with hmG
  have hmass : (gaussMeasure (Set.Ioo α β)).toReal ≤ mI + 2 * (ε / 3) := by
    have hthin := gaussMeasure_Ioo_thin_le (α := α) (β := β) (a := α + δ) (b := β - δ) hδ0
      (le_refl _) (le_refl _)
    have hinner := gaussMeasure_Ioo_thin_le_sum_insideWords (B := B) hM0 α β
    rw [← hδdef] at hinner
    linarith
  have hsub : (⋃ v ∈ insideWords B M α β, cfCylinder v) ⊆ Set.Ioo α β := by
    refine Set.iUnion₂_subset fun v hv => ?_
    exact (Finset.mem_filter.1 hv).2
  have hfI := tendsto_windowFreq (S := insideWords B M α β) hx horb hM0
    (fun v hv => boundedWords_len (Finset.mem_filter.1 hv).1)
    (fun v hv => boundedWords_pos (Finset.mem_filter.1 hv).1)
  have hev := hfI.eventually (eventually_gt_nhds (show mI - ε / 3 < mI by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hmono : blockCount (⋃ v ∈ insideWords B M α β, cfCylinder v) p x
      ≤ blockCount (Set.Ioo α β) p x := blockCount_mono hsub p x
  have hdiv : blockCount (⋃ v ∈ insideWords B M α β, cfCylinder v) p x / (p : ℝ)
      ≤ blockCount (Set.Ioo α β) p x / (p : ℝ) := by
    rw [div_le_div_iff_of_pos_right hpR]
    exact hmono
  linarith

/-- **S7-EQ.**  A CF-normal orbit equidistributes for intervals, with the Gauss measure as the
limit.  No absolute continuity and no ergodic theorem: only CF-normality of `x`. -/
theorem tendsto_blockCount_Ioo {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (α β : ℝ) :
    Tendsto (fun p => blockCount (Set.Ioo α β) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (Set.Ioo α β)).toReal) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU := eventually_blockCount_Ioo_div_le hx horb (α := α) (β := β)
    (show (0:ℝ) < ε / 2 by linarith)
  have hL := eventually_le_blockCount_Ioo_div hx horb (α := α) (β := β)
    (show (0:ℝ) < ε / 2 by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hU.and hL)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hu, hl⟩ := hN n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.gaussMeasure_Ioo_thicken_le
#print axioms NormalNumbers.VandeheyS7.gaussMeasure_Ioo_thin_le_sum_insideWords
#print axioms NormalNumbers.VandeheyS7.eventually_blockCount_Ioo_div_le
#print axioms NormalNumbers.VandeheyS7.eventually_le_blockCount_Ioo_div
#print axioms NormalNumbers.VandeheyS7.tendsto_blockCount_Ioo

end Audit
