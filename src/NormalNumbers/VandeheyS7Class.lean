/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CL: the finite-cell decomposition — `BlockAverageBound ⟸ ClassFreqBound + width-frequency`

This is mandated item (c) of the CURRENT DIRECTIVE.  Fact (δ) (S7-BX) puts the run's states of
width `≥ η` in a fixed compact box of `ℝ⁴`; S7-NR makes `s ↦ s.mob` Lipschitz there with a
modulus that is free of the width.  So the predictor `n ↦ s_n⁻¹(I_w)` factors, to precision
`κ = 4ρ/√(|det Φ|/6)`, through a FINITE family of *fixed* sets

    clusterSet t w κ  =  t.mob ⁻¹' (cthickening κ (I_w ∩ (0,1)))  ∩  (0,1) ,

one for each centre `t` of a `ρ`-net of the box (`mapBlockSet_subset_clusterSet`).

Given such a net — a centre map `cen : Fin M → MapState` and a cell assignment `idx`, bundled as
the hypothesis `StateNet` — the slot form of the crux (S7-SL) splits:

    slotCount(q+2)  ≤  2  +  widthBadCount(q)  +  Σ_{i<M} cellHitCount i q ,

`Σ_i cellCount i q ≤ runClock`, and therefore

    `blockAverageBound_of_classFreq` :
        ClassFreqBound (per-cell relative frequency ≤ B)  +  width-frequency  ⟹  BlockAverageBound B .

The point, recorded as the directive's warning: the sum over `i` is taken against `cellCount i`,
NOT against `p`.  Dropping the state constraint and summing would cost the factor `M(η,ρ)` and
give no fixed `C`; here the `cellCount`s add up to the clock and the constant survives.

What remains after this module is `ClassFreqBound` itself, and the width-frequency input
(S7-HT/S7-LG).  Nothing else.
-/
import NormalNumbers.VandeheyS7Slot
import NormalNumbers.VandeheyS7Ledger

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-! ## The fixed cluster sets -/

/-- The pullback of a `κ`-thickened target under a FIXED state `t`. -/
def clusterSet (t : MapState) (w : List ℕ) (κ : ℝ) : Set ℝ :=
  t.mob ⁻¹' (Metric.cthickening κ (cfCylinder w ∩ Set.Ioo (0:ℝ) 1)) ∩ Set.Ioo (0:ℝ) 1

/-- **Step 1 of the decomposition.**  A run state entrywise within `ρ` of `t` has its `j = 0`
block set inside the FIXED cluster set of `t` at scale `4ρ/√(|det Φ|/6)`. -/
theorem mapBlockSet_subset_clusterSet {Φ : MapState} (x : ℝ) (n : ℕ) {t : MapState} {ρ : ℝ}
    (ha : |(runState Φ x (n + 2)).a - t.a| ≤ ρ) (hb : |(runState Φ x (n + 2)).b - t.b| ≤ ρ)
    (hc : |(runState Φ x (n + 2)).c - t.c| ≤ ρ) (hd : |(runState Φ x (n + 2)).d - t.d| ≤ ρ)
    (w : List ℕ) :
    mapBlockSet (runState Φ x (n + 2)) w 0
      ⊆ clusterSet t w (4 * ρ / Real.sqrt (|Φ.det| / 6)) := by
  rintro z ⟨hz1, hz2⟩
  refine ⟨?_, hz2⟩
  have hzIcc : z ∈ Icc (0:ℝ) 1 := ⟨hz2.1.le, hz2.2.le⟩
  have hdist : |(runState Φ x (n + 2)).mob z - t.mob z| ≤ 4 * ρ / Real.sqrt (|Φ.det| / 6) := by
    by_cases hΦ : Φ.det = 0
    · exact absurd hΦ Φ.hdet
    · exact abs_mob_sub_runState_le hΦ x n hzIcc ha hb hc hd
  refine Metric.mem_cthickening_of_dist_le _ ((runState Φ x (n + 2)).mob z) _ _ ?_ ?_
  · simpa using hz1
  · rw [Real.dist_eq, abs_sub_comm]; exact hdist

/-! ## The net, the cells, and the three counts -/

/-- A `ρ`-net of the run's states of width `≥ η`: centres `cen`, a cell assignment `idx`, and the
guarantee that a wide state sits in the cell it is assigned to.  Fact (δ) is what makes such a
net exist with `M = M(η,ρ)`; this structure is the interface. -/
structure StateNet (Φ : MapState) (x : ℝ) (η ρ : ℝ) (M : ℕ) where
  cen : Fin M → MapState
  idx : ℕ → Fin M
  near : ∀ m : ℕ, η ≤ (runState Φ x (m + 2)).width →
    |(runState Φ x (m + 2)).a - (cen (idx m)).a| ≤ ρ ∧
    |(runState Φ x (m + 2)).b - (cen (idx m)).b| ≤ ρ ∧
    |(runState Φ x (m + 2)).c - (cen (idx m)).c| ≤ ρ ∧
    |(runState Φ x (m + 2)).d - (cen (idx m)).d| ≤ ρ

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

open Classical in
/-- Emission mass in cell `i` up to shifted time `q`. -/
noncomputable def cellCount (net : StateNet Φ x η ρ M) (i : Fin M) (q : ℕ) : ℝ :=
  ∑ m ∈ range q,
    if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then emitIndic Φ x (m + 2) else 0

open Classical in
/-- Emission mass in cell `i` that also lands in the cell's cluster set. -/
noncomputable def cellHitCount (net : StateNet Φ x η ρ M) (w : List ℕ) (i : Fin M) (q : ℕ) : ℝ :=
  ∑ m ∈ range q,
    if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then
      emitIndic Φ x (m + 2) *
        blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6)))
          (gaussMap^[m + 2] x)
    else 0

open Classical in
/-- Emission mass at times when the state is too narrow for the net to see. -/
noncomputable def widthBadCount (Φ : MapState) (x : ℝ) (η : ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ range q, if η ≤ (runState Φ x (m + 2)).width then 0 else emitIndic Φ x (m + 2)

/-! ## Bookkeeping -/

lemma sum_range_add_two (g : ℕ → ℝ) (q : ℕ) :
    ∑ n ∈ range (q + 2), g n = (g 0 + g 1) + ∑ m ∈ range q, g (m + 2) := by
  induction q with
  | zero => simp [Finset.sum_range_succ]
  | succ q ih =>
    rw [show q + 1 + 2 = (q + 2) + 1 by ring, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- **The cells partition the wide times.** -/
lemma sum_cellCount (net : StateNet Φ x η ρ M) (q : ℕ) :
    ∑ i : Fin M, cellCount net i q
      = ∑ m ∈ range q,
          (if η ≤ (runState Φ x (m + 2)).width then emitIndic Φ x (m + 2) else 0) := by
  classical
  unfold cellCount
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hw : η ≤ (runState Φ x (m + 2)).width
  · rw [if_pos hw]
    have : ∀ i : Fin M,
        (if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then emitIndic Φ x (m + 2) else 0)
          = (if net.idx m = i then emitIndic Φ x (m + 2) else 0) := by
      intro i; by_cases h : net.idx m = i <;> simp [h, hw]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by tauto)]

/-- **The emission mass in all cells is at most the clock.** -/
theorem sum_cellCount_le_runClock (net : StateNet Φ x η ρ M) (q : ℕ) :
    ∑ i : Fin M, cellCount net i q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  classical
  rw [sum_cellCount, runClock_eq_sum_emitIndic, sum_range_add_two]
  have h1 : ∑ m ∈ range q,
      (if η ≤ (runState Φ x (m + 2)).width then emitIndic Φ x (m + 2) else 0)
      ≤ ∑ m ∈ range q, emitIndic Φ x (m + 2) := by
    refine Finset.sum_le_sum fun m _ => ?_
    by_cases hw : η ≤ (runState Φ x (m + 2)).width
    · rw [if_pos hw]
    · rw [if_neg hw]; exact emitIndic_nonneg Φ x (m + 2)
  have h2 : 0 ≤ emitIndic Φ x 0 + emitIndic Φ x 1 := by
    have := emitIndic_nonneg Φ x 0; have := emitIndic_nonneg Φ x 1; linarith
  linarith

/-- **Step 2 of the decomposition.**  The slot count splits into the narrow times and the
cells. -/
theorem slotCount_le_split (net : StateNet Φ x η ρ M) (w : List ℕ) (q : ℕ) :
    slotCount Φ x w (q + 2)
      ≤ 2 + widthBadCount Φ x η q + ∑ i : Fin M, cellHitCount net w i q := by
  classical
  have hsplit := sum_range_add_two
    (fun n => emitIndic Φ x n * blockIndic (mapBlockSet (runState Φ x n) w 0) (gaussMap^[n] x)) q
  rw [slotCount, hsplit]
  have hfirst : emitIndic Φ x 0 * blockIndic (mapBlockSet (runState Φ x 0) w 0) (gaussMap^[0] x)
      + emitIndic Φ x 1 * blockIndic (mapBlockSet (runState Φ x 1) w 0) (gaussMap^[1] x) ≤ 2 := by
    have hb : ∀ (s : MapState) (z : ℝ), blockIndic (mapBlockSet s w 0) z ≤ 1 := by
      intro s z
      rw [blockIndic]
      by_cases hm : z ∈ mapBlockSet s w 0
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hbn : ∀ (s : MapState) (z : ℝ), 0 ≤ blockIndic (mapBlockSet s w 0) z := fun s z =>
      Set.indicator_nonneg (by intro _ _; norm_num) _
    rcases emitIndic_eq_zero_or_one Φ x 0 with h0 | h0 <;>
      rcases emitIndic_eq_zero_or_one Φ x 1 with h1 | h1 <;>
      rw [h0, h1] <;>
      nlinarith [hb (runState Φ x 0) (gaussMap^[0] x), hb (runState Φ x 1) (gaussMap^[1] x),
        hbn (runState Φ x 0) (gaussMap^[0] x), hbn (runState Φ x 1) (gaussMap^[1] x)]
  have hrest : ∑ m ∈ range q,
      emitIndic Φ x (m + 2) * blockIndic (mapBlockSet (runState Φ x (m + 2)) w 0)
        (gaussMap^[m + 2] x)
      ≤ widthBadCount Φ x η q + ∑ i : Fin M, cellHitCount net w i q := by
    unfold widthBadCount cellHitCount
    rw [Finset.sum_comm (s := (univ : Finset (Fin M)))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    set z := gaussMap^[m + 2] x with hz
    set e := emitIndic Φ x (m + 2) with he
    have hen : 0 ≤ e := emitIndic_nonneg Φ x (m + 2)
    by_cases hw : η ≤ (runState Φ x (m + 2)).width
    · rw [if_pos hw, zero_add]
      obtain ⟨ha, hb, hc, hd⟩ := net.near m hw
      have hsub := mapBlockSet_subset_clusterSet (Φ := Φ) x m ha hb hc hd w
      have hind : blockIndic (mapBlockSet (runState Φ x (m + 2)) w 0) z
          ≤ blockIndic (clusterSet (net.cen (net.idx m)) w
              (4 * ρ / Real.sqrt (|Φ.det| / 6))) z := by
        rw [blockIndic, blockIndic]
        by_cases hm : z ∈ mapBlockSet (runState Φ x (m + 2)) w 0
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hsub hm)]
        · rw [Set.indicator_of_notMem hm]
          exact Set.indicator_nonneg (by intro _ _; norm_num) _
      have hcell : ∑ i : Fin M,
          (if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then
            e * blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6))) z
          else 0)
          = e * blockIndic (clusterSet (net.cen (net.idx m)) w
              (4 * ρ / Real.sqrt (|Φ.det| / 6))) z := by
        have : ∀ i : Fin M,
            (if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then
              e * blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6))) z
            else 0)
            = (if net.idx m = i then
                e * blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6))) z
              else 0) := by
          intro i; by_cases h : net.idx m = i <;> simp [h, hw]
        rw [Finset.sum_congr rfl (fun i _ => this i)]
        simp
      rw [hcell]
      exact mul_le_mul_of_nonneg_left hind hen
    · rw [if_neg hw]
      have hz0 : ∑ i : Fin M,
          (if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then
            e * blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6))) z
          else 0) = 0 := Finset.sum_eq_zero fun i _ => by rw [if_neg (by tauto)]
      rw [hz0, add_zero]
      have hb : blockIndic (mapBlockSet (runState Φ x (m + 2)) w 0) z ≤ 1 := by
        rw [blockIndic]
        by_cases hm : z ∈ mapBlockSet (runState Φ x (m + 2)) w 0
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      have hbn : 0 ≤ blockIndic (mapBlockSet (runState Φ x (m + 2)) w 0) z :=
        Set.indicator_nonneg (by intro _ _; norm_num) _
      nlinarith
  linarith


/-! ## `ClassFreqBound`, and the reduction -/

/-- **`ClassFreqBound`** — the residual, stated as the directive requires: *per cell*, the
emission times whose orbit point lands in that cell's cluster set have relative frequency at most
`B` **among the emission times in that cell**.  The normalization is `cellCount i`, not `p`. -/
def ClassFreqBound (net : StateNet Φ x η ρ M) (w : List ℕ) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ i : Fin M, ∀ᶠ q in atTop,
    cellHitCount net w i q ≤ (B + ε) * cellCount net i q

/-- **The width-frequency input** — S7-HT's open half: narrow states are rare among emissions. -/
def WidthFreqBound (Φ : MapState) (x : ℝ) (η : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop,
    widthBadCount Φ x η q ≤ ε * ((runClock Φ x (q + 2) : ℕ) : ℝ)

/-- **S7-CL, mandated item (c).**  The finite-cell decomposition really does reduce
`BlockAverageBound` to `ClassFreqBound` plus the width-frequency bound, with NO loss of the
constant: the per-cell denominators sum to the clock. -/
theorem blockAverageBound_of_classFreq (net : StateNet Φ x η ρ M) (w : List ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop)
    (hCF : ClassFreqBound net w B) (hW : WidthFreqBound Φ x η) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) := by
  classical
  rw [blockAverageBound_iff_slot]
  intro ε hε
  set ε' := ε / 3 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hcells : ∀ᶠ q in atTop, ∀ i : Fin M,
      cellHitCount net w i q ≤ (B + ε') * cellCount net i q := by
    exact Filter.eventually_all.mpr (fun i => hCF ε' hε'pos i)
  have hwide := hW ε' hε'pos
  have hbig : ∀ᶠ q in atTop, (2:ℝ) ≤ ε' * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have := hclock.eventually_ge_atTop (2 / ε')
    filter_upwards [this] with q hq
    rw [div_le_iff₀ hε'pos] at hq
    linarith
  have hmain : ∀ᶠ q in atTop,
      slotCount Φ x w (q + 2) ≤ (B + ε) * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    filter_upwards [hcells, hwide, hbig] with q hc hw2 hb2
    have hsplit := slotCount_le_split net w q
    have hsum : ∑ i : Fin M, cellHitCount net w i q
        ≤ (B + ε') * ∑ i : Fin M, cellCount net i q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hc i
    have hcc : ∑ i : Fin M, cellCount net i q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
      sum_cellCount_le_runClock net q
    have hBε : 0 ≤ B + ε' := by linarith
    have h3 : (B + ε') * ∑ i : Fin M, cellCount net i q
        ≤ (B + ε') * ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcc hBε
    have : ε = 3 * ε' := by rw [hε']; ring
    nlinarith [hsplit, hsum, h3, hw2, hb2]
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp hmain
  refine eventually_atTop.mpr ⟨q₀ + 2, fun p hp => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
  exact hq₀ j (by omega)

end MapState

section Audit

#print axioms MapState.mapBlockSet_subset_clusterSet
#print axioms MapState.sum_cellCount
#print axioms MapState.sum_cellCount_le_runClock
#print axioms MapState.slotCount_le_split
#print axioms MapState.blockAverageBound_of_classFreq

end Audit

end NormalNumbers.VandeheyS7
