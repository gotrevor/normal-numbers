/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CM: `CellMemory`, and the pointwise bridge it buys

S7-MY isolated the mechanism that beats predictability: a selection determined by finitely many
recent digits makes the joint event "selected AND the next digits are `v`" the occurrence of ONE
word.  S7-CS made the cluster set short, so `cellCover_inv_log_two` covers it by finitely many
cells.  This module joins the two and names the hypothesis.

* `selIndic net i m` — the selection: time `m` emits, its state is wide, and it lies in cell `i`.
* `CellMemory net L` — the wall, stated: the selection is decided by the `L` input digits at
  positions `m+2−L … m+1`, i.e. by which cylinder `I_u` (`|u| = L`) the orbit point
  `G^{m+2−L}x` lies in.  This is fact (γ)'s complement: the matrix `s_m` remembers the whole
  history, but its **cell** in a `ρ`-net should not.
* `selIndic_mul_blockIndic_le` — **the pointwise bridge, proved**: under `CellMemory` and any cell
  cover `F` of the cluster set, the selected-and-hit indicator at time `m` is dominated by
  `∑_{u ∈ U i} ∑_{c ∈ F} 1_{cellSet (u ++ c.1) c.2}(G^{m+2−L}x)` — a sum of indicators of FIXED
  cells, evaluated at one orbit point.  Everything after this is CF-normality (S7-CellFreq) and
  quasi-Bernoulli mass (S7-HC), both already proved.
-/
import NormalNumbers.VandeheyS7Cluster
import NormalNumbers.VandeheyS7HitCell

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

open Classical in
/-- The selection at input time `m`: it emits, its state is wide, and the state lies in cell `i`. -/
noncomputable def selIndic (net : StateNet Φ x η ρ M) (i : Fin M) (m : ℕ) : ℝ :=
  if net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width then emitIndic Φ x (m + 2) else 0

lemma cellCount_eq_sum_selIndic (net : StateNet Φ x η ρ M) (i : Fin M) (q : ℕ) :
    cellCount net i q = ∑ m ∈ Finset.range q, selIndic net i m := rfl

lemma selIndic_nonneg (net : StateNet Φ x η ρ M) (i : Fin M) (m : ℕ) :
    0 ≤ selIndic net i m := by
  classical
  rw [selIndic]
  split
  · exact emitIndic_nonneg Φ x (m + 2)
  · exact le_refl 0

open Classical in
/-- **The wall, named.**  The selection is a function of the last `L` input digits: it is decided
by which of finitely many length-`L` cylinders the orbit point `G^{m+2−L}x` lies in. -/
def CellMemory (net : StateNet Φ x η ρ M) (L : ℕ) : Prop :=
  0 < L ∧ ∃ U : Fin M → Finset (List ℕ),
    (∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a)) ∧
    ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0

open Classical in
/-- **The pointwise bridge.**  Under `CellMemory` with selector words `U`, and for any finite cell
family `F` covering the cluster set along irrational points, the selected-and-hit indicator is
dominated by a sum of indicators of the fixed cells `u ++ c`, all evaluated at the single orbit
point `G^{m+2−L}x`. -/
theorem selIndic_mul_blockIndic_le {net : StateNet Φ x η ρ M} {L : ℕ}
    (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    {U : Fin M → Finset (List ℕ)}
    (hUlen : ∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a))
    (hUsel : ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0)
    {A : Set ℝ} {F : Finset (List ℕ × ℕ)}
    (hcov : ∀ z : ℝ, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → z ∈ A →
      ∃ c ∈ F, z ∈ cellSet c.1 c.2)
    (i : Fin M) (m : ℕ) (hm : L ≤ m + 2) :
    selIndic net i m * blockIndic A (gaussMap^[m + 2] x)
      ≤ ∑ u ∈ U i, ∑ c ∈ F,
          blockIndic (cellSet (u ++ c.1) c.2) (gaussMap^[m + 2 - L] x) := by
  classical
  set z : ℝ := gaussMap^[m + 2 - L] x with hz
  have hznn : ∀ (u : List ℕ) (c : List ℕ × ℕ), 0 ≤ blockIndic (cellSet (u ++ c.1) c.2) z :=
    fun u c => Set.indicator_nonneg (by intro _ _; norm_num) _
  have hsum_nonneg : 0 ≤ ∑ u ∈ U i, ∑ c ∈ F, blockIndic (cellSet (u ++ c.1) c.2) z :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun c _ => hznn u c
  have hsel := hUsel i m hm
  by_cases hex : ∃ u ∈ U i, z ∈ cfCylinder u
  · -- the selection fires; identify the orbit point `L` steps later
    rcases id hex with ⟨u, huU, huz⟩
    have hzirr : Irrational z := (irrational_orbit x hx hmem (m + 2 - L)).1
    have hzmem : z ∈ Set.Ioo (0:ℝ) 1 := (irrational_orbit x hx hmem (m + 2 - L)).2
    obtain ⟨hulen, hupos⟩ := hUlen i u huU
    have hshift : gaussMap^[u.length] z = gaussMap^[m + 2] x := by
      rw [hz, hulen, ← Function.iterate_add_apply]
      congr 1
      omega
    have hsel1 : selIndic net i m = 1 := by
      rw [hsel, if_pos hex]
    rw [hsel1, one_mul]
    by_cases hA : gaussMap^[m + 2] x ∈ A
    · -- the cover supplies a cell
      have hAirr : Irrational (gaussMap^[m + 2] x) := (irrational_orbit x hx hmem (m + 2)).1
      have hAmem : gaussMap^[m + 2] x ∈ Set.Ioo (0:ℝ) 1 := (irrational_orbit x hx hmem (m + 2)).2
      obtain ⟨c, hcF, hcmem⟩ := hcov _ hAirr hAmem hA
      have hjoint : z ∈ cellSet (u ++ c.1) c.2 := by
        refine (mem_cellSet_append_iff hzirr hzmem u c.1 c.2).mpr ⟨huz, ?_⟩
        rw [hshift]; exact hcmem
      have hone : blockIndic (cellSet (u ++ c.1) c.2) z = 1 := by
        rw [blockIndic, Set.indicator_of_mem hjoint]; rfl
      calc blockIndic A (gaussMap^[m + 2] x) = 1 := by
            rw [blockIndic, Set.indicator_of_mem hA]; rfl
        _ = blockIndic (cellSet (u ++ c.1) c.2) z := hone.symm
        _ ≤ ∑ c' ∈ F, blockIndic (cellSet (u ++ c'.1) c'.2) z :=
            Finset.single_le_sum (fun c' _ => hznn u c') hcF
        _ ≤ ∑ u' ∈ U i, ∑ c' ∈ F, blockIndic (cellSet (u' ++ c'.1) c'.2) z :=
            Finset.single_le_sum (fun u' _ => Finset.sum_nonneg fun c' _ => hznn u' c') huU
    · rw [blockIndic, Set.indicator_of_notMem hA]
      exact hsum_nonneg
  · rw [hsel, if_neg hex, zero_mul]
    exact hsum_nonneg


/-! ## Summing the bridge -/

open Classical in
lemma cellHitCount_eq_sum (net : StateNet Φ x η ρ M) (w : List ℕ) (i : Fin M) (q : ℕ) :
    cellHitCount net w i q
      = ∑ m ∈ Finset.range q, selIndic net i m *
          blockIndic (clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6)))
            (gaussMap^[m + 2] x) := by
  classical
  unfold cellHitCount selIndic
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

open Classical in
/-- **The count form of the bridge.**  Summing `selIndic_mul_blockIndic_le` over `m < q`: the
cell's hit count is, up to the `L` initial times, at most the total number of visits of the orbit
to the finitely many fixed cells `u ++ c`. -/
theorem cellHitCount_le_blockCounts {net : StateNet Φ x η ρ M} {L : ℕ}
    (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1) (w : List ℕ)
    {U : Fin M → Finset (List ℕ)}
    (hUlen : ∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a))
    (hUsel : ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0)
    {F : Finset (List ℕ × ℕ)} (i : Fin M)
    (hcov : ∀ z : ℝ, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 →
      z ∈ clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6)) →
      ∃ c ∈ F, z ∈ cellSet c.1 c.2)
    (q : ℕ) :
    cellHitCount net w i q
      ≤ (L : ℝ) + ∑ u ∈ U i, ∑ c ∈ F,
          blockCount (cellSet (u ++ c.1) c.2) (q + 2) x := by
  classical
  set A : Set ℝ := clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6)) with hA
  set g : List ℕ → List ℕ × ℕ → ℕ → ℝ :=
    fun u c k => blockIndic (cellSet (u ++ c.1) c.2) (gaussMap^[k] x) with hg
  have hgnn : ∀ u c k, 0 ≤ g u c k := fun u c k =>
    Set.indicator_nonneg (by intro _ _; norm_num) _
  set T : Finset ℕ := (Finset.range q).filter (fun m => L ≤ m + 2) with hT
  set Tc : Finset ℕ := (Finset.range q).filter (fun m => ¬ L ≤ m + 2) with hTc
  set f : ℕ → ℝ := fun m => selIndic net i m * blockIndic A (gaussMap^[m + 2] x) with hf
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m
    exact mul_nonneg (selIndic_nonneg net i m)
      (Set.indicator_nonneg (by intro _ _; norm_num) _)
  have hsplit : ∑ m ∈ Finset.range q, f m = ∑ m ∈ T, f m + ∑ m ∈ Tc, f m := by
    rw [hT, hTc, Finset.sum_filter_add_sum_filter_not]
  -- the initial times contribute at most `L`
  have hbad : ∑ m ∈ Tc, f m ≤ (L : ℝ) := by
    have hcard : Tc.card ≤ L := by
      have hsub : Tc ⊆ Finset.range L := by
        intro m hm
        have := (Finset.mem_filter.mp (hTc ▸ hm)).2
        exact Finset.mem_range.mpr (by omega)
      have := Finset.card_le_card hsub
      simpa using this
    have hone : ∀ m ∈ Tc, f m ≤ 1 := by
      intro m _
      have he : selIndic net i m ≤ 1 := by
        rw [selIndic]
        split
        · rcases emitIndic_eq_zero_or_one Φ x (m + 2) with h | h <;> rw [h] <;> norm_num
        · norm_num
      have hb : blockIndic A (gaussMap^[m + 2] x) ≤ 1 := by
        rw [blockIndic]
        by_cases hz : gaussMap^[m + 2] x ∈ A
        · rw [Set.indicator_of_mem hz]; norm_num
        · rw [Set.indicator_of_notMem hz]; norm_num
      have hbn : 0 ≤ blockIndic A (gaussMap^[m + 2] x) :=
        Set.indicator_nonneg (by intro _ _; norm_num) _
      have hen : 0 ≤ selIndic net i m := selIndic_nonneg net i m
      rw [hf]
      nlinarith
    calc ∑ m ∈ Tc, f m ≤ ∑ _m ∈ Tc, (1:ℝ) := Finset.sum_le_sum hone
      _ = (Tc.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (L : ℝ) := by exact_mod_cast hcard
  -- the rest is dominated by the fixed cells, after reindexing `m ↦ m + 2 − L`
  have hgood : ∑ m ∈ T, f m
      ≤ ∑ u ∈ U i, ∑ c ∈ F, blockCount (cellSet (u ++ c.1) c.2) (q + 2) x := by
    have hstep : ∀ m ∈ T, f m ≤ ∑ u ∈ U i, ∑ c ∈ F, g u c (m + 2 - L) := by
      intro m hm
      have hmL := (Finset.mem_filter.mp (hT ▸ hm)).2
      exact selIndic_mul_blockIndic_le hx hmem hUlen hUsel hcov i m hmL
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    -- reindex: `m ↦ m + 2 − L` is injective on `T` and lands in `range (q+2)`
    have hinj : ∀ m₁ ∈ T, ∀ m₂ ∈ T, m₁ + 2 - L = m₂ + 2 - L → m₁ = m₂ := by
      intro m₁ h₁ m₂ h₂ heq
      have h₁' := (Finset.mem_filter.mp (hT ▸ h₁)).2
      have h₂' := (Finset.mem_filter.mp (hT ▸ h₂)).2
      omega
    have himg : T.image (fun m => m + 2 - L) ⊆ Finset.range (q + 2) := by
      intro k hk
      obtain ⟨m, hmT, rfl⟩ := Finset.mem_image.mp hk
      have hmq := Finset.mem_range.mp (Finset.mem_filter.mp (hT ▸ hmT)).1
      exact Finset.mem_range.mpr (by omega)
    calc ∑ m ∈ T, g u c (m + 2 - L)
        = ∑ k ∈ T.image (fun m => m + 2 - L), g u c k := (Finset.sum_image hinj).symm
      _ ≤ ∑ k ∈ Finset.range (q + 2), g u c k :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun k _ _ => hgnn u c k)
      _ = blockCount (cellSet (u ++ c.1) c.2) (q + 2) x := by
          rw [blockCount_apply]
  rw [cellHitCount_eq_sum net w i q, ← hf, hsplit]
  linarith

end MapState

section Audit

#print axioms MapState.selIndic_mul_blockIndic_le
#print axioms MapState.cellHitCount_le_blockCounts

end Audit

end NormalNumbers.VandeheyS7
