/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CT: the two frequencies, and `ClassFreqBoundSlack` from `CellMemory`

S7-CM sandwiched both sides of the per-cell bound between Birkhoff counts of FIXED cells; S7-CR
turned a pair of frequencies plus a mass comparison into the bound.  This module computes the
frequencies and the mass comparison, closing the memory route down to `CellMemory` itself.

* `blockCount_le_add`, `blockCount_mono`, `tendsto_blockCount_shift` — an index shift by a bounded
  amount does not change a visit frequency (the counts differ by at most the shift).
* `tendsto_cellCounts` / `tendsto_cylCounts` — the two limits, from CF-normality
  (`blockCount_freq_cellSet_of_isCFNormal`, `blockCount_freq_of_isCFNormal`) plus
  `gaussMeasure_cellSet_eq`.
* `classFreqSlack_of_cellMemory` — **the payoff**: with `CellMemory`'s selector words and any cell
  cover `F` of the cluster set, the per-cell bound holds with
  `B = (1 + 8 log 2)·Σ_{c ∈ F} γ(cellSet c)` and slack `L`.  The selector mass cancels — that is
  the whole point of the quasi-Bernoulli bound — so `B` does not depend on the cell, on `L`, or on
  how many cells the net has.
-/
import NormalNumbers.VandeheyS7CellRatio
import NormalNumbers.VandeheyS7FrontSlack
import NormalNumbers.VandeheyS7HitCell
import NormalNumbers.VandeheyS7Tight2
import NormalNumbers.CFScheduleA

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

/-! ## Shifting the index -/

lemma blockCount_mono (A : Set ℝ) (x : ℝ) {n m : ℕ} (h : n ≤ m) :
    blockCount A n x ≤ blockCount A m x := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) h)) ?_
  intro k _ _
  exact Set.indicator_nonneg (by intro _ _; norm_num) _

lemma blockCount_le_add (A : Set ℝ) (x : ℝ) (n k : ℕ) :
    blockCount A (n + k) x ≤ blockCount A n x + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb : blockIndic A (gaussMap^[n + k] x) ≤ 1 := by
      rw [blockIndic]
      by_cases h : gaussMap^[n + k] x ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    have hstep : blockCount A (n + k + 1) x = blockCount A (n + k) x
        + blockIndic A (gaussMap^[n + k] x) := by
      rw [blockCount_apply, blockCount_apply, Finset.sum_range_succ]
    have : n + (k + 1) = (n + k) + 1 := by ring
    rw [this, hstep]
    push_cast
    linarith

/-- The counts at two indices differing by at most `K` differ by at most `K`. -/
lemma abs_blockCount_sub_le (A : Set ℝ) (x : ℝ) {n m K : ℕ} (h1 : m ≤ n + K) (h2 : n ≤ m + K) :
    |blockCount A n x - blockCount A m x| ≤ (K : ℝ) := by
  rcases le_or_gt n m with h | h
  · have hup : blockCount A m x ≤ blockCount A n x + K :=
      le_trans (blockCount_mono A x h1) (blockCount_le_add A x n K)
    have hlo : blockCount A n x ≤ blockCount A m x := blockCount_mono A x h
    rw [abs_le]; constructor <;> linarith
  · have hup : blockCount A n x ≤ blockCount A m x + K :=
      le_trans (blockCount_mono A x h2) (blockCount_le_add A x m K)
    have hlo : blockCount A m x ≤ blockCount A n x := blockCount_mono A x h.le
    rw [abs_le]; constructor <;> linarith

/-- **An index shift by a bounded amount preserves the frequency.** -/
theorem tendsto_blockCount_shift {A : Set ℝ} {x c : ℝ} {g : ℕ → ℕ} {K : ℕ}
    (h : Tendsto (fun p : ℕ => blockCount A p x / p) atTop (nhds c))
    (h1 : ∀ p, g p ≤ p + K) (h2 : ∀ p, p ≤ g p + K) :
    Tendsto (fun p : ℕ => blockCount A (g p) x / p) atTop (nhds c) := by
  have hKz : Tendsto (fun p : ℕ => (K : ℝ) / p) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hd : Tendsto (fun p : ℕ => blockCount A (g p) x / p - blockCount A p x / p)
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hKz
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have habs := abs_blockCount_sub_le A x (n := g p) (m := p) (h2 p) (h1 p)
    rw [Real.norm_eq_abs, div_sub_div_same, abs_div, abs_of_pos hpR]
    exact div_le_div_of_nonneg_right habs hpR.le
  have := hd.add h
  simpa using this

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

/-- **The numerator's frequency.** -/
theorem tendsto_num (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hCF : IsCFNormal x) (U : Finset (List ℕ)) (F : Finset (List ℕ × ℕ))
    (hUlen : ∀ u ∈ U, u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a))
    (hF : ∀ c ∈ F, (∀ e ∈ c.1, 1 ≤ e) ∧ 1 ≤ c.2) :
    Tendsto (fun q : ℕ => (∑ u ∈ U, ∑ c ∈ F,
        blockCount (cellSet (u ++ c.1) c.2) (q + 2) x) / q) atTop
      (nhds (∑ u ∈ U, ∑ c ∈ F, (gaussMeasure (cellSet (u ++ c.1) c.2)).toReal)) := by
  classical
  have hterm : ∀ u ∈ U, ∀ c ∈ F,
      Tendsto (fun q : ℕ => blockCount (cellSet (u ++ c.1) c.2) (q + 2) x / q) atTop
        (nhds (gaussMeasure (cellSet (u ++ c.1) c.2)).toReal) := by
    intro u hu c hc
    have hne : (u ++ c.1) ≠ [] := by
      simp [(hUlen u hu).1]
    have hpos : ∀ a ∈ (u ++ c.1), 1 ≤ a := by
      intro a ha
      rcases List.mem_append.1 ha with h | h
      · exact (hUlen u hu).2 a h
      · exact (hF c hc).1 a h
    have h := blockCount_freq_cellSet_of_isCFNormal hx hmem hCF (u ++ c.1) hne hpos c.2
    rw [← gaussMeasure_cellSet_eq (u ++ c.1) (hF c hc).2] at h
    exact tendsto_blockCount_shift (K := 2) h (fun p => by omega) (fun p => by omega)
  have hdiv : ∀ q : ℕ, (∑ u ∈ U, ∑ c ∈ F,
      blockCount (cellSet (u ++ c.1) c.2) (q + 2) x) / q
      = ∑ u ∈ U, ∑ c ∈ F, blockCount (cellSet (u ++ c.1) c.2) (q + 2) x / q := by
    intro q
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_div _ _ _
  simp only [hdiv]
  exact tendsto_finsetSum _ (fun u hu => tendsto_finsetSum _ (fun c hc => hterm u hu c hc))

/-- **The denominator's frequency.** -/
theorem tendsto_den {L : ℕ} (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hCF : IsCFNormal x) (U : Finset (List ℕ)) (hL : 2 ≤ L)
    (hUlen : ∀ u ∈ U, u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a)) :
    Tendsto (fun q : ℕ => (∑ u ∈ U, blockCount (cfCylinder u) (q + 2 - L) x) / q) atTop
      (nhds (∑ u ∈ U, (gaussMeasure (cfCylinder u)).toReal)) := by
  classical
  have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1 :=
    fun j => (irrational_orbit x hx hmem j).2
  have hterm : ∀ u ∈ U,
      Tendsto (fun q : ℕ => blockCount (cfCylinder u) (q + 2 - L) x / q) atTop
        (nhds (gaussMeasure (cfCylinder u)).toReal) := by
    intro u hu
    have h := blockCount_freq_of_isCFNormal horb hCF u (hUlen u hu).1 (hUlen u hu).2
    exact tendsto_blockCount_shift (K := L) h (fun p => by omega) (fun p => by omega)
  have hdiv : ∀ q : ℕ, (∑ u ∈ U, blockCount (cfCylinder u) (q + 2 - L) x) / q
      = ∑ u ∈ U, blockCount (cfCylinder u) (q + 2 - L) x / q := fun q => Finset.sum_div _ _ _
  simp only [hdiv]
  exact tendsto_finsetSum _ hterm

open Classical in
/-- **S7-CT, the payoff.**  `CellMemory`'s selector words plus any cell cover of the cluster set
give the per-cell bound with constant `B = (1 + 8 log 2)·Σ_{c ∈ F} γ(cellSet c)` and slack `L`.
The selector mass cancels, so `B` is free of the cell, of `L`, and of the number of cells. -/
theorem classFreqSlack_of_cellMemory {net : StateNet Φ x η ρ M} {L : ℕ}
    {U : Fin M → Finset (List ℕ)} {F : Finset (List ℕ × ℕ)} {B : ℝ} (w : List ℕ)
    (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1) (hCFn : IsCFNormal x) (hL : 2 ≤ L)
    (hUlen : ∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a))
    (hUsel : ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0)
    (hUne : ∀ i : Fin M, (U i).Nonempty)
    (hF : ∀ c ∈ F, (∀ e ∈ c.1, 1 ≤ e) ∧ 1 ≤ c.2)
    (hcov : ∀ i : Fin M, ∀ z : ℝ, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 →
      z ∈ clusterSet (net.cen i) w (4 * ρ / Real.sqrt (|Φ.det| / 6)) →
      ∃ c ∈ F, z ∈ cellSet c.1 c.2)
    (hB : (1 + 8 * Real.log 2) * ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal ≤ B) :
    ClassFreqBoundSlack net w B := by
  classical
  intro ε hε i
  refine ⟨(L:ℝ), by positivity, ?_⟩
  -- the words of `U i` are genuine
  have hUne' : ∀ u ∈ U i, u ≠ [] ∧ (∀ a ∈ u, 1 ≤ a) := by
    intro u hu
    obtain ⟨hlen, hpos⟩ := hUlen i u hu
    exact ⟨by intro h; rw [h] at hlen; simp at hlen; omega, hpos⟩
  set N : ℕ → ℝ := fun q => ∑ u ∈ U i, ∑ c ∈ F,
    blockCount (cellSet (u ++ c.1) c.2) (q + 2) x with hN
  set D : ℕ → ℝ := fun q => ∑ u ∈ U i, blockCount (cfCylinder u) (q + 2 - L) x with hD
  set nm : ℝ := ∑ u ∈ U i, ∑ c ∈ F, (gaussMeasure (cellSet (u ++ c.1) c.2)).toReal with hnm
  set dm : ℝ := ∑ u ∈ U i, (gaussMeasure (cfCylinder u)).toReal with hdm
  have hNlim := tendsto_num hx hmem hCFn (U i) F hUne' hF
  have hDlim := tendsto_den hx hmem hCFn (U i) hL hUne'
  have hdmpos : 0 < dm := by
    obtain ⟨u₀, hu₀⟩ := hUne i
    have hpos : ∀ u ∈ U i, 0 < (gaussMeasure (cfCylinder u)).toReal := by
      intro u hu
      exact gaussMeasure_cfCylinder_toReal_pos u (hUne' u hu).1 (hUne' u hu).2
    rw [hdm]
    exact Finset.sum_pos hpos ⟨u₀, hu₀⟩
  -- the mass comparison: the selector mass cancels
  have hcellnn : ∀ c ∈ F, 0 ≤ (gaussMeasure (cellSet c.1 c.2)).toReal := by
    intro c _; positivity
  have hmass : nm ≤ B * dm := by
    set Cq : ℝ := 1 + 8 * Real.log 2 with hCq
    set S : ℝ := ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal with hS
    have h1 : nm ≤ ∑ u ∈ U i, ∑ c ∈ F, Cq * ((gaussMeasure (cfCylinder u)).toReal
        * (gaussMeasure (cellSet c.1 c.2)).toReal) := by
      rw [hnm]
      refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun c _ => ?_
      exact gaussMeasure_cellSet_append_le u c.1 (hUne' u hu).2 c.2
    have hinner : ∀ u : List ℕ, ∑ c ∈ F, Cq * ((gaussMeasure (cfCylinder u)).toReal
        * (gaussMeasure (cellSet c.1 c.2)).toReal)
        = (Cq * (gaussMeasure (cfCylinder u)).toReal) * S := by
      intro u
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    have h2 : ∑ u ∈ U i, ∑ c ∈ F, Cq * ((gaussMeasure (cfCylinder u)).toReal
        * (gaussMeasure (cellSet c.1 c.2)).toReal) = Cq * dm * S := by
      rw [Finset.sum_congr rfl (fun u _ => hinner u), ← Finset.sum_mul, ← Finset.mul_sum, hdm]
    have hstep : nm ≤ Cq * dm * S := by rw [← h2]; exact h1
    have hdmnn : 0 ≤ dm := hdmpos.le
    have hfin : Cq * dm * S ≤ B * dm := by
      have h := mul_le_mul_of_nonneg_right hB hdmnn
      nlinarith [h]
    linarith
  have hB0 : 0 ≤ B := by
    have hsum : 0 ≤ ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal :=
      Finset.sum_nonneg hcellnn
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hB]
  -- the two sandwiches
  have hnum : ∀ᶠ q in atTop, cellHitCount net w i q ≤ (L:ℝ) + N q := by
    filter_upwards with q
    exact cellHitCount_le_blockCounts hx hmem w hUlen hUsel i (hcov i) q
  have hden : ∀ᶠ q in atTop, D q ≤ cellCount net i q := by
    filter_upwards [eventually_ge_atTop L] with q hq
    exact cellCount_ge_blockCounts hUlen hUsel i hL hq
  exact classFreqSlack_of_limits i hnum hden hNlim hDlim hdmpos hB0 hmass hε

end MapState

section Audit

#print axioms tendsto_blockCount_shift
#print axioms MapState.tendsto_num
#print axioms MapState.tendsto_den
#print axioms MapState.classFreqSlack_of_cellMemory

end Audit

end NormalNumbers.VandeheyS7
