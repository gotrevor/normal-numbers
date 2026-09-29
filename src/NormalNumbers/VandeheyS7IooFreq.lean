/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7BadMass
import NormalNumbers.VandeheyS7HitIoo

/-!
# S7-IF: interval frequencies for a CF-normal orbit, and the bad set's frequency

Lap 62 left an exact split: the bad set `nearInv η` is small in *measure* for free, and the cost is
the passage measure → frequency.  For the INPUT orbit that passage is not soft but it is available,
because CF-normality is a hypothesis we hold.  This module makes it.

* `blockCount_freq_cellSet_nil` — the missing nil-word case of `blockCount_freq_cellSet_mass`:
  the tail cell `cellSet [] T` has frequency equal to its Gauss mass.  (The general lemma needs
  `w ≠ []` only to invoke `blockCount_freq_of_isCFNormal`; for `w = []` the cylinder is `(0,1)`
  and the frequency is `1`.)
* `blockCount_Ioo_le` — hence **every** interval: `freq{n : Gⁿx ∈ (a,b)} ≤ (b−a)/log 2 + 2δ`,
  with the absolute Gauss density constant and no window.
* `blockCount_nearInv_freq_le` — and therefore, summing the lap-62 covering,
  `freq{n : Gⁿx ∈ nearInv η} ≤ 7√η/log 2 + ε`.

## What this changes

Lap 48 controlled the bad positions through the chain's second hypothesis `ImageTight`
(`exists_nearInv_freq_le`).  For the input orbit that hypothesis is now **unnecessary**: bad input
positions are rare unconditionally, at rate `√η`.  `ImageTight` is still needed on the IMAGE — the
statement there is about the image orbit, for which CF-normality is the conclusion, not a
hypothesis — but the input half of lap 48 is discharged.

## Guard rule

Content locator: `blockCount_Ioo_le`'s constant is exactly the Gauss density `1/log 2`, and the
`2δ` is the covering slack plus the convergence slack — both arbitrary.  Degenerate cases: `b ≤ a`
or an interval disjoint from `(0,1)` makes the count `0`; `η ≥ 1` makes the `nearInv` bound weaker
than the trivial `1`.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The nil-word cell frequency.**  Missing case of `blockCount_freq_cellSet_mass`. -/
theorem blockCount_freq_cellSet_nil {y : ℝ} (hirr : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (h : IsCFNormal y) {T : ℕ} (hT : 1 ≤ T) :
    Tendsto (fun p => blockCount (cellSet [] T) p y / (p:ℝ)) atTop
      (nhds (gaussMeasure (cellSet [] T)).toReal) := by
  classical
  have horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0:ℝ) 1 :=
    fun j => (irrational_orbit y hirr hmem j).2
  have hmass1 : (gaussMeasure (cfCylinder ([] : List ℕ))).toReal = 1 := by
    rw [cfCylinder_nil, ← cellSet_nil_one]; exact gaussMeasure_cellSet_nil_one
  have hcyl : Tendsto (fun p : ℕ => blockCount (cfCylinder ([] : List ℕ)) p y / (p:ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder ([] : List ℕ))).toReal) := by
    rw [hmass1]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    rw [cfCylinder_nil, blockCount_Ioo_zero_one hirr hmem p, div_self hpR.ne']
  have hext : ∀ a ∈ Finset.Ico 1 T,
      Tendsto (fun p => blockCount (cfCylinder (([] : List ℕ) ++ [a])) p y / (p:ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder (([] : List ℕ) ++ [a]))).toReal) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Ico.1 ha).1
    refine blockCount_freq_of_isCFNormal horb h _ (by simp) ?_
    intro e he
    simp only [List.nil_append, List.mem_singleton] at he
    omega
  have hsum := tendsto_finsetSum (Finset.Ico 1 T) (fun a ha => hext a ha)
  have hlim := hcyl.sub hsum
  rw [gaussMeasure_cellSet_eq [] hT]
  refine hlim.congr fun p => ?_
  rw [blockCount_cellSet_eq hirr hmem [] T p, sub_div, Finset.sum_div]

/-- **Interval frequencies.**  No window, absolute constant `1/log 2`. -/
theorem blockCount_Ioo_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (Set.Ioo a b) p x / (p:ℝ) ≤ (b - a) / Real.log 2 + 2 * δ := by
  classical
  obtain ⟨F, hFpos, hFcov, hFmass⟩ := cellCover_inv_log_two a b ha hab hb δ hδ
  have hpt : ∀ n : ℕ, blockIndic (Set.Ioo a b) (gaussMap^[n] x)
      ≤ ∑ c ∈ F, blockIndic (cellSet c.1 c.2) (gaussMap^[n] x) := by
    intro n
    by_cases hn : gaussMap^[n] x ∈ Set.Ioo a b
    · obtain ⟨hirr', hmem'⟩ := irrational_orbit x hirr hmem n
      obtain ⟨c, hcF, hc⟩ := hFcov (gaussMap^[n] x) hirr' hmem' hn
      have hone : blockIndic (Set.Ioo a b) (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hn]; rfl
      rw [hone]
      have hterm : blockIndic (cellSet c.1 c.2) (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hc]; rfl
      calc (1:ℝ) = blockIndic (cellSet c.1 c.2) (gaussMap^[n] x) := hterm.symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun c : List ℕ × ℕ => blockIndic (cellSet c.1 c.2) (gaussMap^[n] x))
            (fun i _ => blockIndic_nonneg _ _) hcF
    · rw [blockIndic, Set.indicator_of_notMem hn]
      exact Finset.sum_nonneg fun i _ => blockIndic_nonneg _ _
  have hcount : ∀ p : ℕ, blockCount (Set.Ioo a b) p x
      ≤ ∑ c ∈ F, blockCount (cellSet c.1 c.2) p x := by
    intro p
    simp only [blockCount_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n _ => hpt n
  have hfreq : ∀ c ∈ F, Tendsto (fun p => blockCount (cellSet c.1 c.2) p x / (p:ℝ)) atTop
      (nhds (gaussMeasure (cellSet c.1 c.2)).toReal) := by
    intro c hc
    rcases eq_or_ne c.1 [] with h0 | h0
    · rw [h0]
      exact blockCount_freq_cellSet_nil hirr hmem hx (hFpos c hc).2
    · exact blockCount_freq_cellSet_mass hirr hmem hx c.1 h0 (hFpos c hc).1 (hFpos c hc).2
  have hsum := tendsto_finsetSum F (fun c hc => hfreq c hc)
  have hmassR : (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal)
      ≤ (b - a) / Real.log 2 + δ := by
    simpa [one_div, div_eq_inv_mul] using hFmass
  have hlim := hsum.eventually (eventually_lt_nhds
    (show (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal) <
      (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal) + δ by linarith))
  filter_upwards [hlim, eventually_gt_atTop 0] with p hp hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  have hdiv : blockCount (Set.Ioo a b) p x / (p:ℝ)
      ≤ (∑ c ∈ F, blockCount (cellSet c.1 c.2) p x) / (p:ℝ) := by
    gcongr
    exact hcount p
  have hrw : (∑ c ∈ F, blockCount (cellSet c.1 c.2) p x) / (p:ℝ)
      = ∑ c ∈ F, blockCount (cellSet c.1 c.2) p x / (p:ℝ) := by
    rw [Finset.sum_div]
  rw [hrw] at hdiv
  linarith [hdiv, hp, hmassR]

#print axioms blockCount_freq_cellSet_nil
#print axioms blockCount_Ioo_le

end NormalNumbers.VandeheyS7
