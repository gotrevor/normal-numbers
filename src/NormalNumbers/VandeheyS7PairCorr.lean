/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-PC: the Gauss system's pair correlations, and the digit tail along a CF-normal orbit

S7-NR located route A's remaining content in the LOCALITY of the crux: the run's window statistics
must track the input's window by window, not merely on average.  Both halves of that comparison are
window averages at a fixed scale `T`, so what the attack needs is a concentration estimate for
window averages — and for the INPUT side that is a statement about the Gauss system alone.

This module lands the two measure-theoretic inputs of that estimate.

* `abs_gaussMeasure_pair_sub_sq_le` — **pair correlations decay geometrically**: for a genuine word
  `w` and a gap `g ≥ |w|`,

      |γ(I_w ∩ G^{-g} I_w) − γ(I_w)²| ≤ 4 · (9/10)^{g − |w|},

  a one-line consequence of `gaussMeasure_cylinder_mixing` (S7-MX) with the cylinder itself as the
  far set.  This is the `Σ_{i,j} Cov` input of a variance bound at scale `T`: the off-diagonal
  covariances are summable, so the variance of a window average is `O(1/T)`.
* `exists_digitTail_freq_le` — **the digit tail has small frequency**: for a CF-normal `y` and every
  `ε > 0` there is a digit bound `B` with

      #{m < p : cfDigit y m > B} ≤ ε · p   eventually.

  This is what lets a countable union of cylinders be replaced by a finite subfamily in an orbit
  frequency: the error is the frequency of a large digit somewhere in the window, and that is
  `|window| · (tail)`.

Together they are the two ingredients of the upper bound on the orbit's pair frequency (next step:
`limsup (1/p)·#{m<p : Gᵐy ∈ I_w ∧ G^{m+g}y ∈ I_w} ≤ γ(I_w ∩ G^{-g}I_w)`), hence of the variance
bound, hence — by Cauchy–Schwarz on the orbit — of the input half of the crux.

## Guard rule

**Content locator.**  The mixing bound is the only analytic input and it is cited from S7-MX, where
it is proved.  The tail lemma's content is that the single-digit cylinders of digit `≤ B` carry mass
`→ 1` (`exists_boundedWords_sum_gt 1`), and that every orbit point of a genuine orbit lies in
exactly one of them.

**Degenerate cases.**  `g = |w|` gives the bound `4`, which is trivially true (both terms are in
`[0,1]`); the content starts at `g > |w|`.  `B = 0` makes the tail bound `1`, also trivial.
-/
import NormalNumbers.VandeheyS7WindowFreq
import NormalNumbers.CFGammaMixing
import NormalNumbers.VandeheyOutputFreq
import NormalNumbers.VandeheyS7IntervalFreq

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers Finset

/-! ## Pair correlations of a cylinder -/

/-- **Geometric decay of the pair correlation of a cylinder.**  The gap is measured from the end of
the word: with `g = |w| + h` the bound is `4·(9/10)^h`. -/
theorem abs_gaussMeasure_pair_sub_sq_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) (h : ℕ) :
    |(gaussMeasure (cfCylinder w ∩ (gaussMap^[w.length + h]) ⁻¹' cfCylinder w)).toReal
        - (gaussMeasure (cfCylinder w)).toReal ^ 2|
      ≤ 4 * (9 / 10 : ℝ) ^ h := by
  have hsub : cfCylinder w ⊆ Set.Ioo (0:ℝ) 1 := fun t ht => ht.1
  have hmix := gaussMeasure_cylinder_mixing w hpos h (measurableSet_cfCylinder w) hsub
  have hvol : (volume (cfCylinder w)).toReal ≤ 1 := by
    have hle : volume (cfCylinder w) ≤ volume (Set.Ioo (0:ℝ) 1) := measure_mono hsub
    have h1 : volume (Set.Ioo (0:ℝ) 1) = 1 := by simp
    have hb : volume (cfCylinder w) ≤ 1 := by rw [← h1]; exact hle
    simpa using ENNReal.toReal_mono (by simp) hb
  have hvol0 : (0:ℝ) ≤ (volume (cfCylinder w)).toReal := ENNReal.toReal_nonneg
  have hγ1 : (gaussMeasure (cfCylinder w)).toReal ≤ 1 := by
    have hb : gaussMeasure (cfCylinder w) ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq gaussMeasure_univ)
    simpa using ENNReal.toReal_mono (by simp) hb
  have hγ0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder w)).toReal := ENNReal.toReal_nonneg
  have hpow : (0:ℝ) ≤ (9 / 10 : ℝ) ^ h := by positivity
  have hsq : (gaussMeasure (cfCylinder w)).toReal * (gaussMeasure (cfCylinder w)).toReal
      = (gaussMeasure (cfCylinder w)).toReal ^ 2 := by ring
  rw [hsq] at hmix
  refine hmix.trans ?_
  have hmul : (4 * (volume (cfCylinder w)).toReal) * (gaussMeasure (cfCylinder w)).toReal ≤ 4 := by
    nlinarith
  calc (9 / 10 : ℝ) ^ h * (4 * (volume (cfCylinder w)).toReal)
        * (gaussMeasure (cfCylinder w)).toReal
      = (9 / 10 : ℝ) ^ h * ((4 * (volume (cfCylinder w)).toReal)
          * (gaussMeasure (cfCylinder w)).toReal) := by ring
    _ ≤ (9 / 10 : ℝ) ^ h * 4 := by
        exact mul_le_mul_of_nonneg_left hmul hpow
    _ = 4 * (9 / 10 : ℝ) ^ h := by ring

/-! ## The digit tail along a CF-normal orbit -/

/-- The single-digit cylinders of digit at most `B`. -/
noncomputable def smallDigits (B : ℕ) : Finset (List ℕ) := boundedWords B 1

lemma mem_smallDigits {B : ℕ} {v : List ℕ} :
    v ∈ smallDigits B ↔ v.length = 1 ∧ ∀ a ∈ v, 1 ≤ a ∧ a ≤ B := by
  rw [smallDigits, mem_boundedWords]

/-- A genuine orbit point lies in the union of the small-digit cylinders exactly when its first
digit is at most `B`. -/
lemma mem_smallDigits_union_iff {y : ℝ} (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0:ℝ) 1)
    (m B : ℕ) :
    gaussMap^[m] y ∈ (⋃ v ∈ smallDigits B, cfCylinder v) ↔ cfDigit y m ≤ B := by
  classical
  have hone : 1 ≤ cfDigit y m := by
    have := horb m
    have h1 : (1:ℝ) < (gaussMap^[m] y)⁻¹ := by
      rw [lt_inv_comm₀ one_pos this.1]; simpa using this.2
    rw [cfDigit, Nat.le_floor_iff (by positivity)]
    exact_mod_cast h1.le
  have hd : cfDigit (gaussMap^[m] y) 0 = cfDigit y m := rfl
  constructor
  · intro hmem
    obtain ⟨v, hv, hmv⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hlen, hb⟩ := mem_smallDigits.1 hv
    obtain ⟨a, ha⟩ : ∃ a, v = [a] := by
      match v, hlen with
      | [a], _ => exact ⟨a, rfl⟩
    subst ha
    have hdig := hmv.2 0 (by simp)
    rw [hd] at hdig
    have := (hb a (by simp)).2
    simpa [hdig] using this
  · intro hle
    refine Set.mem_iUnion₂.2 ⟨[cfDigit y m], mem_smallDigits.2 ⟨by simp, ?_⟩, ?_⟩
    · intro a ha
      have : a = cfDigit y m := by simpa using ha
      subst this
      exact ⟨hone, hle⟩
    · refine ⟨horb m, fun i hi => ?_⟩
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      rw [hd]
      rfl

/-- **The digit tail has small frequency.**  For a CF-normal input, the times whose digit exceeds a
large bound have frequency at most `ε`. -/
theorem exists_digitTail_freq_le {y : ℝ} (hy : IsCFNormal y)
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ᶠ p : ℕ in atTop,
      (((range p).filter fun m => B < cfDigit y m).card : ℝ) ≤ ε * (p : ℝ) := by
  classical
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt 1 (show (0:ℝ) < ε / 2 by linarith)
  refine ⟨B, ?_⟩
  have hfreq : Tendsto (fun p => blockCount (⋃ v ∈ smallDigits B, cfCylinder v) p y / (p : ℝ))
      atTop (nhds (∑ v ∈ smallDigits B, (gaussMeasure (cfCylinder v)).toReal)) := by
    refine tendsto_windowFreq hy horb (K := 1) one_pos ?_ ?_
    · intro v hv; exact (mem_smallDigits.1 hv).1
    · intro v hv a ha; exact ((mem_smallDigits.1 hv).2 a ha).1
  have hev := hfreq.eventually (eventually_gt_nhds
    (show (∑ v ∈ smallDigits B, (gaussMeasure (cfCylinder v)).toReal) - ε / 2
      < ∑ v ∈ smallDigits B, (gaussMeasure (cfCylinder v)).toReal by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- the block count of the small-digit union counts exactly the times with small digit
  have hcount : blockCount (⋃ v ∈ smallDigits B, cfCylinder v) p y
      = (((range p).filter fun m => cfDigit y m ≤ B).card : ℝ) := by
    rw [blockCount_apply]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : cfDigit y m ≤ B
    · rw [blockIndic_eq_one' ((mem_smallDigits_union_iff horb m B).2 hm), if_pos hm]
    · rw [blockIndic_eq_zero' (fun hc => hm ((mem_smallDigits_union_iff horb m B).1 hc)),
        if_neg hm]
  rw [hcount] at hp
  -- the two filters partition `range p`
  have hsplit : (((range p).filter fun m => cfDigit y m ≤ B).card : ℝ)
      + (((range p).filter fun m => B < cfDigit y m).card : ℝ) = (p : ℝ) := by
    have hnot : ∀ m, ¬ (cfDigit y m ≤ B) ↔ B < cfDigit y m := by intro m; omega
    have := Finset.card_filter_add_card_filter_not
      (s := range p) (p := fun m => cfDigit y m ≤ B)
    rw [Finset.card_range] at this
    have heq : ((range p).filter fun m => ¬ (cfDigit y m ≤ B))
        = ((range p).filter fun m => B < cfDigit y m) := by
      refine Finset.filter_congr fun m _ => ?_
      constructor
      · intro h; omega
      · intro h; omega
    rw [heq] at this
    exact_mod_cast this
  have hmassle : (∑ v ∈ smallDigits B, (gaussMeasure (cfCylinder v)).toReal) ≤ 1 := by
    have hle : (⋃ v ∈ smallDigits B, cfCylinder v) ⊆ Set.Ioo (0:ℝ) 1 := by
      intro t ht
      obtain ⟨v, -, hv⟩ := Set.mem_iUnion₂.1 ht
      exact hv.1
    have hsum : gaussMeasure (⋃ v ∈ smallDigits B, cfCylinder v)
        = ∑ v ∈ smallDigits B, gaussMeasure (cfCylinder v) := by
      refine measure_biUnion_finset ?_ (fun v _ => measurableSet_cfCylinder v)
      intro u hu v hv hne
      exact cfCylinder_disjoint (by rw [(mem_smallDigits.1 hu).1, (mem_smallDigits.1 hv).1]) hne
    have hb : gaussMeasure (⋃ v ∈ smallDigits B, cfCylinder v) ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq gaussMeasure_univ)
    have htoReal : (∑ v ∈ smallDigits B, (gaussMeasure (cfCylinder v)).toReal)
        = (gaussMeasure (⋃ v ∈ smallDigits B, cfCylinder v)).toReal := by
      rw [hsum, ENNReal.toReal_sum]
      intro v _
      exact measure_ne_top _ _
    rw [htoReal]
    simpa using ENNReal.toReal_mono (by simp) hb
  rw [lt_div_iff₀ hpR] at hp
  have hsame : smallDigits B = boundedWords B 1 := rfl
  rw [hsame] at hp hmassle
  nlinarith [hB]

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.abs_gaussMeasure_pair_sub_sq_le
#print axioms NormalNumbers.VandeheyS7.exists_digitTail_freq_le

end Audit
