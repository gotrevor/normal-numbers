/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-T2: CF-normality gives tightness (and does NOT give a Lévy bound)

Lap 44 reduced the §7 chain's second hypothesis to `ImageTight` — "for every `ε` there is a
threshold `T` whose digit frequency in the image is eventually `≤ ε`".  This module proves the
matching *input-side* statement, which is exactly the shape the clock argument will need:

    `imageTight_of_isCFNormal : IsCFNormal y → ImageTight y`   (for `y` irrational in `(0,1)`).

Two ingredients, both elementary:

* **The partition.**  At each orbit time the digit is either `≥ T` or equals exactly one
  `a ∈ [1, T)`, so `blockCount (cellSet [] T) p y + ∑_{a < T} blockCount (I_{[a]}) p y = p`
  (`blockCount_cellSet_nil_add_eq`).  CF-normality pins each cylinder frequency, hence the tail
  frequency's limit is `1 − ∑_{a < T} γ(I_{[a]})`.
* **The masses exhaust `(0,1)`.**  Every `t ∈ (0,1)` lies in `I_{[cfDigit t 0]}`, and a digit
  `> n` forces `t ≤ 1/n`, so `Ioo 0 1 ⊆ (⋃_{a ≤ n} I_{[a]}) ∪ Ioo 0 (2/n)` and therefore
  `1 ≤ ∑_{a ≤ n} γ(I_{[a]}) + (2/n)/log 2` (`one_le_sum_gaussMeasure_cfCylinder_singleton`).
  No null-set argument is needed: the covering is exact, rationals included.

**Why tightness and not Lévy.**  `LevyBound` would need `∑ log(aᵢ+1) = O(p)`, which is a uniform
integrability statement; CF-normality gives only the *pointwise-in-`T`* frequencies, and those
are compatible with a sparse sequence of enormous digits that moves no cell frequency at all
while blowing up `∑ log aᵢ`.  Tightness is precisely the part of Lévy that normality does
supply — which is why lap 44's weakening of the hypothesis was the right move.
-/
import NormalNumbers.VandeheyS7Reduce
import NormalNumbers.CFOrbitFreq

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- CF-normality in orbit-count form: the converse of `isCFNormal_of_orbit_freq`, by the same
`≤ |v|` window↔orbit gap. -/
theorem blockCount_freq_of_isCFNormal {y : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1) (h : IsCFNormal y)
    (v : List ℕ) (hne : v ≠ []) (hpos : ∀ a ∈ v, 1 ≤ a) :
    Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder v)).toReal) := by
  set A : ℕ → ℕ := fun p => countOccurrences v ((List.range p).map (cfDigit y)) with hA
  have hbnds : ∀ p, (A p : ℝ) ≤ blockCount (cfCylinder v) p y ∧
      blockCount (cfCylinder v) p y ≤ (A p : ℝ) + v.length := by
    intro p
    have hb := blockCount_sub_countOccurrences_bounds horb v hne 0 p
    simp only [Function.iterate_zero_apply, Nat.zero_add] at hb
    exact hb
  have hAfreq : Tendsto (fun p => (A p : ℝ) / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder v)).toReal) := h v hne hpos
  have hzero : Tendsto (fun p : ℕ => (v.length : ℝ) / (p : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hup : Tendsto (fun p => (A p : ℝ) / (p : ℝ) + (v.length : ℝ) / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder v)).toReal) := by simpa using hAfreq.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hAfreq hup ?_ ?_
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
      dsimp only
      gcongr
      exact (hbnds p).1
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    · have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
      dsimp only
      rw [← add_div]
      gcongr
      exact (hbnds p).2

/-- **The partition of the orbit clock.**  At each time the digit is `≥ T` or equals exactly one
`a ∈ [1, T)`. -/
theorem blockCount_cellSet_nil_add_eq {y : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1) {T : ℕ} (hT : 1 ≤ T) (p : ℕ) :
    blockCount (cellSet [] T) p y
        + ∑ a ∈ Finset.Icc 1 (T - 1), blockCount (cfCylinder [a]) p y = (p : ℝ) := by
  classical
  have hpt : ∀ k : ℕ, blockIndic (cellSet [] T) (gaussMap^[k] y)
      + ∑ a ∈ Finset.Icc 1 (T - 1), blockIndic (cfCylinder [a]) (gaussMap^[k] y) = 1 := by
    intro k
    set z := gaussMap^[k] y with hz
    have hz01 := horb k
    have hd1 : 1 ≤ cfDigit z 0 := by
      rw [cfDigit_zero]
      have : (1:ℝ) < z⁻¹ := by
        rw [lt_inv_comm₀ (by norm_num) hz01.1]; simpa using hz01.2
      exact Nat.one_le_iff_ne_zero.2 (by
        intro h0
        rw [Nat.floor_eq_zero] at h0
        linarith)
    by_cases hbig : T ≤ cfDigit z 0
    · have hmemc : z ∈ cellSet [] T :=
        ⟨by rw [cfCylinder_nil]; exact hz01, by simpa using hbig⟩
      have h1 : blockIndic (cellSet [] T) z = 1 := by
        rw [blockIndic, Set.indicator_of_mem hmemc]; simp
      have h2 : ∀ a ∈ Finset.Icc 1 (T - 1), blockIndic (cfCylinder [a]) z = 0 := by
        intro a ha
        obtain ⟨-, ha2⟩ := Finset.mem_Icc.1 ha
        refine (Set.indicator_of_notMem ?_ _)
        intro hmem
        have := (mem_cfCylinder_singleton.1 hmem).2
        omega
      rw [h1, Finset.sum_eq_zero h2]; ring
    · push_neg at hbig
      have hmem0 : z ∈ cfCylinder [cfDigit z 0] := mem_cfCylinder_singleton.2 ⟨hz01, rfl⟩
      have hin : cfDigit z 0 ∈ Finset.Icc 1 (T - 1) := Finset.mem_Icc.2 ⟨hd1, by omega⟩
      have h1 : blockIndic (cellSet [] T) z = 0 := by
        refine Set.indicator_of_notMem ?_ _
        intro hc
        have : T ≤ cfDigit z 0 := by simpa using hc.2
        omega
      have h2 : ∑ a ∈ Finset.Icc 1 (T - 1), blockIndic (cfCylinder [a]) z = 1 := by
        rw [Finset.sum_eq_single_of_mem (cfDigit z 0) hin ?_]
        · rw [blockIndic, Set.indicator_of_mem hmem0]; simp
        · intro b hb hbne
          refine Set.indicator_of_notMem ?_ _
          intro hc
          exact hbne ((mem_cfCylinder_singleton.1 hc).2).symm
      rw [h1, h2]; ring
  calc blockCount (cellSet [] T) p y
        + ∑ a ∈ Finset.Icc 1 (T - 1), blockCount (cfCylinder [a]) p y
      = ∑ k ∈ Finset.range p, (blockIndic (cellSet [] T) (gaussMap^[k] y)
          + ∑ a ∈ Finset.Icc 1 (T - 1), blockIndic (cfCylinder [a]) (gaussMap^[k] y)) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        rfl
    _ = (p : ℝ) := by rw [Finset.sum_congr rfl fun k _ => hpt k]; simp

/-- **The single-digit cylinders exhaust `(0,1)`.**  Every `t ∈ (0,1)` lies in
`I_{[cfDigit t 0]}`, and a digit exceeding `n` forces `t ≤ 1/n`. -/
theorem one_le_sum_gaussMeasure_cfCylinder_singleton {n : ℕ} (hn : 1 ≤ n) :
    (1:ℝ) ≤ (∑ a ∈ Finset.Icc 1 n, (gaussMeasure (cfCylinder [a])).toReal)
      + (2 / n) / Real.log 2 := by
  classical
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hcover : Set.Ioo (0:ℝ) 1 ⊆
      (⋃ a ∈ Finset.Icc 1 n, cfCylinder [a]) ∪ Set.Ioo (0:ℝ) (2 / n) := by
    intro t ht
    have hd1 : 1 ≤ cfDigit t 0 := by
      rw [cfDigit_zero]
      have h1 : (1:ℝ) < t⁻¹ := by
        rw [lt_inv_comm₀ (by norm_num) ht.1]; simpa using ht.2
      exact Nat.one_le_iff_ne_zero.2 (by
        intro h0
        rw [Nat.floor_eq_zero] at h0
        linarith)
    by_cases hle : cfDigit t 0 ≤ n
    · exact Or.inl (Set.mem_biUnion (Finset.mem_Icc.2 ⟨hd1, hle⟩)
        (mem_cfCylinder_singleton.2 ⟨ht, rfl⟩))
    · push_neg at hle
      refine Or.inr ⟨ht.1, ?_⟩
      have hle' := ((cfDigit_zero_eq_iff ht hd1).1 rfl).2
      have hnlt : (n:ℝ) < (cfDigit t 0 : ℝ) := by exact_mod_cast hle
      have : (1:ℝ) / (cfDigit t 0 : ℝ) < 2 / n := by
        rw [div_lt_div_iff₀ (by linarith) hnR]
        linarith
      linarith
  have hdisj : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint (fun a => cfCylinder [a]) := by
    intro a _ b _ hne
    exact cfCylinder_disjoint_of_length_eq rfl (by simpa using hne)
  have hun : gaussMeasure (⋃ a ∈ Finset.Icc 1 n, cfCylinder [a])
      = ∑ a ∈ Finset.Icc 1 n, gaussMeasure (cfCylinder [a]) :=
    measure_biUnion_finset hdisj (fun a _ => measurableSet_cfCylinder _)
  have hmono : gaussMeasure (Set.Ioo (0:ℝ) 1)
      ≤ (∑ a ∈ Finset.Icc 1 n, gaussMeasure (cfCylinder [a]))
        + gaussMeasure (Set.Ioo (0:ℝ) (2 / n)) := by
    refine le_trans (measure_mono hcover) ?_
    exact le_trans (measure_union_le _ _) (by rw [hun])
  have hone : (gaussMeasure (Set.Ioo (0:ℝ) 1)).toReal = 1 := by
    rw [← cellSet_nil_one]; exact gaussMeasure_cellSet_nil_one
  have hfin1 : (∑ a ∈ Finset.Icc 1 n, gaussMeasure (cfCylinder [a])) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun a _ => measure_ne_top _ _)
  have htoReal := ENNReal.toReal_mono
    (by exact ENNReal.add_ne_top.2 ⟨hfin1, measure_ne_top _ _⟩) hmono
  rw [hone, ENNReal.toReal_add hfin1 (measure_ne_top _ _),
    ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)] at htoReal
  have htail : (gaussMeasure (Set.Ioo (0:ℝ) (2 / n))).toReal ≤ (2 / n) / Real.log 2 := by
    rcases le_or_gt (2 / (n:ℝ)) 1 with h | h
    · simpa using gaussMeasure_Ioo_toReal_le (u := 0) (v := 2 / n) le_rfl (by positivity) h
    · have h1 : (gaussMeasure (Set.Ioo (0:ℝ) (2 / n))).toReal ≤ 1 := by
        have hsub := measure_mono (μ := gaussMeasure)
          (Set.subset_univ (Set.Ioo (0:ℝ) (2 / (n:ℝ))))
        rw [measure_univ] at hsub
        exact ENNReal.toReal_mono (by simp) hsub
      have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have : (1:ℝ) ≤ (2/(n:ℝ)) / Real.log 2 := by
        rw [le_div_iff₀ hlog]
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        linarith
      linarith
  linarith

/-- **CF-normality gives tightness.**  This is the input-side form of the §7 chain's second
hypothesis. -/
theorem imageTight_of_isCFNormal {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (h : IsCFNormal y) : ImageTight y := by
  classical
  have horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0:ℝ) 1 :=
    fun j => (irrational_orbit y hy hmem j).2
  intro ε hε
  -- choose `n` with the covering deficiency below `ε/2`
  obtain ⟨n, hn1, hnε⟩ : ∃ n : ℕ, 1 ≤ n ∧ (2 / (n:ℝ)) / Real.log 2 < ε / 2 := by
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨n, hn⟩ := exists_nat_gt (max (4 / (ε * Real.log 2)) 1)
    have hn1 : (1:ℝ) < (n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    refine ⟨n, by exact_mod_cast hn1.le, ?_⟩
    have h1 : 4 / (ε * Real.log 2) < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨n + 1, by omega, ?_⟩
  -- the tail frequency's limit is the covering deficiency
  have hlim : Tendsto (fun p : ℕ => blockCount (cellSet [] (n+1)) p y / (p:ℝ)) atTop
      (nhds (1 - ∑ a ∈ Finset.Icc 1 n, (gaussMeasure (cfCylinder [a])).toReal)) := by
    have hcyl : Tendsto (fun p : ℕ =>
        ∑ a ∈ Finset.Icc 1 n, blockCount (cfCylinder [a]) p y / (p:ℝ)) atTop
        (nhds (∑ a ∈ Finset.Icc 1 n, (gaussMeasure (cfCylinder [a])).toReal)) := by
      refine tendsto_finset_sum _ fun a ha => ?_
      refine blockCount_freq_of_isCFNormal horb h [a] (by simp) ?_
      intro b hb
      have hb' : b = a := by simpa using hb
      rw [hb']
      exact (Finset.mem_Icc.1 ha).1
    have hone : Tendsto (fun p : ℕ => (p:ℝ)/(p:ℝ)) atTop (nhds 1) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop 0] with p hp
      have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
      rw [div_self this.ne']
    have := hone.sub hcyl
    refine Tendsto.congr' ?_ this
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have heq := blockCount_cellSet_nil_add_eq horb (T := n+1) (by omega) p
    rw [show n + 1 - 1 = n from rfl] at heq
    field_simp
    rw [← Finset.sum_div] at *
    field_simp at *
    linarith [heq]
  have hdef : 1 - ∑ a ∈ Finset.Icc 1 n, (gaussMeasure (cfCylinder [a])).toReal < ε / 2 :=
    by linarith [one_le_sum_gaussMeasure_cfCylinder_singleton hn1, hnε]
  have hlt : 1 - ∑ a ∈ Finset.Icc 1 n, (gaussMeasure (cfCylinder [a])).toReal < ε := by linarith
  have := hlim.eventually (eventually_lt_nhds hlt)
  filter_upwards [this] with p hp
  linarith

section Audit

#print axioms blockCount_cellSet_nil_add_eq
#print axioms one_le_sum_gaussMeasure_cfCylinder_singleton
#print axioms imageTight_of_isCFNormal

end Audit

end NormalNumbers.VandeheyS7
