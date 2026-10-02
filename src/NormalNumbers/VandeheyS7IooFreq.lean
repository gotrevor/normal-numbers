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


/-- Orbit points lie in `(0,1)`, so a target may be clipped to `[0,1]` for free. -/
theorem blockCount_inter_Ioo {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (A : Set ℝ) (p : ℕ) :
    blockCount (A ∩ Set.Ioo (0:ℝ) 1) p x = blockCount A p x := by
  classical
  simp only [blockCount_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn := (irrational_orbit x hirr hmem n).2
  by_cases h : gaussMap^[n] x ∈ A
  · have hmem2 : gaussMap^[n] x ∈ A ∩ Set.Ioo (0:ℝ) 1 := ⟨h, hn⟩
    rw [blockIndic, Set.indicator_of_mem hmem2, blockIndic, Set.indicator_of_mem h]
  · rw [blockIndic, Set.indicator_of_notMem (fun hc => h hc.1), blockIndic,
      Set.indicator_of_notMem h]

/-- **Interval frequencies, unclipped.**  Any `a ≤ b` at all. -/
theorem blockCount_Ioo_le' {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {a b : ℝ} (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (Set.Ioo a b) p x / (p:ℝ) ≤ (b - a) / Real.log 2 + 2 * δ := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set a' := max 0 a with ha'
  set b' := min 1 b with hb'
  have hinter : Set.Ioo a b ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo a' b' := by
    rw [Set.Ioo_inter_Ioo]
    rw [show max a 0 = a' from max_comm a 0, show min b 1 = b' from min_comm b 1]
  have hcnt : ∀ p : ℕ, blockCount (Set.Ioo a b) p x = blockCount (Set.Ioo a' b') p x := by
    intro p
    rw [← hinter, blockCount_inter_Ioo hirr hmem]
  rcases le_or_gt a' b' with hle | hgt
  · have h := blockCount_Ioo_le hirr hmem hx (le_max_left _ _) hle (min_le_left _ _) hδ
    filter_upwards [h] with p hp
    rw [hcnt p]
    have hlen : b' - a' ≤ b - a := by
      have h1 : a ≤ a' := le_max_right _ _
      have h2 : b' ≤ b := min_le_right _ _
      linarith
    have : (b' - a') / Real.log 2 ≤ (b - a) / Real.log 2 := by gcongr
    linarith
  · have hempty : Set.Ioo a' b' = ∅ := Set.Ioo_eq_empty (by linarith)
    filter_upwards [eventually_gt_atTop 0] with p hp0
    rw [hcnt p, hempty]
    have : blockCount (∅ : Set ℝ) p x = 0 := by
      simp [blockCount_apply, blockIndic]
    rw [this]
    have hba : 0 ≤ (b - a) / Real.log 2 := by positivity
    have hpR : (0:ℝ) < p := by exact_mod_cast hp0
    rw [zero_div]
    linarith

/-- **The bad set is rare for the input orbit — unconditionally.**  No `ImageTight`. -/
theorem blockCount_nearInv_freq_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (nearInv η) p x / (p:ℝ) ≤ 7 * Real.sqrt η / Real.log 2 + ε := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set s := Real.sqrt η with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hη
  have hss : s * s = η := Real.mul_self_sqrt hη.le
  have hs1 : s ≤ 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hη1
  have hηs : η ≤ s := by nlinarith
  set K : ℕ := ⌈1 / s⌉₊ with hKdef
  have hKpos : 0 < K := by rw [hKdef, Nat.ceil_pos]; positivity
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKlow : 1 / s ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
  set lo : ℕ → ℝ := fun i => if i = 0 then -η else 1 / (i : ℝ) - η with hlo
  set hi : ℕ → ℝ := fun i => if i = 0 then 1 / (K : ℝ) + η else 1 / (i : ℝ) + η with hhi
  have hlolehi : ∀ i, lo i ≤ hi i := by
    intro i
    by_cases h : i = 0
    · simp only [hlo, hhi, h, if_pos rfl]
      have : (0:ℝ) < 1 / (K:ℝ) := by positivity
      linarith
    · simp only [hlo, hhi, if_neg h]
      linarith
  -- the covering
  have hcover : ∀ t : ℝ, t ∈ nearInv η → ∃ i ∈ Finset.range (K + 1), t ∈ Set.Ioo (lo i) (hi i) := by
    rintro t ⟨k, hk1, habs⟩
    have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
    have h1 := (abs_lt.1 habs).1
    have h2 := (abs_lt.1 habs).2
    rcases le_or_gt k K with hk | hk
    · refine ⟨k, Finset.mem_range.2 (by omega), ?_⟩
      have hkne : k ≠ 0 := by omega
      simp only [hlo, hhi, if_neg hkne]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨0, Finset.mem_range.2 (by omega), ?_⟩
      have hkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
      have hinv : 1 / (k : ℝ) ≤ 1 / (K : ℝ) := one_div_le_one_div_of_le hKR hkR
      have hpos : (0:ℝ) < 1 / (k : ℝ) := by positivity
      simp only [hlo, hhi, if_pos rfl]
      exact ⟨by linarith, by linarith⟩
  have hpt : ∀ n : ℕ, blockIndic (nearInv η) (gaussMap^[n] x)
      ≤ ∑ i ∈ Finset.range (K + 1), blockIndic (Set.Ioo (lo i) (hi i)) (gaussMap^[n] x) := by
    intro n
    by_cases hn : gaussMap^[n] x ∈ nearInv η
    · obtain ⟨i, hiF, hmem'⟩ := hcover _ hn
      have hone : blockIndic (nearInv η) (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hn]; rfl
      rw [hone]
      have hterm : blockIndic (Set.Ioo (lo i) (hi i)) (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hmem']; rfl
      calc (1:ℝ) = blockIndic (Set.Ioo (lo i) (hi i)) (gaussMap^[n] x) := hterm.symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun i => blockIndic (Set.Ioo (lo i) (hi i)) (gaussMap^[n] x))
            (fun j _ => blockIndic_nonneg _ _) hiF
    · rw [blockIndic, Set.indicator_of_notMem hn]
      exact Finset.sum_nonneg fun i _ => blockIndic_nonneg _ _
  have hcount : ∀ p : ℕ, blockCount (nearInv η) p x
      ≤ ∑ i ∈ Finset.range (K + 1), blockCount (Set.Ioo (lo i) (hi i)) p x := by
    intro p
    simp only [blockCount_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n _ => hpt n
  -- each piece
  set δ : ℝ := ε / (2 * ((K:ℝ) + 1)) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hpieces : ∀ᶠ p : ℕ in atTop, ∀ i ∈ Finset.range (K + 1),
      blockCount (Set.Ioo (lo i) (hi i)) p x / (p:ℝ) ≤ (hi i - lo i) / Real.log 2 + 2 * δ := by
    refine (eventually_all_finset (Finset.range (K+1))).2 fun i _ => ?_
    exact blockCount_Ioo_le' hirr hmem hx (hlolehi i) hδ0
  -- the total length
  have hlensum : ∑ i ∈ Finset.range (K + 1), (hi i - lo i)
      = 1 / (K:ℝ) + 2 * η + 2 * η * (K:ℝ) := by
    rw [Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range K, hi (i + 1) - lo (i + 1) = 2 * η := by
      intro i _
      have hne : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp only [hlo, hhi, if_neg hne]
      try ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
    simp only [hlo, hhi, if_pos rfl, nsmul_eq_mul]
    ring
  have hreal : 1 / (K : ℝ) + 2 * η + 2 * η * (K : ℝ) ≤ 7 * s := by
    have h1 : 1 / (K : ℝ) ≤ s := by
      rw [div_le_iff₀ hKR]
      have h := hKlow
      rw [div_le_iff₀ hs0] at h
      linarith
    have h2 : 2 * η * (K : ℝ) ≤ 2 * s + 2 * η := by
      have hKb : (K : ℝ) ≤ 1 / s + 1 := hKhigh.le
      have hstep : 2 * η * (K : ℝ) ≤ 2 * η * (1 / s + 1) := by nlinarith
      have hds : η * (1 / s) = s := by
        rw [← hss]; field_simp
      nlinarith [hstep, hds]
    linarith
  filter_upwards [hpieces, eventually_gt_atTop 0] with p hp hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  have hdiv : blockCount (nearInv η) p x / (p:ℝ)
      ≤ ∑ i ∈ Finset.range (K + 1), blockCount (Set.Ioo (lo i) (hi i)) p x / (p:ℝ) := by
    rw [← Finset.sum_div]
    gcongr
    exact hcount p
  have hsum2 : ∑ i ∈ Finset.range (K + 1), blockCount (Set.Ioo (lo i) (hi i)) p x / (p:ℝ)
      ≤ ∑ i ∈ Finset.range (K + 1), ((hi i - lo i) / Real.log 2 + 2 * δ) :=
    Finset.sum_le_sum fun i hi' => hp i hi'
  have hRHS : ∑ i ∈ Finset.range (K + 1), ((hi i - lo i) / Real.log 2 + 2 * δ)
      ≤ 7 * s / Real.log 2 + ε := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, hlensum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hd : ((K:ℝ) + 1) * (2 * δ) = ε := by
      rw [hδdef]; field_simp
      try ring
    have hcast : ((K + 1 : ℕ) : ℝ) = (K:ℝ) + 1 := by push_cast; ring
    rw [hcast, hd]
    have : (1 / (K:ℝ) + 2 * η + 2 * η * (K:ℝ)) / Real.log 2 ≤ 7 * s / Real.log 2 := by
      gcongr
    linarith
  linarith [hdiv, hsum2, hRHS]

#print axioms blockCount_freq_cellSet_nil
#print axioms blockCount_Ioo_le
#print axioms blockCount_Ioo_le'
#print axioms blockCount_nearInv_freq_le

end NormalNumbers.VandeheyS7
