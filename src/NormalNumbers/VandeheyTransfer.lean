/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyZFree

/-!
# Assembling the automaton transfer principle

Glue for `VandeheyAutomaton.exists_jointFreq_limit`: the squeeze that turns the exact
combinatorics of `VandeheyAutomaton.lean` and the two analytic limits
(`tendsto_digitTail_freq`, `tendsto_gaussMeasure_zFreeSet`) into one convergent frequency
with an `x`-independent limit.

This file holds the arithmetic-of-limits helpers and the digit-tail smallness bound; the
squeeze itself follows.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut

/-! ## Shifting the index in a frequency -/

/-- `(n − L)` shift: a frequency limit survives a bounded backward shift of the numerator. -/
lemma tendsto_sub_div {f : ℕ → ℕ} {c : ℝ} (L : ℕ)
    (hf : Tendsto (fun m => (f m : ℝ) / m) atTop (nhds c)) :
    Tendsto (fun n => (f (n - L) : ℝ) / n) atTop (nhds c) := by
  have h1 : Tendsto (fun n : ℕ => n - L) atTop atTop := tendsto_sub_atTop_nat L
  have h2 : Tendsto (fun n : ℕ => (f (n - L) : ℝ) / ((n - L : ℕ) : ℝ)) atTop (nhds c) :=
    hf.comp h1
  have h3 : Tendsto (fun n : ℕ => (((n - L : ℕ) : ℝ)) / (n : ℝ)) atTop (nhds 1) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) - (L : ℝ) / n) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (L : ℝ))
    rw [sub_zero] at hbase
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop L] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_sub hn.le]
    field_simp
  have hmul := h2.mul h3
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop L] with n hn
  have hnL : ((n - L : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_sub hn.le]
    have : (L : ℝ) < n := by exact_mod_cast hn
    intro h; linarith [sub_eq_zero.mp h]
  field_simp

/-- `(m + L)` shift: likewise for a bounded forward shift. -/
lemma tendsto_add_div {f : ℕ → ℕ} {c : ℝ} (L : ℕ)
    (hf : Tendsto (fun n => (f n : ℝ) / n) atTop (nhds c)) :
    Tendsto (fun m => (f (m + L) : ℝ) / m) atTop (nhds c) := by
  have h1 : Tendsto (fun m : ℕ => m + L) atTop atTop := tendsto_add_atTop_nat L
  have h2 : Tendsto (fun m : ℕ => (f (m + L) : ℝ) / ((m + L : ℕ) : ℝ)) atTop (nhds c) :=
    hf.comp h1
  have h3 : Tendsto (fun m : ℕ => (((m + L : ℕ) : ℝ)) / (m : ℝ)) atTop (nhds 1) := by
    have hbase : Tendsto (fun m : ℕ => (1 : ℝ) + (L : ℝ) / m) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (L : ℝ))
    rw [add_zero] at hbase
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  have hmul := h2.mul h3
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmL : ((m + L : ℕ) : ℝ) ≠ 0 := by push_cast; positivity
  field_simp

/-! ## The digit tail is uniformly small -/

/-- `(1/(K+1), 1)` is covered by the length-one cylinders with digit in `[1,K]`: for
`x` in that interval `x⁻¹ ∈ (1, K+1)`, so `⌊x⁻¹⌋₊ ∈ [1,K]`. -/
lemma Ioo_subset_iUnion_digit_cylinder (K : ℕ) :
    Set.Ioo (1 / ((K : ℝ) + 1)) 1 ⊆ ⋃ k ∈ Finset.Icc 1 K, cfCylinder [k] := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx1.le
  have hinv1 : (1 : ℝ) < x⁻¹ := by
    rw [lt_inv_comm₀ one_pos hx0]; simpa using hx2
  have hinv2 : x⁻¹ < (K : ℝ) + 1 := by
    rw [inv_lt_comm₀ hx0 hKpos]
    rw [one_div] at hx1
    simpa using hx1
  set a : ℕ := ⌊x⁻¹⌋₊ with ha
  have ha1 : 1 ≤ a := Nat.one_le_floor_iff _ |>.mpr hinv1.le
  have haK : a ≤ K := by
    have : (a : ℝ) ≤ x⁻¹ := Nat.floor_le (by positivity)
    have hlt : (a : ℝ) < (K : ℝ) + 1 := lt_of_le_of_lt this hinv2
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  refine Set.mem_iUnion₂.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha1, haK⟩, ⟨hx0, hx2⟩, ?_⟩
  intro i hi
  simp only [List.length_singleton] at hi
  interval_cases i
  simpa [cfDigit_zero] using ha.symm

/-- **The digit tail mass is `O(1/K)`**: `1 − Σ_{k=1}^{K} γ(I_{[k]}) ≤ log(1 + 1/(K+1))/log 2`. -/
theorem digitTail_le (K : ℕ) :
    1 - ∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal
      ≤ Real.log (1 + 1 / ((K : ℝ) + 1)) / Real.log 2 := by
  classical
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hu0 : (0 : ℝ) ≤ 1 / ((K : ℝ) + 1) := by positivity
  have hu1 : 1 / ((K : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hKpos]
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  -- the finite union has mass at least that of the interval
  have hdisj : (↑(Finset.Icc 1 K) : Set ℕ).PairwiseDisjoint (fun k => cfCylinder [k]) :=
    fun k _ k' _ hne => cfCylinder_disjoint (by simp) (by simpa using hne)
  have hbi := MeasureTheory.measure_biUnion_finset hdisj
    (fun k (_ : k ∈ Finset.Icc 1 K) => measurableSet_cfCylinder [k]) (μ := gaussMeasure)
  have hmono : gaussMeasure (Set.Ioo (1 / ((K : ℝ) + 1)) 1)
      ≤ gaussMeasure (⋃ k ∈ Finset.Icc 1 K, cfCylinder [k]) :=
    measure_mono (Ioo_subset_iUnion_digit_cylinder K)
  have hIoo : gaussMeasure (Set.Ioo (1 / ((K : ℝ) + 1)) 1)
      = ENNReal.ofReal ((Real.log 2 - Real.log (1 + 1 / ((K : ℝ) + 1))) / Real.log 2) := by
    rw [gaussMeasure_Ioo hu0 hu1 (le_refl 1)]
    norm_num
  have hsum : ∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal
      = (gaussMeasure (⋃ k ∈ Finset.Icc 1 K, cfCylinder [k])).toReal := by
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), hbi]
  have hle : (Real.log 2 - Real.log (1 + 1 / ((K : ℝ) + 1))) / Real.log 2
      ≤ ∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal := by
    rw [hsum]
    have h1 := ENNReal.toReal_mono (measure_ne_top gaussMeasure _) hmono
    rw [hIoo, ENNReal.toReal_ofReal] at h1
    · exact h1
    · have : Real.log (1 + 1 / ((K : ℝ) + 1)) ≤ Real.log 2 := by
        apply Real.log_le_log (by positivity)
        linarith
      apply div_nonneg (by linarith) hlog.le
  have hsplit : (Real.log 2 - Real.log (1 + 1 / ((K : ℝ) + 1))) / Real.log 2
      = 1 - Real.log (1 + 1 / ((K : ℝ) + 1)) / Real.log 2 := by
    field_simp
  rw [hsplit] at hle
  linarith

/-- The digit-tail bound tends to `0`. -/
theorem tendsto_digitTail_bound :
    Tendsto (fun K : ℕ => Real.log (1 + 1 / ((K : ℝ) + 1)) / Real.log 2) atTop (nhds 0) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKat : Tendsto (fun K : ℕ => (K : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun K : ℕ => 1 / ((K : ℝ) + 1)) atTop (nhds 0) := by
    refine (hKat.inv_tendsto_atTop).congr fun K => ?_
    simp [one_div]
  have h1 : Tendsto (fun K : ℕ => 1 + 1 / ((K : ℝ) + 1)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add h0
  have h2 : Tendsto (fun K : ℕ => Real.log (1 + 1 / ((K : ℝ) + 1))) atTop (nhds 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
    simpa [Function.comp_def] using this
  simpa using h2.div_const (Real.log 2)

end NormalNumbers
