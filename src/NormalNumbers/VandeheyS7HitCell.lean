/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7CellFreq

/-!
# S7-HC: the hit cell — a window followed by a cell IS a cell

The interval-target window-hit theorem counts the times `n` at which the orbit is in the window
cylinder `I_v` and, `|v|` steps later, in a cell of the cover of the target interval.  This
module identifies that event: along irrational points,

    t ∈ cellSet (v ++ c) S   ↔   t ∈ I_v  ∧  G^{|v|} t ∈ cellSet c S    (`mem_cellSet_append_iff`)

so the hit event is a single cell of the word `v ++ c` — whose frequency CF-normality pins
(lap 53) and whose mass the quasi-Bernoulli bound controls (lap 51):

    γ(cellSet (v ++ c) S)  ≤  (1 + 8 log 2) · γ(I_v) · γ(cellSet c S)   (`gaussMeasure_cellSet_append_le`)

## Guard rule

Content locator: the `←` direction needs the orbit point to be in `(0,1)`, which is where
irrationality enters; `gaussMeasure_cellSet_append_le` at `v = []` degenerates to
`γ(cellSet c S) ≤ (1+8log2)γ(cellSet c S)`, so the content is in the window factor.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The hit-cell identity.** -/
theorem mem_cellSet_append_iff {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    (v c : List ℕ) (S : ℕ) :
    t ∈ cellSet (v ++ c) S ↔ t ∈ cfCylinder v ∧ gaussMap^[v.length] t ∈ cellSet c S := by
  obtain ⟨hirr', hmem'⟩ := irrational_orbit t hirr hmem v.length
  constructor
  · rintro ⟨⟨htmem, hdig⟩, hthr⟩
    refine ⟨⟨htmem, fun i hi => ?_⟩, ⟨⟨hmem', fun j hj => ?_⟩, ?_⟩⟩
    · have h := hdig i (by simp; omega)
      rwa [List.getD_append _ _ _ _ hi] at h
    · have h := hdig (v.length + j) (by simp; omega)
      rw [List.getD_append_right v c 0 (v.length + j) (by omega)] at h
      simpa [cfDigit_add, Nat.add_sub_cancel_left] using
        (by simpa [Nat.add_sub_cancel_left] using h : cfDigit t (v.length + j) = c.getD j 0)
    · show S ≤ cfDigit (gaussMap^[v.length] t) c.length
      rw [← cfDigit_add]
      simpa [List.length_append] using hthr
  · rintro ⟨⟨htmem, hvdig⟩, ⟨⟨-, hcdig⟩, hthr⟩⟩
    refine ⟨⟨htmem, fun i hi => ?_⟩, ?_⟩
    · rw [List.length_append] at hi
      rcases Nat.lt_or_ge i v.length with h | h
      · rw [List.getD_append _ _ _ _ h]
        exact hvdig i h
      · rw [List.getD_append_right v c 0 i h]
        have hj : i - v.length < c.length := by omega
        have hc := hcdig (i - v.length) hj
        have hi2 : i = v.length + (i - v.length) := by omega
        conv_lhs => rw [hi2]
        rw [cfDigit_add]
        exact hc
    · show S ≤ cfDigit t (v ++ c).length
      rw [List.length_append, cfDigit_add]
      exact hthr

/-- The subset form, which is what the counting uses. -/
theorem cellSet_append_subset (v c : List ℕ) (S : ℕ) :
    cellSet (v ++ c) S ⊆
      (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (cellSet c S)) ∪ Set.range ((↑) : ℚ → ℝ) := by
  intro t ht
  by_cases hirr : Irrational t
  · have hmem : t ∈ Set.Ioo (0:ℝ) 1 := ht.1.1
    exact Or.inl ((mem_cellSet_append_iff hirr hmem v c S).1 ht)
  · refine Or.inr ?_
    rw [Irrational, not_not] at hirr
    exact hirr

private lemma gaussMeasure_countable_zero' {S : Set ℝ} (hS : S.Countable) :
    gaussMeasure S = 0 := by
  have hm : MeasurableSet S := hS.measurableSet
  have h := gaussMeasure_le_volume S hm
  rw [hS.measure_zero volume, mul_zero] at h
  simpa using h

/-- **The hit-cell mass bound.** -/
theorem gaussMeasure_cellSet_append_le (v c : List ℕ) (hvpos : ∀ a ∈ v, 1 ≤ a) (S : ℕ) :
    (gaussMeasure (cellSet (v ++ c) S)).toReal ≤
      (1 + 8 * Real.log 2) * ((gaussMeasure (cfCylinder v)).toReal *
        (gaussMeasure (cellSet c S)).toReal) := by
  have hnull : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    gaussMeasure_countable_zero' (Set.countable_range _)
  have hmono : gaussMeasure (cellSet (v ++ c) S)
      ≤ gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (cellSet c S)) := by
    calc gaussMeasure (cellSet (v ++ c) S)
        ≤ gaussMeasure ((cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (cellSet c S)) ∪
            Set.range ((↑) : ℚ → ℝ)) := measure_mono (cellSet_append_subset v c S)
      _ ≤ gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (cellSet c S)) +
            gaussMeasure (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  have hqb := gaussMeasure_inter_preimage_le v hvpos (measurableSet_cellSet c S)
    (fun t ht => ht.1.1)
  have hmonoR : (gaussMeasure (cellSet (v ++ c) S)).toReal
      ≤ (gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (cellSet c S))).toReal :=
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _) |>.2 hmono
  linarith

section Audit

#print axioms mem_cellSet_append_iff
#print axioms gaussMeasure_cellSet_append_le

end Audit

end NormalNumbers.VandeheyS7
