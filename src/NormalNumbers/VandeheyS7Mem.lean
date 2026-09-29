/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-MY: finite memory DEFEATS predictability — the mechanism `ClassFreqBound` needs

Directive fact (α) says CF-normality of `x` cannot by itself beat a *predictable* selection of
times, and fact (δ) supplies the one escape hatch: finiteness of the predictor's range.  This
module isolates the mechanism by which that escape hatch actually works, in the cleanest possible
form — and it is not an approximation argument, it is an identity.

**If the selection at time `n` is determined by the last `L` input digits**, then "`n` is selected
AND the next `|v|` digits are `v`" is the occurrence of the SINGLE word `u ++ v` at position
`n − L`.  So CF-normality of `x` — a statement about occurrence frequencies of fixed words —
applies to the *joint* event directly, with no independence assumption and no error term:

    freq(joint)  =  Σ_{u ∈ U} γ(I_{u++v})   (`tendsto_sum_countOccurrences_append`)

and bounded distortion of the Gauss map collapses the right-hand side:

    γ(I_{u++v})  ≤  8·log 2 · γ(I_u) · γ(I_v)   (`gaussMeasure_append_le`, lap 50, S7-WH)

giving

    freq(joint)  ≤  8·log 2 · γ(I_v) · freq(selected)    (`memory_joint_le`)

— which is exactly `ClassFreqBound` with the **absolute** constant `C = 8 log 2`, independent of
the memory length `L`, of the selector set `U`, and of the number of cells.

So the remaining gap in the §7 chain is now completely explicit, and it is a statement about the
transducer and nothing else:

> **`CellMemory`** — up to times of small frequency, which cell of the fact-(δ) net the state
> `s_n` lies in is determined by a bounded number of recent input digits.

Fact (γ) (`Γ ∩ Φ⁻¹ΓΦ = {±I}`) says the *matrix* `s_n` remembers everything; `CellMemory` asks
only that its *position in a ρ-net* does not.  That is the honest wall, and it is a different and
much better-posed one than the self-joining wall.
-/
import NormalNumbers.VandeheyS7Net
import NormalNumbers.VandeheyS7WindowHit
import NormalNumbers.Headline

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

/-! ## Finite-memory selections -/

/-- Finite additivity of CF-normality: a finite family of words has the sum of the expected
frequencies. -/
theorem tendsto_sum_countOccurrences {x : ℝ} (hx : IsCFNormal x) (U : Finset (List ℕ))
    (hU : ∀ u ∈ U, u ≠ [] ∧ ∀ a ∈ u, 1 ≤ a) :
    Tendsto (fun p => (∑ u ∈ U,
        (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)) / p)
      atTop (nhds (∑ u ∈ U, (gaussMeasure (cfCylinder u)).toReal)) := by
  have : ∀ p : ℕ, (∑ u ∈ U, (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)) / p
      = ∑ u ∈ U, (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ) / p := by
    intro p; rw [Finset.sum_div]
  simp only [this]
  exact tendsto_finsetSum _ (fun u hu => hx u (hU u hu).1 (hU u hu).2)

/-- **S7-MY, the headline.**  For a finite-memory selection — selector words `U`, target word
`v` — the joint frequency is at most `8 log 2 · γ(I_v)` times the selection frequency.  The
constant does NOT depend on the memory length, on `U`, or on the number of cells. -/
theorem memory_joint_le {x : ℝ} (hx : IsCFNormal x) (U : Finset (List ℕ))
    (hU : ∀ u ∈ U, u ≠ [] ∧ ∀ a ∈ u, 1 ≤ a)
    (v : List ℕ) (hv : v ≠ []) (hvpos : ∀ a ∈ v, 1 ≤ a) :
    Tendsto (fun p => (∑ u ∈ U,
        (countOccurrences (u ++ v) ((List.range p).map (cfDigit x)) : ℝ)) / p)
        atTop (nhds (∑ u ∈ U, (gaussMeasure (cfCylinder (u ++ v))).toReal))
      ∧ (∑ u ∈ U, (gaussMeasure (cfCylinder (u ++ v))).toReal)
          ≤ 8 * Real.log 2 * (gaussMeasure (cfCylinder v)).toReal *
              ∑ u ∈ U, (gaussMeasure (cfCylinder u)).toReal := by
  constructor
  · have hdiv : ∀ p : ℕ, (∑ u ∈ U,
        (countOccurrences (u ++ v) ((List.range p).map (cfDigit x)) : ℝ)) / p
        = ∑ u ∈ U, (countOccurrences (u ++ v) ((List.range p).map (cfDigit x)) : ℝ) / p :=
      fun p => Finset.sum_div _ _ _
    simp only [hdiv]
    refine tendsto_finsetSum _ (fun u hu => hx (u ++ v) (by simp [hv]) ?_)
    intro a ha
    exact (List.mem_append.1 ha).elim ((hU u hu).2 a) (hvpos a)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have h := gaussMeasure_append_le u v (hU u hu).1 hv (hU u hu).2 hvpos
    calc (gaussMeasure (cfCylinder (u ++ v))).toReal
        ≤ 8 * Real.log 2 * ((gaussMeasure (cfCylinder u)).toReal *
            (gaussMeasure (cfCylinder v)).toReal) := h
      _ = 8 * Real.log 2 * (gaussMeasure (cfCylinder v)).toReal *
            (gaussMeasure (cfCylinder u)).toReal := by ring

section Audit

#print axioms tendsto_sum_countOccurrences
#print axioms memory_joint_le

end Audit

end NormalNumbers.VandeheyS7
