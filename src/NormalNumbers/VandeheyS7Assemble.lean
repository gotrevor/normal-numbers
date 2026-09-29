/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Budget
import NormalNumbers.VandeheyRunClock

/-!
# Assembly: the Cesàro engine, and what still stands between it and `SampledUniformCount`

Every analytic input to the transfer is now proved (`VandeheyS7Word`, `VandeheyS7Boundary`,
`VandeheyS7Budget`).  What remains is bookkeeping, and this module supplies its engine and states
precisely what the bookkeeping still owes.

## The engine

If the image digit at position `j` is a fixed function `F` of a fixed-length window of the INPUT
digits, then an image block `v` occurs at `j` exactly when the input window at `j` lies in a
certain set `S_v` of input words.  So

    (image occurrences of `v` in the first `p`) / p  =  ∑_{u ∈ S_v} (occurrences of `u`) / p ,

and CF-normality of the input gives each summand a limit `γ(I_u)`.  For a FINITE `S_v` that is
immediate — `cfFreq_finset_sum` below — and it is the whole content when the input digits are
capped at a cutoff `K`, which is exactly the regime `VandeheyS7Boundary`'s cutoff already puts us
in.

## What is still owed

`S_v` is finite only after the cutoff; the uncapped set is countably infinite, so the assembly
needs the limit and the sum exchanged.  The repo already has the summability inputs for that
(`CFAeKhinchin.summable_logMul_vol_cfCylinder`, `summable_sqLog_gaussMeasure_cfCylinder`).  That
exchange, plus the identification of `S_v` from `cfDigit_agree_depth`, is the remaining work; it
is assembly, not new mathematics, and it is deliberately NOT hidden inside a Prop here.

## Guard rule

Content locator: `cfFreq_finset_sum_singleton` — a one-element family is exactly the
CF-normality hypothesis, so the lemma adds finite additivity and nothing else.  Degenerate case:
`cfFreq_finset_sum_empty` — the empty family gives the constant `0`, so the content is in the
nonempty case.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-- **The Cesàro engine.**  A finite family of input words has a joint occurrence frequency,
namely the sum of their Gauss masses.  This is finite additivity on top of CF-normality, and it
is what turns "the image digit is a window function of the input" into an image frequency. -/
theorem cfFreq_finset_sum {x : ℝ} (hx : IsCFNormal x) (S : Finset (List ℕ))
    (hS : ∀ u ∈ S, u ≠ [] ∧ ∀ a ∈ u, 1 ≤ a) :
    Tendsto
      (fun p => (∑ u ∈ S, (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)) / p)
      atTop (nhds (∑ u ∈ S, (gaussMeasure (cfCylinder u)).toReal)) := by
  have hterm : ∀ u ∈ S, Tendsto
      (fun p => (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ) / p)
      atTop (nhds ((gaussMeasure (cfCylinder u)).toReal)) := by
    intro u hu
    obtain ⟨hne, hpos⟩ := hS u hu
    exact hx u hne hpos
  have hsum := tendsto_finset_sum S hterm
  refine hsum.congr fun p => ?_
  rw [Finset.sum_div]

/-- Content locator: one word is exactly CF-normality. -/
theorem cfFreq_finset_sum_singleton {x : ℝ} (hx : IsCFNormal x) {u : List ℕ}
    (hne : u ≠ []) (hpos : ∀ a ∈ u, 1 ≤ a) :
    Tendsto (fun p => (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ) / p)
      atTop (nhds ((gaussMeasure (cfCylinder u)).toReal)) := hx u hne hpos

/-- Degenerate case: the empty family carries no content. -/
theorem cfFreq_finset_sum_empty {x : ℝ} (hx : IsCFNormal x) :
    Tendsto
      (fun p => (∑ u ∈ (∅ : Finset (List ℕ)),
        (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)) / p)
      atTop (nhds 0) := by
  simpa using cfFreq_finset_sum hx ∅ (by simp)

/-- **The assembly step, with the remaining obligation isolated.**  If the image's occurrence
count of `v` agrees, up to a BOUNDED error, with the total occurrence count of a finite family
`S` of input words, then it has a Cesàro limit — and that limit is `∑_{u ∈ S} γ(I_u)`, which
depends only on `S`, hence only on the window function and `v`, and NOT on `x`.  That is exactly
the `x`-independence `SampledUniformCount` asks for.

The bounded error is the right form: the edge effects of a window of fixed length are `O(1)` in
`p`, not `o(p)` in disguise.  What is still owed is `hdecomp` itself — the identification of `S`
from `cfDigit_agree_depth` — and nothing else. -/
theorem cfCount_tendsto_of_decomposition {x z : ℝ} (hx : IsCFNormal x) (v : List ℕ)
    (S : Finset (List ℕ)) (hS : ∀ u ∈ S, u ≠ [] ∧ ∀ a ∈ u, 1 ≤ a) {C : ℝ}
    (hdecomp : ∀ p : ℕ, |VandeheyOut.cfCount v z p
      - ∑ u ∈ S, (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)| ≤ C) :
    Tendsto (fun p => VandeheyOut.cfCount v z p / p) atTop
      (nhds (∑ u ∈ S, (gaussMeasure (cfCylinder u)).toReal)) := by
  have hmain := cfFreq_finset_sum hx S hS
  have herr : Tendsto (fun p : ℕ => (VandeheyOut.cfCount v z p
      - ∑ u ∈ S, (countOccurrences u ((List.range p).map (cfDigit x)) : ℝ)) / p)
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpr : (0:ℝ) < p := by exact_mod_cast hp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpr]
    gcongr
    exact hdecomp p
  have := herr.add hmain
  rw [zero_add] at this
  refine this.congr fun p => ?_
  rcases eq_or_ne (p : ℝ) 0 with hp0 | hp0
  · simp [hp0]
  · field_simp
    ring

section Audit

#print axioms cfFreq_finset_sum
#print axioms cfCount_tendsto_of_decomposition

end Audit

end NormalNumbers.VandeheyS7
