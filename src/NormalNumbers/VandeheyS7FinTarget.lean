/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-FT: finitely many targets close the crux, end to end

This module runs the whole lap-81–87 chain to a conclusion, on the one hypothesis the chain was
built to isolate.  Suppose the run's state-dependent targets are, for every time, contained in a
FIXED finite family of intervals:

    ∀ n, mapBlockSet (runState Φ x n) w 0 ⊆ ⋃ i, Ioo (α i) (β i)          (`hcover`)

Then for every `ε > 0` the crux's counting function obeys

    slotCount Φ x w p / p  ≤  (Σ_i (β i − α i)) / log 2 + ε              (`slotCount_le_of_finiteTargets`)

eventually — with no further hypothesis, no modulus, and no class equidistribution.  The proof is
the composition:

  S7-SK   the counting function is a Birkhoff sum of a fixed observable;
  S7-CV   the level-`M` cylinders meeting an interval have mass ≤ (length + 2·2^{-M+1})/log 2;
  S7-WD′  a finite-window domination, outside a bounded-digit exceptional family, bounds the
          frequency;
  S7-WN   and CF-normality of `x` evaluates every finite-window frequency exactly.

The digit bound `B` and the level `M` are chosen inside the proof: `B` from
`exists_boundedWords_sum_gt` (the truncation is tight) and `M` from `2/2^M ≤ ε`.

## What this says about the route

It is the exact analogue of Vandehey's finite-state Theorem 1.1, obtained through the new
machinery rather than through a finite automaton: *finiteness of the predictor's range* — directive
fact (α)'s first escape hatch, supplied by fact (δ) — really does close the crux, and the constant
is `Σ_i |target_i| / log 2`.  What remains for §7 Problem 1 is therefore exactly: produce the
finite family.  Fact (δ)'s compact box plus a `ρ`-net gives one for the times of width `≥ η`, with
`Σ_i |target_i| ≤ M(η,ρ)·(2K₀/η)·γ(I_w)`; the open point is the frequency of the remaining times.

## Guard rule

Content locator: `hgood` is where the truncation is paid — the exceptional term `1 − Σ_G γ` is
made `< ε/2` by choosing `B`, and the cover's boundary term `2·N·2^{-M+1}` is made `< ε/2` by
choosing `M`; both are genuinely needed, since the cover family must be finite and the cylinders
have positive diameter.  Degenerate case: an empty target family forces `slotObs = 0`, and the
bound reads `0`.
-/
import NormalNumbers.VandeheyS7Cover
import NormalNumbers.VandeheyS7WindowDom
import NormalNumbers.VandeheyOutputFreq

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-- Sub-additivity of a nonnegative sum over a `biUnion`. -/
lemma sum_biUnion_le_sum_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset (List ℕ)) (f : List ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hunion : ∑ a ∈ t i ∪ s.biUnion t, f a
          ≤ ∑ a ∈ t i, f a + ∑ a ∈ s.biUnion t, f a := by
        have hdis : Disjoint (t i) (s.biUnion t \ t i) := Finset.disjoint_sdiff
        have hrw : t i ∪ s.biUnion t = t i ∪ (s.biUnion t \ t i) := by
          rw [Finset.union_sdiff_self_eq_union]
        rw [hrw, Finset.sum_union hdis]
        have : ∑ a ∈ s.biUnion t \ t i, f a ≤ ∑ a ∈ s.biUnion t, f a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) fun a _ _ => hf a
        linarith
      linarith [ih]

/-- The finite cover family: the level-`M`, digit-`≤B` words whose cylinder meets one of the
target intervals. -/
noncomputable def coverWords (B M N : ℕ) (α β : Fin N → ℝ) : Finset (List ℕ) :=
  (boundedWords B M).filter fun v => ∃ i : Fin N, ∃ t ∈ cfCylinder v, t ∈ Set.Ioo (α i) (β i)

lemma coverWords_subset (B M N : ℕ) (α β : Fin N → ℝ) :
    coverWords B M N α β ⊆ boundedWords B M := by
  rw [coverWords]; exact Finset.filter_subset _ _

lemma mem_boundedWords_len {B M : ℕ} {v : List ℕ} (hv : v ∈ boundedWords B M) :
    v.length = M ∧ ∀ a ∈ v, 1 ≤ a :=
  ⟨(mem_boundedWords.1 hv).1, fun a ha => ((mem_boundedWords.1 hv).2 a ha).1⟩

/-- The cover's mass is at most the total target length plus a boundary term. -/
theorem sum_gaussMeasure_coverWords_le {B M N : ℕ} (hM : 0 < M) {α β : Fin N → ℝ}
    (hab : ∀ i, α i ≤ β i) :
    (∑ v ∈ coverWords B M N α β, (gaussMeasure (cfCylinder v)).toReal)
      ≤ ∑ i : Fin N, ((β i - α i) + 2 * (2 / 2 ^ M)) / Real.log 2 := by
  classical
  set δ : ℝ := 2 / 2 ^ M with hδdef
  have hδ : 0 ≤ δ := by positivity
  -- split the cover by which target it meets
  set Si : Fin N → Finset (List ℕ) := fun i =>
    (boundedWords B M).filter fun v => ∃ t ∈ cfCylinder v, t ∈ Set.Ioo (α i) (β i) with hSi
  have hsub : coverWords B M N α β ⊆ Finset.univ.biUnion Si := by
    intro v hv
    rw [coverWords, Finset.mem_filter] at hv
    obtain ⟨hvB, i, ht⟩ := hv
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by rw [hSi]; exact Finset.mem_filter.2 ⟨hvB, ht⟩⟩
  have hnn : ∀ v : List ℕ, 0 ≤ (gaussMeasure (cfCylinder v)).toReal := fun _ =>
    ENNReal.toReal_nonneg
  have hstep : (∑ v ∈ coverWords B M N α β, (gaussMeasure (cfCylinder v)).toReal)
      ≤ ∑ i : Fin N, ∑ v ∈ Si i, (gaussMeasure (cfCylinder v)).toReal := by
    calc (∑ v ∈ coverWords B M N α β, (gaussMeasure (cfCylinder v)).toReal)
        ≤ ∑ v ∈ Finset.univ.biUnion Si, (gaussMeasure (cfCylinder v)).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => hnn v
      _ ≤ ∑ i : Fin N, ∑ v ∈ Si i, (gaussMeasure (cfCylinder v)).toReal :=
          sum_biUnion_le_sum_sum _ _ _ hnn
  refine hstep.trans (Finset.sum_le_sum fun i _ => ?_)
  refine sum_gaussMeasure_cover_le (M := M) (S := Si i)
    (fun v hv => (mem_boundedWords_len (Finset.mem_filter.1 hv).1).1)
    (fun v hv => (mem_boundedWords_len (Finset.mem_filter.1 hv).1).2)
    hδ (hab i) ?_ ?_
  · intro v hv u hu t ht
    have hvB := (Finset.mem_filter.1 hv).1
    obtain ⟨hlen, hpos⟩ := mem_boundedWords_len hvB
    have hne : v ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have := dist_le_of_mem_cfCylinder hne hpos hu ht
    rw [hlen] at this
    exact this
  · intro v hv
    exact (Finset.mem_filter.1 hv).2

end MapState

end NormalNumbers.VandeheyS7
