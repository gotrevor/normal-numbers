/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelGradedStatement
import NormalNumbers.OccurrenceCountEquiv

/-!
# Faithfulness cross-check for Theorem C′ (independent NL → Lean rendering)

`PrimeModelGradedStatement.lean` is the audit surface: the headline with every definition of
this repository unwound.  It defends against *our* definitions drifting from the prose.  It does
not defend against the prose itself having been written to match our definitions.

So on 2026-09-23 the English statement of Theorem C′ (and only the English — never our Lean) was
handed to an independent auto-formalizer, which produced its own Lean rendering.  It differs from
ours in exactly three places, and **all three are provably equivalent**, which is what this
module records:

1. *the fresh window*: it wrote `Real.sqrt N < p` over `Finset.Icc 1 N`, we write
   `Nat.sqrt N < p` over `Finset.Ioc (Nat.sqrt N) N`.  For a natural `p` both say `N < p²`
   (`sqrt_lt_iff_nat` below), so the index sets are **equal**, not merely cofinal;
2. *divergence*: it wrote `¬ Summable` over the subtype `{p // p.Prime ∧ P p}`, we write
   `¬ Summable` of the indicator on `ℕ` (`divergentRecip_iff_subtype`);
3. *the occurrence count*: it counted start positions `i < n` whose digit block matches, we
   count suffixes of the first `n` digits carrying `w` as a prefix.  These are literally
   different finite numbers, but they differ by at most `|w| = O(1)` out of `n`, so the
   frequency limits agree — proved in `OccurrenceCountEquiv.lean` (`tendsto_occStart_iff`)
   and cashed here as `isNormal_subsetLambert_crossCheckForm_occStart`.

`isNormal_subsetLambert_crossCheckForm` then derives our headline from the independently written
hypotheses verbatim, which is the actual content of the cross-check.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyGraded

open NormalNumbers NormalNumbers.G4Sparse NormalNumbers.PrimeLambert

variable (P : ℕ → Prop) [DecidablePred P]

/-- The real and the natural square-root cutoffs define the **same** fresh window. -/
theorem sqrt_lt_iff_nat {N p : ℕ} (hp : 0 < p) : Real.sqrt N < p ↔ Nat.sqrt N < p := by
  rw [show ((p : ℝ)) = ((p : ℝ)) from rfl, Real.sqrt_lt' (by exact_mod_cast hp), Nat.sqrt_lt']
  constructor
  · intro h; exact_mod_cast (by exact_mod_cast h : (N : ℝ) < ((p ^ 2 : ℕ) : ℝ))
  · intro h
    have : ((N : ℕ) : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    simpa using this

theorem freshWindow_eq (N : ℕ) :
    (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ P p ∧ Real.sqrt N < p)
      = (Finset.Ioc (Nat.sqrt N) N).filter (fun p => Nat.Prime p ∧ P p) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hpr, hP, hs⟩
    exact ⟨⟨(sqrt_lt_iff_nat (by omega)).1 hs, h2⟩, hpr, hP⟩
  · rintro ⟨⟨h1, h2⟩, hpr, hP⟩
    have hp0 : 0 < p := hpr.pos
    exact ⟨⟨hp0, h2⟩, hpr, hP, (sqrt_lt_iff_nat hp0).2 h1⟩

/-- Hypothesis (a), independently written, is our `SqrtFreshMassZero`. -/
theorem sqrtFreshMassZero_iff_crossCheck :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N).filter
        (fun p => Nat.Prime p ∧ P p ∧ Real.sqrt N < p), (1 : ℝ) / p) atTop (𝓝 0)
      ↔ NormalNumbers.PrimeModel.SqrtFresh.SqrtFreshMassZero P := by
  constructor <;> intro h <;>
    · refine h.congr fun N => ?_
      simp [NormalNumbers.PrimeModel.SqrtFresh.SqrtFreshMassZero, recipSumIoc,
        freshWindow_eq P N]

/-- Hypothesis (b), independently written, is our `DivergentRecip`. -/
theorem divergentRecip_iff_subtype :
    (¬ Summable (fun p : {p : ℕ // Nat.Prime p ∧ P p} => (1 : ℝ) / (p : ℕ)))
      ↔ DivergentRecip P := by
  rw [DivergentRecip, not_iff_not]
  have hset : ∀ p : ℕ,
      (if Nat.Prime p ∧ P p then (1 : ℝ) / p else 0)
        = Set.indicator {p : ℕ | Nat.Prime p ∧ P p} (fun p : ℕ => (1 : ℝ) / p) p := by
    intro p
    by_cases hp : Nat.Prime p ∧ P p <;> simp [Set.indicator, hp]
  rw [funext hset]
  exact summable_subtype_iff_indicator (s := {p : ℕ | Nat.Prime p ∧ P p})
    (f := fun p : ℕ => (1 : ℝ) / p)

/-- **The cross-check.**  Theorem C′ off the independently formalised hypotheses, verbatim. -/
theorem isNormal_subsetLambert_crossCheckForm
    (hfresh : Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N).filter
        (fun p => Nat.Prime p ∧ P p ∧ Real.sqrt N < p), (1 : ℝ) / p) atTop (𝓝 0))
    (hdiv : ¬ Summable (fun p : {p : ℕ // Nat.Prime p ∧ P p} => (1 : ℝ) / (p : ℕ))) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_sqrtFreshMassZero P
    ((sqrtFreshMassZero_iff_crossCheck P).1 hfresh)
    ((divergentRecip_iff_subtype P).1 hdiv)


/-- **The cross-check in the independent counting convention.**  Same hypotheses, and the
conclusion stated with `occStart` — occurrences counted by *start position* `i < n`, reading
digits past the end of the prefix — rather than by suffixes of the first `n` digits. -/
theorem isNormal_subsetLambert_crossCheckForm_occStart
    (hfresh : Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N).filter
        (fun p => Nat.Prime p ∧ P p ∧ Real.sqrt N < p), (1 : ℝ) / p) atTop (𝓝 0))
    (hdiv : ¬ Summable (fun p : {p : ℕ // Nat.Prime p ∧ P p} => (1 : ℝ) / (p : ℕ))) :
    ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 4) →
      Tendsto (fun n : ℕ =>
          (occStart w (digitOf 4 (Int.fract (subsetLambert P 4))) n : ℝ) / n)
        atTop (𝓝 (((4 : ℝ) ^ w.length)⁻¹)) := by
  intro w hw hd
  exact (tendsto_occStart_iff w hw _ _).2
    (isNormal_subsetLambert_crossCheckForm P hfresh hdiv w hw hd)

end NormalNumbers.PrimeModel.FamilyGraded
