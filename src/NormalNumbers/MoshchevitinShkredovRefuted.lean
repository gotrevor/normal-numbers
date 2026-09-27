/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline

/-!
# The Moshchevitin–Shkredov hot-spot criterion is false for continued fractions

Moshchevitin–Shkredov 2003, Theorem 1 (the Pyatetskii-Shapiro criterion in their form) is
the step Vandehey 2017 cites for his Lemma 3.3 (3.2 in arXiv v1).  Airey–Mance
(arXiv:1912.10265) show it is false on non-compact spaces.  This file states the CF
specialization and asks for its refutation (open target, not yet wired into
`src/NormalNumbers.lean` - wire it in once proved).

Counterexample (Airey–Mance's `(1,2,3,…)`, lifted): `x = [0; 1, 2, 3, 4, …]`.  Its digits
strictly increase, so every block occurs at most once, every block frequency tends to `0`,
and the hypothesis holds vacuously for any `σ`; but digit `1` has frequency `0 ≠ γ(I₁)`,
so `x` is not CF-normal.  When proved, add a `.falseAsStated` `Maze.lean` row aliased onto
`moshchevitinShkredov_cf_false`, and point `papers/vandehey-2017-open-problem-attack-map.md`
§6.1 at it.
-/

namespace NormalNumbers

/-- The CF specialization of Moshchevitin–Shkredov Theorem 1 (as Vandehey uses it, with a
linear `φ(t) = σ t`): uniformly bounded upper block frequencies imply CF-normality. -/
def moshchevitinShkredov_cf : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → Irrational x →
    (∃ σ : ℝ, ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Filter.limsup
          (fun p => (countOccurrences v ((List.range p).map (cfDigit x)) : ℝ) / p)
          Filter.atTop
        ≤ σ * (gaussMeasure (cfCylinder v)).toReal) →
    IsCFNormal x

/-- **Refutation** (open target): witnessed by `x = [0; 1, 2, 3, …]`. -/
theorem moshchevitinShkredov_cf_false : ¬ moshchevitinShkredov_cf := by
  sorry

end NormalNumbers
