/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertNonNormal

/-!
# Stretch node: the word frequencies of a perfect-power Lambert constant exist

Not part of the richness gate.  Conjecture node only (no `sorry` in this file).

For `r ≥ 2` the coefficient sequence `c m = #{d > 8 : d^r ∣ m}` is limit-periodic in the
Besicovitch sense: `c = lim_D c_D` with `c_D m = #{8 < d ≤ D : d^r ∣ m}` periodic mod `lcm(1..D)^r`
and `‖c − c_D‖_{B¹} ≤ Σ_{d>D} d^{−r} → 0`.  The digit at position `n` is a function of the window
`(c(n+1), …, c(n+J))` up to an event of density `O(b^{−J})`, so every word frequency should exist
and be computable as a limit of periodic frequencies.  Confidence 85%.  A proof would make
`S_{b,r}` the first explicit arithmetic constant with a complete, non-uniform word-frequency law.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

open Classical in
/-- Every word has a limiting frequency in the base-`b` expansion of `powerLambert b r`. -/
def PowerLambertFrequenciesExist (b r : ℕ) : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ f : ℝ,
    Tendsto (fun N : ℕ =>
      (((range N).filter (fun n => OccursAt b (powerLambert b r) w n)).card : ℝ) / N)
      atTop (𝓝 f)

end NormalNumbers.ArithmeticDisjunctivity
