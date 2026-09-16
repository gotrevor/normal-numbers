/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaWitness
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Size arithmetic for the `Ω` schedule

The two `Ω`-specific §4D fields of `ScheduleWitnessΩ` (`hjunk`, `hfar`) are pure size
arithmetic in the schedule parameters.  The one non-obvious input is the frozen sum

  `T(P₀) = ∑_{p ∣ P₀} 1/(p−1)`,

which must be **log log**-size, not `ω(P₀)`-size: the junk term is multiplied by `rowL1 b K`,
which only decays like `(2/3)^K`, while `ω(P₀)` is super-exponential in `K`.  The saving is that
the `j`-th smallest prime factor is at least `j + 2`, so `T(P₀) ≤ harmonic ω(P₀) ≤ 1 + log ω(P₀)`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- A finset of positive naturals has reciprocal sum at most the harmonic number of its size:
the `j`-th smallest element is at least `j+1`. -/
theorem sum_inv_le_harmonic : ∀ (n : ℕ) (B : Finset ℕ), B.card = n → 0 ∉ B →
    ∑ k ∈ B, (1 : ℝ) / k ≤ (harmonic n : ℝ) := by
  sorry

/-- **`∑_{p ∣ N} 1/(p−1) ≤ harmonic ω(N)`.** -/
theorem sum_inv_sub_one_primeFactors_le (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ (harmonic N.primeFactors.card : ℝ) := by
  sorry

/-- The `log log` form. -/
theorem sum_inv_sub_one_primeFactors_le_log (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ 1 + Real.log (N.primeFactors.card) :=
  (sum_inv_sub_one_primeFactors_le N).trans (harmonic_le_one_add_log _)

end NormalNumbers.G4
