/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertFrequenciesExist
import NormalNumbers.PowerLambertPeriodicApprox

/-!
# The word-frequency law of a perfect-power Lambert constant is computable

`powerLambertFrequenciesExist` gives every word `w` a limiting frequency `powerLambertFreq b r w`.
This file pins it down: it is the limit, along `Q_D = (D!)^r`, of the frequencies of the
`Q_D`-periodic model `n ↦ {periodicTail b r Q_D n}` (a finite computation for each `D`), and
packages the three properties of the constant: rich, every word frequency exists, not normal.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

open Classical in
/-- The limiting frequency of the word `w` in the base-`b` expansion of `powerLambert b r`
(its existence is `powerLambertFrequenciesExist`). -/
noncomputable def powerLambertFreq (b r : ℕ) (w : List ℕ) : ℝ :=
  limUnder atTop fun N : ℕ =>
    (((range N).filter fun n => OccursAt b (powerLambert b r) w n).card : ℝ) / N

open Classical in
/-- The frequency of the cylinder of `w` in the `Q`-periodic model: the share of `n < Q` whose
periodic orbit point `{periodicTail b r Q n}` lies in `[W/b^ℓ, (W+1)/b^ℓ)`. -/
noncomputable def periodicModelFreq (b r Q : ℕ) (w : List ℕ) : ℝ :=
  (((range Q).filter fun n => Int.fract (periodicTail b r Q n) ∈
      Set.Ico ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length)).card : ℝ) / Q

/-- **Frozen (2026-11-04).**  The word frequency is the limit of the periodic-model frequencies
along `Q_D = (D!)^r`: the law is computable. -/
theorem powerLambertFreq_eq_lim (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) :
    Tendsto (fun D : ℕ => periodicModelFreq b r (D.factorial ^ r) w) atTop
      (𝓝 (powerLambertFreq b r w)) := by
  sorry

/-- **Frozen (2026-11-04).**  The three properties together: `Σ_{n≥1} 1/(b^{n^r} − 1)` is rich,
has a limiting frequency for every word, and is not normal. -/
theorem powerLambert_frequency_law (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) ∧ PowerLambertFrequenciesExist b r ∧
      ¬ IsNormal b (powerLambert b r) := by
  sorry

end NormalNumbers.ArithmeticDisjunctivity
