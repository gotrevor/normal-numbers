/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinEndpoint

/-!
# The Erdős–Borwein endpoint `a = ln 2`, Step 2 and assembly (FDEK-conditional)

Statements copied verbatim from the KB packet `NNErdosBorweinRandom.lean`.  The growing-moment
criterion `ebRandom_ae_normal_of_divisorVariance_diverges` is proved in
`CoefmassErdosBorweinEndpoint.lean`.  This file owes Step 2, divergence of the variance divisor
mass at the endpoint given finite-dimensional Erdős–Kac (a named literature hypothesis, not an
axiom), and the assembly.  Paper: `nn-erdos-borwein-random-2026-10-12.md`, "Step 2".
-/

namespace NormalNumbers.ErdosBorweinEndpointEK

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint

/-- The power family `δ_m = min(1/2, (log m)^{-a})` (and `1/2` for `m < 3`). -/
noncomputable def powerDelta (a : ℝ) (m : ℕ) : ℝ :=
  if m < 3 then 1 / 2 else min (1 / 2) (Real.rpow (Real.log m) (-a))

/-- **Candidate positive answer on the unresolved range** (renamed from `EBPowerThresholdOpen` on
2026-10-12, before any use; the statement is unchanged).  For the power family:
* `a > ln 2`: a.s. non-normal (`ebRandom_ae_not_normal`).
* `0 ≤ a < ln 2`: a.s. normal (`ebRandom_ae_normal_below_ln2`, with `c = (log 2)^a/4`).
So the only unresolved case of this Prop is the endpoint `a = ln 2`, where it is the PROPOSED positive
answer.  It is a candidate, not a claim, and its literature status is unverified. -/
def EBPowerCandidateNormal : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Bool), BernoulliLawNat μ (powerDelta a) X →
      ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w)

/-- `ω` restricted to primes `p ≤ y`. -/
noncomputable def omegaUpTo (y : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card

/-- Finite-dimensional law of Brownian motion at times `t 1 < … < t R` (with `t 0 = 0`), as the
image of independent Gaussian increments under partial summation. -/
noncomputable def brownianFDD (R : ℕ) (t : Fin (R + 1) → ℝ) : Measure (Fin R → ℝ) :=
  (Measure.pi (fun j : Fin R =>
      gaussianReal 0 (Real.toNNReal (t j.succ - t j.castSucc)))).map
    (fun y j => ∑ i ∈ Finset.univ.filter (fun i : Fin R => i ≤ j), y i)

open Classical in
/-- Literature input: finite-dimensional Erdős–Kac, in portmanteau (closed-set upper bound) form.
For `n` uniform in `[1, N]`, `((ω(n; ≤ exp((log N)^{t_j})) - t_j log log N)/√(log log N))_j`
converges in law to `(B_{t_j})_j`.  Standard via the Kubilius model or the moment method plus
Cramér–Wold.  It is a special case of Billingsley's functional limit theorem (Ann. Probab. 2 (1974)
749–791; theorem number unverified).  A named hypothesis, not an axiom. -/
def ErdosKacFiniteDim : Prop :=
  ∀ R : ℕ, ∀ t : Fin (R + 1) → ℝ, StrictMono t → t 0 = 0 → t (Fin.last R) ≤ 1 →
    ∀ F : Set (Fin R → ℝ), IsClosed F → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (((Finset.Icc 1 N).filter (fun n =>
          (fun j : Fin R =>
            ((omegaUpTo (Real.exp (Real.log N ^ t j.succ)) n : ℝ) -
                t j.succ * Real.log (Real.log N)) /
              Real.sqrt (Real.log (Real.log N))) ∈ F)).card : ℝ) / N ≤
          (brownianFDD R t F).toReal + ε

/-- **The divisor variance mass diverges at the endpoint.**  Chain bound: for a prime `p ∣ n+a₀`
with `P₀ < p`, the `2^{t-1}` divisors `p·d'` (with `t = ω(n+a₀; ≤ p)`) give
`W ≥ (c/2) exp(ln 2 (t - log log p) - ln 2 · ln t)`.  So `W ≤ T` caps the walk
`ω(n+a₀; ≤ e^{e^u}) - u` by `O(log log log N) = o(√(log log N))` at every jump.  FDEK on refining
grids and `P(sup_{(0,1-η]} B ≤ 0) = 0` finish. -/
theorem divisorVariance_diverges_at_ln2 (hEK : ErdosKacFiniteDim)
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    (a₀ : ℕ) (T : ℝ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + a₀) ≤ T)).card : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

/-- **Normal at and below `ln 2`.**  `δ_m(1-δ_m) ≥ c (log m)^{-ln 2}` gives a.s., for each `b`, base-`b` normality of `E_b` (one number per base, not absolute normality).
Below `ln 2` is a literal corollary (for `m ≥ 3`, `(log m)^{-a} ≥ (log m)^{-ln 2}`), so this
supersedes the Hardy–Ramanujan route of `ebRandom_ae_normal_below_ln2`, given FDEK. -/
@[blueprint (title := "Random Erdős–Borwein subseries are normal at exponent ln 2")]
theorem ebRandom_ae_normal_le_ln2_of_EK (hEK : ErdosKacFiniteDim)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c : ℝ) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-Real.log 2) ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

/-- The candidate positive answer holds, given FDEK.  For `0 < a ≤ ln 2` and `m ≥ 3`,
`powerDelta a m (1 - powerDelta a m) ≥ (1/4)(log m)^{-ln 2}`.  At `m = 2` the variance is `1/4`, so
`c = 1/8` works throughout. -/
theorem ebPowerCandidateNormal_of_EK (hEK : ErdosKacFiniteDim) : EBPowerCandidateNormal := by
  sorry



end NormalNumbers.ErdosBorweinEndpointEK
