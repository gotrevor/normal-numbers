/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs

/-!
# Random Erdős–Borwein subseries: the negative side (above exponent `ln 2`)

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 7eb1c8f3
(namespace relocated).  Paper-accepted by codex2 at 95% (mail 20261012T051355Z).  Paper argument:
`nn-erdos-borwein-random-2026-10-12.md`, section "Marginal-only proof".  LOCAL-ONLY branch.

Recommended order: `largeDivisorMass_moment_small` → `typicalDivisorMass_small` (Markov) →
`ebRandom_ae_not_normal_of_marginal_bound` → `ebRandom_ae_not_normal` (marginals of a
`BernoulliLawNat` satisfy the marginal bound; `C ≥ 0` from `m = 2`).
-/

namespace NormalNumbers.ErdosBorweinRandom

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Independent Bernoulli selections of positive integers (index `0` unused). -/
def BernoulliLawNat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ m, 0 ≤ delta m ∧ delta m ≤ 1) ∧
  (∀ m, Measurable (X m)) ∧ iIndepFun X μ ∧
    ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)

/-- The random Erdős–Borwein subseries `Σ_{m ≥ 1, X_m} 1/(b^m - 1)`. -/
noncomputable def ebLambert {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool) (w : Ω) : ℝ :=
  ∑' m : ℕ, (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)

/-- Weighted large-divisor mass `Σ_{d ∣ n, d > M} (log d)^{-a}`. -/
noncomputable def largeDivisorMass (a : ℝ) (M n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => M < d), Real.rpow (Real.log d) (-a)

/-- **Typical divisor mass is small above `ln 2`.**  Dyadic blocks in `log d`.  The divisors
`d ≤ y` of `n` divide the `y`-smooth part `n_y`, so their number is at most `τ(n_y)`.  Use
`(1/N) Σ_{n ≤ N} τ(n_y)^s ≤ ∏_{p ≤ y}(1 + (2^s-1)/p + O(p^{-2})) ≤ C (log y)^{2^s-1}`, which needs
only an upper Mertens bound.  Markov at level `ε·2^{j(a-η)}` on block `j`, with `log y_j = 2^{j+1}`,
gives a geometric series exactly when `a - η > (2^s-1)/s`, and `(2^s-1)/s → ln 2` as `s → 0⁺`. -/
theorem typicalDivisorMass_small (a : ℝ) (ha : Real.log 2 < a) (ε η : ℝ) (hε : 0 < ε)
    (hη : 0 < η) :
    ∃ M : ℕ, ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => ε < largeDivisorMass a M n)).card : ℝ) ≤ η * N := by
  sorry

/-- **Non-normality beyond finite mass.**  Paper proof:
1. Remove the rational head `m ≤ M`.
2. `frac(b^n Y_M) ≤ 2 Σ_{j ≥ 1} b^{-j} d_{S,M}(n+j)`, since `α_m(n) = b^{m-j}/(b^m-1)` with
   `m ∣ n+j`.
3. `E_X 1[d_{S,M}(n) ≥ 1] ≤ C · largeDivisorMass a M n`; the `j > J` tail is handled by the typical
   bound plus Markov in `X`.
4. So `E_X` of the density of `{n ≤ N : frac ≥ ε'}` is small, uniformly in `N`.
5. Fatou gives non-normality with positive probability.  Normality is a tail event (finite changes
   are rational shifts, Wall), so Kolmogorov's 0-1 law makes it almost sure. -/
@[blueprint (title := "Random Erdős–Borwein subseries are non-normal above exponent ln 2")]
theorem ebRandom_ae_not_normal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a C : ℝ) (ha : Real.log 2 < a)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * Real.rpow (Real.log m) (-a)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

/-- Uniform vanishing fractional moment of the large-divisor mass.  Choose `0 < s ≤ 1` with
`q = 2^s - 1 < a s`.  `τ(n_y)^s = 1 * g_y` with `g_y ≥ 0`, so for EVERY `T`,
`(1/T) Σ_{n ≤ T} τ(n_y)^s ≤ ∏_{p ≤ y}(1 + q/p + 1/(p(p-1))) ≤ A_s (log y)^q`; prime powers are
retained.  Subadditivity of `t^s` over log-dyadic blocks gives
`(1/T) Σ μ_M^s ≤ A_s 2^q Σ_{ℓ ≥ L} 2^{-(as-q)ℓ} → 0`.  Implies `typicalDivisorMass_small` by Markov.
Paper confidence 95% (codex2); unproved in Lean. -/
theorem largeDivisorMass_moment_small (a : ℝ) (ha : Real.log 2 < a) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        (∑ n ∈ Finset.Icc 1 N, Real.rpow (largeDivisorMass a M n) s) ≤ ε * N := by
  sorry

/-- **Marginal decay alone forces non-normality** (strengthens `ebRandom_ae_not_normal`).
Proof outline:
1. Use the exact residual `R_M(n) = Σ_{j ≥ 1} b^{-j} D_M(n+j)`, with
   `D_M(t) = #{m > M selected : m ∣ t}`.  `b^n Y_M - R_M(n) ∈ ℤ`, so `frac ≤ R_M`.
2. By subadditivity and Jensen, `E[frac^s] ≤ C^s Σ_j b^{-js} μ_M(n+j)^s`.
3. Shifting by `j` costs at most `1+j`, which is summable against `b^{-js}`.
4. On the normality event the orbit average of `frac^s` tends to `1/(s+1)`.  Fatou then bounds
   `P(normal)` by a quantity that vanishes as `M → ∞`.
Paper confidence 95% (codex2); unproved in Lean. -/
@[blueprint (title := "Marginal decay alone forces random Erdős–Borwein non-normality")]
theorem ebRandom_ae_not_normal_of_marginal_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hMeas : ∀ m, Measurable (X m))
    (a C : ℝ) (ha : Real.log 2 < a) (hC : 0 ≤ C)
    (hMarginal : ∀ m : ℕ, 2 ≤ m →
      μ {w | X m w = true} ≤ ENNReal.ofReal (C * Real.rpow (Real.log m) (-a))) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinRandom
