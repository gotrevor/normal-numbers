/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassRandomLambertMoment

/-!
# Random Erdős–Borwein subseries: the positive side (below exponent `ln 2`)

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 7eb1c8f3
(namespace relocated).  Paper-accepted by codex2 at 95% (mail 20261012T052349Z).  Paper argument:
`nn-erdos-borwein-random-2026-10-12.md`, section "Below ln 2".  LOCAL-ONLY branch.

The frozen headline `ebRandom_ae_normal_below_ln2` has no Hardy–Ramanujan hypothesis.  Per the
literature-as-hypothesis policy, this module proves the CONDITIONAL companion
`ebRandom_ae_normal_below_ln2_of_HR`, which takes the named input `HardyRamanujanLowerTail`.  The
unconditional headline stays in the packet until Hardy–Ramanujan itself is formalized.

Reusable, already proved in `NormalNumbers.CoefmassRandomLambertMoment` (general modulus `p`, no
primality): `anchor_phase_formula`, `anchor_tail_cos_le`, `cos_two_pi_le_of_near_rational`,
`bernMod_*`, `ePh_*`, `weylMean_even_expansion`.  The Bernoulli integral lemmas there are
`Prime`-indexed; port them to `ℕ` indices (`integral_ePh_finset_sum`,
`norm_integral_ePh_finset_sum`, `norm_integral_ePh_add_randomLambert_le`).
-/

namespace NormalNumbers.ErdosBorweinPositive

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

/-- Literature input: the lower-tail consequence of the classical Hardy–Ramanujan inequality, via
the Poisson–Chernoff bound.  The source inequality is displayed as (1) in Fan, arXiv:2508.06005v3.
This is a named hypothesis, not an axiom (codex2). -/
def HardyRamanujanLowerTail : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ q : ℝ,
    0 < q → q < 1 - α + α * Real.log α →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (((Finset.Icc 1 N).filter (fun n =>
        (n.primeFactors.card : ℝ) ≤ α * Real.log (Real.log N))).card : ℝ) ≤
          C * N * Real.rpow (Real.log N) (-q)

/-- All fixed positive integer moments of the shifted gcd divisor count are bounded (codex2,
95%).  Dominate `τ(gcd)^r` by `Σ_{d ∣ gcd} τ(d)^r`, count simultaneous divisibility
(`≤ 9/d²`), and sum `Σ τ(d)^r/d² < ∞`. -/
theorem shifted_gcd_divisor_moment (u v r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r)) ≤ C * (N : ℝ)^2 := by
  sorry

noncomputable def weylMean (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^n * (x : ℂ))) / N

/-- The summable moment bound behind `ebRandom_ae_normal_below_ln2` (codex2, 95%).
1. With `α ln 2 > a`, fix `k` and `q < Q(α)` with `kq > 1`.
2. The event that all coordinates have poor mass has probability `p_N^{2k} = O((log N)^{-2kq})`.
3. Shared-divisor loss decays at every log-power, by `shifted_gcd_divisor_moment` and Markov at
   `R > 2kq/η`.
4. The remaining tuples contract by `exp(-c_b (log N)^η)`. -/
@[blueprint (title := "Divisor moments yield summable Weyl bounds below log 2")]
theorem eb_weyl_moment_decay (hHR : HardyRamanujanLowerTail)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a c : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m))
    (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ q C : ℝ, 2 < q ∧ 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∫ w, ‖weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        C * Real.rpow (Real.log N) (-q) := by
  sorry

/-- **Conditional headline** (new companion, 2026-10-12; the frozen unconditional
`ebRandom_ae_normal_below_ln2` is NOT weakened).  Identical conclusion, plus the named literature
input `HardyRamanujanLowerTail`.  Proof:
1. `eb_weyl_moment_decay` gives, for each `b, h ≠ 0`, a fixed `k` and `q > 2` with
   `E|A_N|^{2k} ≤ C (log N)^{-q}`.
2. Markov at each rational `ε > 0`, then Borel–Cantelli along `N_j = ⌊exp √j⌋`
   (`Σ j^{-q/2} < ∞`).
3. Interpolate: `|A_N - A_{N_j}| ≤ 2(N - N_j)/N` and `N_{j+1}/N_j → 1`.
4. Take a countable intersection over `b, h, ε`, then Weyl → normality
   (`NormalNumbers.isNormal_of_weylAvg`, QSpanCriterion). -/
theorem ebRandom_ae_normal_below_ln2_of_HR (hHR : HardyRamanujanLowerTail)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a c : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinPositive
