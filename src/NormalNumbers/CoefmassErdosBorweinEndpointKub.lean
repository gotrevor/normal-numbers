/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinEndpointEK
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime

/-!
# The Erdős–Borwein endpoint `a = ln 2` without FDEK (Kubilius-model route)

Statements copied verbatim from the KB packet `NNErdosBorweinRandom.lean`.  The literature input is
`KubiliusTV` (a named hypothesis, not an axiom).  Mertens' second theorem is available proved:
`RS_prime.mertens_second_theorem'` (PrimeNumberTheoremAnd).  Step 1 (the growing-moment criterion)
is `ebRandom_ae_normal_of_divisorVariance_diverges`.  Plan: `EB-ENDPOINT-KUB-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinEndpointKub

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint
  NormalNumbers.ErdosBorweinEndpointEK

/-! ### An FDEK-free endpoint via the Kubilius model (personal-c5, 2026-10-25)

Replaces `ErdosKacFiniteDim`, whose theorem number is unverified, by the Kubilius-model
total-variation bound, whose citation is verified.  Ford, arXiv 2408.03803v4, Theorem A, quotes
Tenenbaum, Number Theory in Progress Vol. 2 (1999), pp. 1099–1129, Théorème 1.1 and (1.7):
`d_TV ≪_ε u^{-u} + x^{-1+ε}` for the prime-exponent vector, `p ≤ y ≤ x`, `u = log x / log y`.
`KubiliusTV` is its image under `v ↦ {p : v_p ≥ 1}` at `ε = 1/2`; TV only shrinks under a map.
On the model, the walk `ω(n; ≤ e^{e^u}) − u` is a sum of independent bounded variables, so the
Step 2 crossing needs no Gaussian limit (paper section "A route that replaces FDEK"). -/

/-- The primes `≤ y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

open Classical in
/-- Mass of `A` under the Kubilius model: each prime `p ≤ y` is included independently with
probability `1/p`. -/
noncomputable def kubiliusMass (y : ℕ) (A : Set (Finset ℕ)) : ℝ :=
  ∑ S ∈ (primesUpTo y).powerset,
    if S ∈ A then ∏ p ∈ primesUpTo y, (if p ∈ S then (1 / p : ℝ) else 1 - 1 / p) else 0

open Classical in
/-- Literature input: the Kubilius-model total-variation bound (Tenenbaum 1999, Théorème 1.1 and
(1.7), as quoted by Ford, arXiv 2408.03803v4, Theorem A), at `ε = 1/2`, projected to divisibility
indicators.  A named hypothesis, not an axiom. -/
def KubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y → y ≤ N → ∀ A : Set (Finset ℕ),
    |(((Finset.Icc 1 N).filter (fun n => n.primeFactors.filter (· ≤ y) ∈ A)).card : ℝ) / N -
        kubiliusMass y A| ≤
      C * (Real.rpow (Real.log N / Real.log y) (-(Real.log N / Real.log y)) +
        Real.rpow N (-(1 / 2 : ℝ)))

/-- **Step 2 from the Kubilius model** (FDEK-free).  Same conclusion as
`divisorVariance_diverges_at_ln2`. -/
theorem divisorVariance_diverges_at_ln2_of_kubilius (hK : KubiliusTV)
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    (a₀ : ℕ) (T : ℝ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + a₀) ≤ T)).card : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

/-- The candidate positive answer, FDEK-free: from the Kubilius model alone. -/
theorem ebPowerCandidateNormal_of_kubilius (hK : KubiliusTV) : EBPowerCandidateNormal := by
  sorry

end NormalNumbers.ErdosBorweinEndpointKub
