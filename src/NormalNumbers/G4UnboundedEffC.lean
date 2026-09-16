/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedAvg
import NormalNumbers.G4SchedOmega

/-!
# Campaign B, step B2e: the effective constant in closed form

`effC c P₀ A = max (A + frozenHarm c P₀) (cMax c P₀)` is what the tame §4D pays instead of
`max C 1`.  Both branches are controlled by the single quantity `cMax c P₀ = max_{p∣P₀} c_p`:
the harmonic branch is `cMax` times `∑_{p∣P₀} 1/(p−1) ≤ 1 + log ω(P₀)`
(`G4SchedOmega.sum_inv_sub_one_primeFactors_le_log`).  So the schedule only ever has to beat

    `A + (max_{p∣P₀} c_p) · (1 + log ω(P₀))`,

a quantity that for `c_p = O(polylog p)` is polynomial in `k₄` — see
`DESIGN-2026-09-16-prime-subset.md`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

/-! ### B2e: `effC` in closed form — largest coefficient times `log log` -/

/-- `cMax` from a pointwise bound on the primes dividing `P₀`. -/
lemma cMax_le {c : ℕ → ℕ} {P₀ V : ℕ} (h : ∀ p ∈ P₀.primeFactors, c p ≤ V) :
    cMax c P₀ ≤ (V : ℝ) := by
  unfold cMax
  exact_mod_cast Finset.sup_le h

/-- **The harmonic branch of `effC` is `cMax` times a `log log`.**  `∑_{p∣P₀} c_p/(p−1)
≤ (max_{p∣P₀} c_p) · ∑_{p∣P₀} 1/(p−1) ≤ cMax · (1 + log ω(P₀))`. -/
lemma frozenHarm_le_cMax_mul (c : ℕ → ℕ) (P₀ : ℕ) :
    frozenHarm c P₀ ≤ cMax c P₀ * (1 + Real.log (P₀.primeFactors.card)) := by
  have hstep : frozenHarm c P₀ ≤ cMax c P₀ * ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    rw [Finset.mul_sum]
    unfold frozenHarm
    refine Finset.sum_le_sum fun p hp => ?_
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hle : (c p : ℝ) ≤ cMax c P₀ := by
      unfold cMax
      exact_mod_cast Finset.le_sup (f := c) hp
    rw [mul_one_div]
    gcongr
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (cMax_nonneg c P₀))
  exact sum_inv_sub_one_primeFactors_le_log P₀

/-- **`effC` in closed form.**  Everything the schedule has to beat is `A` plus the largest
coefficient on a prime dividing `P₀`, times a `log log`. -/
lemma effC_le_closed {c : ℕ → ℕ} {A : ℝ} (hA : 1 ≤ A) (P₀ : ℕ) :
    effC c P₀ A ≤ A + cMax c P₀ * (1 + Real.log (P₀.primeFactors.card)) := by
  have hh := frozenHarm_le_cMax_mul c P₀
  have hc0 := cMax_nonneg c P₀
  have hlog : (0 : ℝ) ≤ Real.log (P₀.primeFactors.card) := Real.log_natCast_nonneg _
  refine max_le (by linarith) ?_
  nlinarith

end NormalNumbers.G4
