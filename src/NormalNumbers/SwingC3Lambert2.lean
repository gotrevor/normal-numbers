/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Subset

/-!
# The crux's constant in closed form

`SwingC3Lambert.fract_tailLarge_eq_orbit` already identifies the large-prime tail with the `×b`
orbit of the single real number `largeLambert P b = ∑_n ω_{>P}(n) b^{−n}`.  What was missing is
what that number *is*.  The closed form of `SwingC3Closed` at `n = 0` supplies it: it is a
**Lambert series restricted to the large primes**,

    largeLambert P b  =  ∑_{p > P prime}  1/(b^p − 1).

So the crux `AddCharTail` is a classical twisted Weyl sum

    (1/N) ∑_{n<N} e(jn/Q) · e(h · b^n · ∑_{p>P} 1/(b^p − 1))  →  0,

for an explicit, literature-checkable constant — the tail of the prime Lambert number
`∑_p 1/(b^p − 1)` (the base-`b` "prime characteristic" constant).  Checking `P = 0` recovers the
classical identity `∑_n ω(n) b^{−n} = ∑_p 1/(b^p − 1)`.
-/

open Finset

namespace NormalNumbers

open PrimeLambert

/-- The large-prime Lambert number is the tail at `0` (the `n = 0` digit is `0`). -/
theorem largeLambert_eq_tailLarge_zero {b : ℕ} (hb : 2 ≤ b) (P : ℕ) :
    largeLambert P b = tailLarge P b 0 := by
  have hzero : omegaLarge P 0 = 0 := by simp [omegaLarge]
  have h0 : tailOf b (omegaLarge P) 0 = largeLambert P b := by
    rw [largeLambert, lambertOf, tailOf]
    rw [(summable_lambertOf hb (omegaLarge_le_omegaR P)).tsum_eq_zero_add]
    rw [hzero]
    simp
  rw [← h0]
  rfl

/-- **The closed form of the crux's constant.**  `largeLambert P b = ∑_{p>P} 1/(b^p − 1)`. -/
theorem largeLambert_eq_tsum {b : ℕ} (hb : 2 ≤ b) (P : ℕ) :
    largeLambert P b = ∑' p : ℕ, (if P < p ∧ p.Prime then 1 / ((b : ℝ) ^ p - 1) else 0) := by
  rw [largeLambert_eq_tailLarge_zero hb P, tailLarge_eq_tsum hb P 0]
  refine tsum_congr fun p => ?_
  by_cases hp : P < p ∧ p.Prime
  · rw [if_pos hp, if_pos hp, tailPrimeTerm]
    norm_num
  · rw [if_neg hp, if_neg hp]

/-- **The crux's exponential is the `×b` orbit of the explicit constant.**  `tailLarge P b n` and
`b^n · largeLambert P b` differ by an integer, so the twisted Weyl sum of `AddCharTail` is the
twisted Weyl sum of `largeLambert P b`. -/
theorem ee_tailLarge_eq_ee_orbit {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) (h : ℤ) :
    ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
      = ee (((h : ℝ) * (largeLambert P b * (b : ℝ) ^ n) : ℝ) : ℂ) := by
  have hfr : Int.fract (tailLarge P b n) = Int.fract (largeLambert P b * (b : ℝ) ^ n) := by
    rw [fract_tailLarge_eq_orbit hb P n, orbit]
  set z : ℤ := ⌊largeLambert P b * (b : ℝ) ^ n⌋ - ⌊tailLarge P b n⌋ with hz
  have hdiff : largeLambert P b * (b : ℝ) ^ n = tailLarge P b n + (z : ℝ) := by
    have h1 := Int.floor_add_fract (tailLarge P b n)
    have h2 := Int.floor_add_fract (largeLambert P b * (b : ℝ) ^ n)
    rw [hz]
    push_cast
    rw [← hfr] at h2
    linarith [h1, h2]
  have hstep : ((h : ℝ) * (largeLambert P b * (b : ℝ) ^ n) : ℝ)
      = ((h : ℝ) * tailLarge P b n : ℝ) + ((h * z : ℤ) : ℝ) := by
    rw [hdiff]; push_cast; ring
  rw [hstep, Complex.ofReal_add, Complex.ofReal_intCast, ee_add, ee_int, mul_one]

/-! ### The swing's conditional, in its sharpest form -/

open Filter Topology

namespace CastingOut

/-- **The crux as a twisted Weyl sum for one explicit constant.**  For every `P`, the `×b` orbit
of `L_P = ∑_{p>P} 1/(b^p − 1)` does not correlate with any nontrivial additive character mod a
modulus `Q` built from the small primes. -/
def WeylLambertTwist (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * ee (((h : ℝ) * (largeLambert P b * (b : ℝ) ^ n) : ℝ) : ℂ)) / N) atTop (𝓝 0)

theorem addCharTail_of_weylLambertTwist {b : ℕ} (hb : 2 ≤ b) (H : WeylLambertTwist b) :
    AddCharTail b := by
  intro P Q j h hQ hj0 hjQ
  have := H P Q j h hQ hj0 hjQ
  refine this.congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [ee_tailLarge_eq_ee_orbit hb P n h]

/-- **`ConjC3` from a single Weyl-type statement about the explicit constants `L_P`.** -/
theorem conjC3_of_weylLambertTwist (H : ∀ b, 3 ≤ b → WeylLambertTwist b) : ConjC3 :=
  conjC3_of_addCharTail fun b hb =>
    addCharTail_of_weylLambertTwist (by omega) (H b hb)

end CastingOut

end NormalNumbers
