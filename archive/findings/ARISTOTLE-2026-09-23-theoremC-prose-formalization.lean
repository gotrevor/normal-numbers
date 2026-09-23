import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Normality in base 4 of the constant `c_P`

Formalization of the following statement.

Fix a base-4 setting.  Let `P` be a set of prime numbers (a decidable predicate on `ℕ`;
only its prime members matter).  Assume

* (a) the "square-root fresh reciprocal mass" of `P` vanishes: as `N → ∞`, the sum of
  `1/p` over the primes `p ∈ P` with `√N < p ≤ N` tends to `0`;
* (b) the reciprocals of the primes in `P` diverge (the family `1/p` is not summable).

Let `c_P = ∑_{m ≥ 0} (number of primes of P dividing m) / 4 ^ m`.

Then `c_P` is normal in base 4.
-/

namespace ThmC

/-- The number of primes belonging to `P` that divide `m`.
(For `m = 0` this is `0`, since `Nat.primeFactors 0 = ∅`.) -/
def primeDivisorCount (P : ℕ → Prop) [DecidablePred P] (m : ℕ) : ℕ :=
  (m.primeFactors.filter P).card

/-- The constant `c_P = ∑_{m ≥ 0} ω_P(m) / 4 ^ m`. -/
noncomputable def cP (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ∑' m : ℕ, (primeDivisorCount P m : ℝ) / 4 ^ m

/-- The `i`-th base-4 digit of (the fractional part of) a real number `x`,
namely `d_i = ⌊frac x * 4 ^ (i+1)⌋ mod 4`. -/
noncomputable def digit4 (x : ℝ) (i : ℕ) : ℕ :=
  (⌊Int.fract x * 4 ^ (i + 1)⌋).toNat % 4

/-- The number of occurrences (overlapping occurrences counted separately) of the word `w`
as a contiguous block of base-4 digits starting at a position `i < n`. -/
noncomputable def occCount (x : ℝ) (w : List (Fin 4)) (n : ℕ) : ℕ :=
  ((Finset.range n).filter
    (fun i => ∀ j : Fin w.length, digit4 x (i + (j : ℕ)) = ((w.get j : Fin 4) : ℕ))).card

/-- `x` is normal in base 4: for every nonempty finite word `w` over `{0,1,2,3}`, the
frequency of occurrences of `w` among the first `n` base-4 digits of `x` tends to
`4 ^ (-|w|)`. -/
def IsNormalBase4 (x : ℝ) : Prop :=
  ∀ w : List (Fin 4), w ≠ [] →
    Filter.Tendsto (fun n : ℕ => (occCount x w n : ℝ) / n) Filter.atTop
      (nhds ((4 : ℝ) ^ (-(w.length : ℤ))))

/-- **Theorem C.**  If the reciprocal mass of the "fresh" primes of `P` in `(√N, N]`
tends to `0`, and the reciprocals of the primes of `P` diverge, then the constant
`c_P = ∑_{m ≥ 0} ω_P(m) / 4 ^ m` is normal in base 4. -/
theorem cP_isNormalBase4 (P : ℕ → Prop) [DecidablePred P]
    (hfresh : Filter.Tendsto
      (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N).filter
          (fun p => Nat.Prime p ∧ P p ∧ Real.sqrt N < p), (1 : ℝ) / p)
      Filter.atTop (nhds 0))
    (hdiv : ¬ Summable (fun p : {p : ℕ // Nat.Prime p ∧ P p} => (1 : ℝ) / (p : ℕ))) :
    IsNormalBase4 (cP P) := by
  sorry

end ThmC
