/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDisjunctivityDefs
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Finite arithmetic consequences of a coefficient system

These lemmas isolate the elementary multiplicative arithmetic used by the
generic construction.  They do not assert a digit-visitation result.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- Every coefficient value `2*a` can be forced at `q^E*p`, uniformly over
distinct primes `p,q`. -/
@[blueprint (title := "Uniform survivor exponent from prime-power coefficient values")]
theorem exists_survivor_exponent {f : ℕ → ℕ}
    (hf : CoefficientSystem f) (a : ℕ) (ha : 2 ≤ a) :
    ∃ E : ℕ, 1 ≤ E ∧ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      f (q ^ E * p) = 2 * a := by
  obtain ⟨d, hd, hprime⟩ := hf.prime
  rcases hd with hd1 | hd2
  · obtain ⟨E, hE, hvalues⟩ := hf.values (2 * a) (by omega)
    refine ⟨E, hE, ?_⟩
    intro p q hp hq hpq
    have hcop : Nat.Coprime (q ^ E) p := by
      simpa using Nat.coprime_pow_primes E 1 hq hp (Ne.symm hpq)
    rw [hf.mul (q ^ E) p hcop, hvalues q hq, hprime p hp, hd1]
    simp
  · obtain ⟨E, hE, hvalues⟩ := hf.values a ha
    refine ⟨E, hE, ?_⟩
    intro p q hp hq hpq
    have hcop : Nat.Coprime (q ^ E) p := by
      simpa using Nat.coprime_pow_primes E 1 hq hp (Ne.symm hpq)
    rw [hf.mul (q ^ E) p hcop, hvalues q hq, hprime p hp, hd2]
    omega

/-- A finite set of prime factors with the same exact valuation contributes
one factor of `C` apiece to the coefficient value. -/
@[blueprint (title := "Exact prime valuations give a coefficient divisibility factor")]
theorem pow_card_dvd_of_exact_valuations {f : ℕ → ℕ}
    (hf : CoefficientSystem f) {n e C : ℕ} (hn : 0 < n) (he : 1 ≤ e)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ n.factorization p = e)
    (hval : ∀ p : ℕ, p.Prime → f (p ^ e) = C) :
    C ^ P.card ∣ f n := by
  classical
  let g : ℕ → ℕ := fun p => f (p ^ n.factorization p)
  have hsubset : P ⊆ n.primeFactors := by
    intro p hpP
    have hnonzero : n.factorization p ≠ 0 := by
      rw [hP p hpP |>.2]
      omega
    have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hnonzero
    simpa only [Nat.support_factorization] using hmem
  have hfactor : f n = ∏ p ∈ n.primeFactors, g p := by
    rw [Nat.multiplicative_factorization f hf.mul hf.one (by omega : n ≠ 0)]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  have hPvalue : P.prod g = C ^ P.card := by
    calc
      P.prod g = P.prod (fun _ => C) := by
        apply Finset.prod_congr rfl
        intro p hpP
        dsimp [g]
        rw [hP p hpP |>.2]
        exact hval p (hP p hpP).1
      _ = C ^ P.card := by simp
  have hdiv : P.prod g ∣ f n := by
    rw [hfactor]
    exact Finset.prod_dvd_prod_of_subset P n.primeFactors g hsubset
  rw [hPvalue] at hdiv
  exact hdiv

/-- The divisor-bound hypothesis implies the elementary linear bound
`f(n) ≤ n`. -/
@[blueprint (title := "Coefficient systems are bounded by their input")]
theorem coefficient_le_self {f : ℕ → ℕ}
    (hf : CoefficientSystem f) (n : ℕ) : f n ≤ n :=
  le_trans (hf.bound n) (NormalNumbers.SwingC2.tau_le_self n)

end NormalNumbers.ArithmeticDisjunctivity
