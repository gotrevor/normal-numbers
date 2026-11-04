/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDisjunctivity
import NormalNumbers.PowerLambertExpansion
import NormalNumbers.SquareLambertProposal

/-!
# Disjunctivity of Lambert series indexed by perfect powers

The generic coefficient theorem applies to the count of `r`-th-power
divisors.  The series identity then gives the arithmetic Lambert family.
For different bases these are different constants; no assertion of
absolute disjunctivity of a fixed member is made.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- Lambert series indexed by positive perfect `r`-th powers. -/
noncomputable def powerLambert (b r : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1)

/-- Every perfect-power-indexed Lambert series is disjunctive in its
defining integer base. -/
@[blueprint (title := "Perfect-power Lambert series are disjunctive in their defining bases")]
theorem isDisjunctive_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) :
    IsDisjunctive b (powerLambert b r) := by
  unfold powerLambert
  rw [powerLambert_eq_coefficientValue hb hr]
  exact isDisjunctive_coefficientValue _ (powerDivisorCount_system r hr) b hb

/-- For fixed `r`, any finitely many bases admit prescribed words at one
common arbitrarily late position in their respective Lambert constants. -/
@[blueprint (title := "Simultaneous word visits for perfect-power Lambert constants")]
theorem jointPowerLambertWords (r : ℕ) (hr : 1 ≤ r)
    (S : Finset ℕ) (hb : ∀ b ∈ S, 2 ≤ b) :
    ∀ lengths values : ℕ → ℕ,
      (∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ b ∈ S,
        ⌊(b : ℝ) ^ lengths b * orbit b (powerLambert b r) n⌋ = (values b : ℤ) := by
  intro lengths values hwin N
  obtain ⟨n, hn, hw⟩ := jointCoefficientWords (powerDivisorCount r)
    (powerDivisorCount_system r hr) S hb lengths values hwin N
  refine ⟨n, hn, fun b hbS => ?_⟩
  unfold powerLambert
  rw [powerLambert_eq_coefficientValue (hb b hbS) hr]
  exact hw b hbS

/-- The specific square-Lambert target from the original proposal. -/
@[blueprint (title := "The binary square-Lambert disjunctivity target")]
theorem squareLambertBinaryDisjunctive :
    SquareLambertProposal.SquareLambertBinaryDisjunctive := by
  exact isDisjunctive_powerLambert 2 2 (by omega) (by omega)

/-- The original proposal's witness gate is the exponent-two instance
of the generic exact-valuation construction. -/
theorem squareLambertWitnessSupply : SquareLambertProposal.SquareLambertWitnessSupply := by
  intro a r ha hr ε hε K N
  exact JointLambert.exists_exact_valuation_small_tail 2 (2 * (a - 1)) r
    (by omega) (by omega) hr hε K N

/-- The original square-series regrouping obligation. -/
theorem squareLambertExpansion : SquareLambertProposal.SquareLambertExpansion := by
  intro b hb
  exact powerLambert_eq_coefficientValue hb (by omega : 1 ≤ 2)

/-- Multiplicativity and the prime-power rule from the original proposal. -/
theorem squareCoefficientArithmetic : SquareLambertProposal.SquareCoefficientArithmetic := by
  constructor
  · exact (powerDivisorCount_system 2 (by omega)).mul
  · intro p e hp
    exact powerDivisorCount_primePow 2 e (by omega) hp

/-- The factorization formula for square-divisor coefficients. -/
theorem squareCoefficientFactorization : SquareLambertProposal.SquareCoefficientFactorization := by
  intro n hn
  change powerDivisorCount 2 n = _
  have hf := powerDivisorCount_system 2 (by omega)
  rw [Nat.multiplicative_factorization (powerDivisorCount 2) hf.mul hf.one (by omega : n ≠ 0),
    Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  exact powerDivisorCount_primePow 2 (n.factorization p) (by omega)
    (Nat.prime_of_mem_primeFactors hp)

/-- A single prime-power slot realizes every positive integer coefficient. -/
theorem squareSingleWriter : SquareLambertProposal.SquareSingleWriter := by
  intro a p q ha hp hq hpq
  change powerDivisorCount 2 (q ^ (2 * (a - 1)) * p) = a
  have hf := powerDivisorCount_system 2 (by omega)
  rw [hf.mul _ _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).2 hpq.symm)),
    powerDivisorCount_primePow 2 _ (by omega) hq]
  have hpv : powerDivisorCount 2 p = 1 := by
    simpa using powerDivisorCount_primePow 2 1 (by omega) hp
  rw [hpv, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  omega

/-- Each prime with exact exponent two supplies one factor two. -/
theorem squareLocalKill : SquareLambertProposal.SquareLocalKill := by
  intro p m hp hcop
  change powerDivisorCount 2 (p ^ 2 * m) = 2 * powerDivisorCount 2 m
  rw [(powerDivisorCount_system 2 (by omega)).mul _ _ (hcop.pow_left _),
    powerDivisorCount_primePow 2 2 (by omega) hp]

/-- The original square-coefficient and tail supply is now unconditional. -/
theorem squareLambertWindowSupply : SquareLambertProposal.SquareLambertWindowSupply := by
  intro a r ha hr ε hε K N
  obtain ⟨k, n, hk, hkr, hn, hN, hvals, hwriter, htail⟩ :=
    squareLambertWitnessSupply a r ha hr ε hε K N
  refine ⟨k, n, hk, hkr, hn, hN, ?_, ?_, htail⟩
  · intro j hj hjr
    obtain ⟨P, hcard, hP⟩ := hvals j hj hjr
    have hdiv := pow_card_dvd_of_exact_valuations
      (powerDivisorCount_system 2 (by omega)) (by omega : 0 < n + j) (by omega : 1 ≤ 2)
      P hP (fun p hp => by simpa using powerDivisorCount_primePow 2 2 (by omega) hp)
    simpa only [hcard, powerDivisorCount, SquareLambertProposal.squareDivisorCount] using hdiv
  · obtain ⟨p, q, hp, hq, hpq, heq⟩ := hwriter
    rw [heq]
    exact squareSingleWriter a p q (by omega) hp hq hpq

/-- The original conditional interface follows from the unconditional
specialization; its premises no longer represent a gap. -/
theorem squareLambertTransfer : SquareLambertProposal.SquareLambertTransfer := by
  intro _ _
  exact squareLambertBinaryDisjunctive

end NormalNumbers.ArithmeticDisjunctivity
