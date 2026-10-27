/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertStatement
import NormalNumbers.SwingC2
import Architect

/-!
# Arithmetic hypotheses for a generic disjunctivity construction

The hypotheses concern coefficient arithmetic only: multiplicativity, an
ordinary-divisor bound, and prime-power values uniform in the prime.
They contain no digit-visitation or tail-selection assumption.
See `docs/square-lambert-proposal.md` for the initial application.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- A sufficient coefficient class.  Positive prime values are one or two
under the divisor bound; their uniformity is part of the hypothesis.  The
prime-power exponent may depend on the requested coefficient, but is chosen
before the prime. -/
structure CoefficientSystem (f : ℕ → ℕ) : Prop where
  zero : f 0 = 0
  one : f 1 = 1
  mul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n
  bound : ∀ n : ℕ, f n ≤ SwingC2.tau n
  prime : ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ ∀ p : ℕ, p.Prime → f p = d
  values : ∀ A : ℕ, 2 ≤ A → ∃ e : ℕ, 1 ≤ e ∧ ∀ p : ℕ, p.Prime → f (p ^ e) = A

/-- One arithmetic coefficient sequence evaluated at reciprocal integer bases. -/
noncomputable def coefficientValue (f : ℕ → ℕ) (b : ℕ) : ℝ :=
  ∑' n : ℕ, (f n : ℝ) / (b : ℝ) ^ n

/-- Prescribed words in finitely many *different constants*, at one common
arbitrarily late position.  This does not assert absolute disjunctivity of
one fixed number. -/
def JointCoefficientWords (f : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ lengths values : ℕ → ℕ,
    (∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ b ∈ S,
        ⌊(b : ℝ) ^ lengths b * orbit b (coefficientValue f b) n⌋ = (values b : ℤ)

/-- Frozen generic target.  Each assumption is independent of the desired
words.  A proof must construct the progression and control carries. -/
@[blueprint (title := "Generic simultaneous disjunctivity from multiplicative coefficient arithmetic")]
def GenericArithmeticDisjunctivity : Prop :=
  ∀ f : ℕ → ℕ, CoefficientSystem f → ∀ S : Finset ℕ,
    (∀ b ∈ S, 2 ≤ b) → JointCoefficientWords f S

end NormalNumbers.ArithmeticDisjunctivity
