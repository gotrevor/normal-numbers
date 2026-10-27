/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertTailBounds
import NormalNumbers.JointLambertArithmetic
import Architect

/-!
# Proposed target: the Lambert series over squares

Research proposal, 2026-10-27.  See `docs/square-lambert-proposal.md` and `MAZE.md`.
The open statements below are not established by this file.  The proved facts
are the divisor majorant, its tail consequence, and finite arithmetic controls.

The proposed mechanism extends the multiplicative coefficient construction for
Erdos--Borwein, not the additive prime-Lambert contraction.  The older exclusion
of squares from that additive interface does not exclude this construction.
-/

namespace NormalNumbers.SquareLambertProposal

/-- Number of positive square roots of square divisors of `n`; zero at `n=0`. -/
def squareDivisorCount (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => d ^ 2 ∣ n).card

/-- An arithmetic series whose definition does not prescribe any digits. -/
noncomputable def squareLambert (b : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((b : ℝ) ^ ((n + 1) ^ 2) - 1)

/-- The proposed first target.  No proof of this statement is claimed. -/
@[blueprint (title := "Proposed binary disjunctivity of the square-indexed Lambert constant")]
def SquareLambertBinaryDisjunctive : Prop := IsDisjunctive 2 (squareLambert 2)

/-- Expected geometric-series regrouping, stated for the prospective proof. -/
def SquareLambertExpansion : Prop :=
  ∀ b : ℕ, 2 ≤ b → squareLambert b =
    ∑' n : ℕ, (squareDivisorCount n : ℝ) / (b : ℝ) ^ n

/-- Elementary arithmetic package still to prove for this defined count. -/
def SquareCoefficientArithmetic : Prop :=
  (∀ m n : ℕ, m.Coprime n →
    squareDivisorCount (m * n) = squareDivisorCount m * squareDivisorCount n) ∧
  (∀ p e : ℕ, p.Prime → squareDivisorCount (p ^ e) = e / 2 + 1)

/-- Expected factorization form; distinguishes square divisors from squarefree divisors. -/
def SquareCoefficientFactorization : Prop :=
  ∀ n : ℕ, 0 < n → squareDivisorCount n =
    ∏ p ∈ n.primeFactors, (n.factorization p / 2 + 1)

/-- A prospective single-coefficient writer: one prescribed prime power
and one prime cofactor can produce every positive coefficient value. -/
def SquareSingleWriter : Prop :=
  ∀ a p q : ℕ, 1 ≤ a → p.Prime → q.Prime → p ≠ q →
    squareDivisorCount (q ^ (2 * (a - 1)) * p) = a

/-- The proposed local kill rule.  Exact prime valuation two contributes
a factor two, independently of the remaining coprime cofactor. -/
def SquareLocalKill : Prop :=
  ∀ p m : ℕ, p.Prime → p.Coprime m →
    squareDivisorCount (p ^ 2 * m) = 2 * squareDivisorCount m

/-- The precise first research gate.  The square-divisor CRT pattern must
coexist with a small *ordinary divisor* tail at arbitrarily late positions.
The majorant below then bounds the square-divisor tail as well.  Existing
Erdos--Borwein witnesses do not automatically satisfy the changed pattern. -/
@[blueprint (title := "Open square-Lambert coefficient and carry-tail supply")]
def SquareLambertWindowSupply : Prop :=
  ∀ a r : ℕ, 2 ≤ a → 1 ≤ r → ∀ ε : ℝ, 0 < ε → ∀ K N : ℕ,
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j : ℕ, j < k → j ≠ r → 2 ^ (j + 1) ∣ squareDivisorCount (n + j)) ∧
      squareDivisorCount (n + r) = a ∧
      (∑' t : ℕ, (SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t)) < ε

/-- More informative first gate: retain the exact prime valuations,
distinctness (as a finset), and prime cofactor through the existing tail
selection.  At parameters `c=3` and `oldA=2*a-1`, the current proof constructs
such local data internally but its final theorem discards them.  This
strengthened statement has not been proved here. -/
@[blueprint (title := "Open retention of square-divisor witnesses through Lambert tail selection")]
def SquareLambertWitnessSupply : Prop :=
  ∀ a r : ℕ, 2 ≤ a → 1 ≤ r → ∀ ε : ℝ, 0 < ε → ∀ K N : ℕ,
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j : ℕ, j < k → j ≠ r → ∃ P : Finset ℕ,
        P.card = j + 1 ∧ ∀ p ∈ P, p.Prime ∧ (n + j).factorization p = 2) ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
        n + r = q ^ (2 * (a - 1)) * p) ∧
      (∑' t : ℕ, (SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t)) < ε

/-- The survivor power is already in the old construction's parameter
family.  This identity alone does not retain or construct any witnesses. -/
theorem square_writer_parameter (a q : ℕ) (ha : 2 ≤ a) :
    2 ≤ 2 * a - 1 ∧ JointLambert.jointQ (2 * a - 1) q = q ^ (2 * (a - 1)) := by
  constructor
  · omega
  · unfold JointLambert.jointQ
    congr 1
    omega

/-- Assembly obligation, kept separate from the unproved arithmetic supply. -/
def SquareLambertTransfer : Prop :=
  SquareLambertExpansion → SquareLambertWindowSupply → SquareLambertBinaryDisjunctive

/-- Square-root candidates form a subset of the positive divisors. -/
theorem squareDivisorCount_le_tau (n : ℕ) : squareDivisorCount n ≤ SwingC2.tau n := by
  exact Finset.card_filter_le _ _

/-- The existing divisor-tail majorant is sufficient on any progression
that the new construction supplies.  This does not supply that progression. -/
@[blueprint (title := "The square-Lambert carry tail is dominated by the ordinary divisor tail")]
theorem square_tail_le_divisor_tail (n k : ℕ) :
    (∑' t : ℕ, (squareDivisorCount (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t)) ≤
    ∑' t : ℕ, (SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) := by
  have hterm : ∀ t : ℕ,
      (squareDivisorCount (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) ≤
      (SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) := by
    intro t
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (squareDivisorCount_le_tau _))
      (by positivity)
  have hsum := JointLambert.summable_binary_tail n k
  exact Summable.tsum_le_tsum hterm
    (Summable.of_nonneg_of_le (fun _ => by positivity) hterm hsum) hsum

/-- Actual arithmetic controls: one square prime produces two, a fourth
power produces three, and two square primes produce four.  They are not
digit visits or evidence for the uniform window-supply statement. -/
@[blueprint (title := "Square-divisor writer and kill controls")]
theorem square_coefficient_controls :
    squareDivisorCount 18 = 2 ∧ squareDivisorCount 162 = 3 ∧
    squareDivisorCount 450 = 4 := by
  decide

end NormalNumbers.SquareLambertProposal
