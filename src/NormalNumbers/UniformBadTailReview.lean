/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadCoherent
import NormalNumbers.UniformBadRoute

/-!
# Proposed next gate: weighted deletion after the proved two-base core

These are review proposal statements, not a new all-base upper bound.  The fixed
weights are the proved gate-4 weights.  The missing estimate charges new losses
to earlier surviving mass, with a summable budget.  Replacing weights by cell
counts would change the proposal.
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

/-- All remaining non-perfect-power bases, including stage zero. -/
def tailBad449 (k a : ℕ) : Prop :=
  ∃ b : ℕ, 5 ≤ b ∧ ¬ IsPerfPow b ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Coherent.window b n A

/-- Ordinary normalized cell weight from the fixed, proved core. -/
noncomputable def coreWeight (k a : ℕ) : ℚ :=
  Coherent.wq (Coherent.classify k a)

/-- A good core cell that has survived every tail containment test so far. -/
def survives (k a : ℕ) : Prop :=
  Coherent.Good449 k a ∧ Count.Alive tailBad449 k a

open Classical in
/-- Total surviving core weight at binary level `6m`. -/
noncomputable def mass (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)),
    coreWeight (6 * m) a

open Classical in
/-- Weight of good depth-six descendants lost to the tail, from surviving parents.
The `Alive` test includes all intermediate levels, not only block endpoints. -/
noncomputable def loss (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)),
    ∑ j ∈ (Finset.range 64).filter (fun j =>
      Coherent.Good449 (6 * (m + 1)) (64 * a + j) ∧
      ¬ Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j)),
      coreWeight (6 * (m + 1)) (64 * a + j)

/-- Proposed frozen crux.  `gamma` is growth per SIX levels.  Coefficients charge
actual weighted deletions to earlier surviving masses.  Every finite partial
budget must fit, so a finite base cutoff alone cannot satisfy the statement.
For an initial numerical target gamma=(17/10)^6, the budget is 9.874655. -/
def TailChargeBudget449 : Prop :=
  ∃ gamma : ℚ, 1 < gamma ∧ ∃ charge : ℕ → ℚ,
    (∀ lag, 0 ≤ charge lag) ∧
    (∀ m, loss m ≤ ∑ lag ∈ Finset.range (m + 1), charge lag * mass (m - lag)) ∧
    (∀ m, (∑ lag ∈ Finset.range (m + 1), charge lag / gamma ^ lag) ≤
      (9 / 5 : ℚ) ^ 6 - gamma)

/-- Structural wiring to prove from gate 4 by summing over disjoint parents.
This statement is recorded explicitly, not assumed or asserted as proved. -/
def CoreDeletionRecurrence449 : Prop :=
  ∀ m, (9 / 5 : ℚ) ^ 6 * mass m ≤ mass (m + 1) + loss m

/-- Completion target for the proposed gate.  The route is positive mass at
every block level, compactness, weak avoidance at 4.49, and strict avoidance at
every larger exponent.  Thus no equality-endpoint upgrade is needed merely to
bound the infimum cStar.  The implication is not proved in this review module. -/
def TailBudgetSuffices449 : Prop :=
  TailChargeBudget449 → cStar ≤ 449 / 100

end NormalNumbers.UniformBadThreshold.TailReview
