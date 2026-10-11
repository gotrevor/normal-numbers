/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailWiring

/-!
# Operator gate 5: the weighted base ≥ 5 tail at exponent 4.49

**Frozen targets** (Ren, operator, 2026-10-10).  Do not weaken or restate them.

* `tailChargeBudget449 : TailReview.TailChargeBudget449`.  This is the crux: the weighted losses
  that bases `≥ 5` inflict on the proved gate-4 core are charged against earlier surviving
  masses within the discounted budget `(9/5)^6 - γ`.
* `tailBudgetSuffices449 : TailReview.TailBudgetSuffices449`.  This is the wiring: sum gate-4
  growth over disjoint surviving parents to get `CoreDeletionRecurrence449`, then induct on the
  delayed charge from root mass 1 to `mass (m+1) ≥ γ · mass m > 0`.  Compactness of the nested
  surviving cells then gives weak avoidance at 4.49, and strict avoidance at every larger
  exponent, so `cStar ≤ 449/100`.  Perfect-power bases are covered by their roots.
* `cStar_le_449` is the headline, the composition of the two.

The design and the quantifier review are Codex's (`UniformBadTailReview.lean`, mail
20261010T163954Z).  The operator re-checked the quantifiers.

## Measure first (the number to reach)

The core weights are fixed and proved: `Coherent.wq ∘ Coherent.classify`.  Positive weights span
a factor of about 3020, so measure WEIGHTED losses, never raw cell counts.  Measure the actual
weighted window losses for bases 5, 6 and 7 over reachable parent states and delay classes,
against the discounted budget `Σ_l h_l / γ^l ≤ (9/5)^6 - γ`.  That budget is 9.874655 at
`γ = (17/10)^6`.

## Controls

* With a zero tail, the budget passes with zero charges.
* Deleting every positive first-block child must FAIL the budget.
* Sampled maxima can refute a proposed uniform coefficient, but they cannot certify one.

## Kill test

If bases 5–7 alone exhaust the budget, state the measured obstruction in Lean (the actual
finite model, the states and an exact rational tolerance), add a Maze row, write
`ON-LINE-REQUEST.md`, and stop.  The structural fix would then be folding those bases into the
core, not finer phase subdivision.

## Forbidden

Unweighted cell counts in place of weighted loss.  A finite base cutoff presented as the
statement.  Retuning gate-4 weights without re-proving `coherentTwoThree449`.
-/

namespace NormalNumbers.UniformBadThreshold.Tail

open TailReview

/-- **Operator gate 5, crux.**  The weighted base ≥ 5 tail fits the discounted budget. -/
theorem tailChargeBudget449 : TailChargeBudget449 := by
  sorry

/-- **Operator gate 5, wiring.**  A tail charge budget bounds `cStar` by `449/100`. -/
theorem tailBudgetSuffices449 : TailBudgetSuffices449 :=
  tailBudgetSuffices449_proof

/-- **Operator gate 5, headline.** -/
theorem cStar_le_449 : cStar ≤ 449 / 100 :=
  tailBudgetSuffices449 tailChargeBudget449

end NormalNumbers.UniformBadThreshold.Tail
