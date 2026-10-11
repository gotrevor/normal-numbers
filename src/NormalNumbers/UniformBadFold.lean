/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTail

/-!
# Operator gate 6, fallback (a): fold small tail bases into the shared-phase core

A second route to the frozen headline `Tail.cStar_le_449`, beside the gate-5 statements
(`TailReview.TailChargeBudget449`, `Tail.tailBudgetSuffices449`), which stay untouched.
The core runs over `{2,3} ∪ F` with `F ⊆ {5,6,7}`; the weighted tail runs over the remaining
non-perfect-power bases `b ≥ 5`, `b ∉ F`.

## Screen (2026-10-11, `scripts/cstar_models/gate6/`, sampled, so upper bounds on a certificate)

`sharedF.js` is `shared3.js` with one extra phase `(x_b, u_b)` per base of `F`.  Controls:
`F = ∅` gives 1.8382 (gate 4: 1.8373), zero radius for base 5 gives the same value, and
deleting every child kills the tree.  Growth per level at 4.49, block `D = 6`:
* `F = {5}`: 1.8311 (base-5 phase bins 64, 128, 256 give 1.8311, 1.8310, 1.8327).
  The target was 1.79 + 0.02.
* `F = {5,6}` and `{5,6,7}`, coarse phases: 1.8368 and 1.8382, against targets 1.75 and 1.715.

The pick is the cheapest `F` that clears its target, `F = {5}`.  The tail was then re-screened
(`tail_kf.py`, the refinements (i)+(ii)+(iii) of `tail5_refined.py`) with this core's own run
sums `f` and layer-cake `e'`, computed on real cells (levels 10..16, screen weights), at core
growth `9/5`:
* `F = {5}`: gap 0.742.  The same instrument with `F = ∅` weights gives 0.664, where the
  certified gate-4 weights give 0.737.  Scaled by that control, the estimate is about 0.82.
* `F = {5,6}`, as a backup: gap 0.372.
Both are below 1, so the gate-6 kill did not fire.  The 0.82 leaves little headroom for
certification losses, and `{5,6}` is the fallback if the exact core or tail certificate for
`{5}` comes in short.  These are sampled numbers, not certificates.

## Statements (frozen for Codex's semantic review before any proof)

* `CoherentCore449F F g`: the gate-4 probe gate `NextReview.CoherentTwoThree449`, with `F` added
  to the core's bases.
* `WeightedCore449F F g wt Good`: the interface the wiring consumes.  It mirrors the facts gate 4
  proved about `Coherent.wq ∘ Coherent.classify` on `Coherent.Good449`: nonnegative weights,
  root weight 1, good cells alive in the core, and six-level growth `g^6`.
* `TailChargeBudget449F F g wt Good`: `TailReview.TailChargeBudget449` with the fold-tail bases,
  the given core, and the budget `g^6 - γ`.
* `TailBudgetSuffices449F`: the wiring to `cStar ≤ 449/100`.
-/

namespace NormalNumbers.UniformBadThreshold.Fold

open NextReview

/-- The chosen fold set (gate-6 screen). -/
def F5 : Finset ℕ := {5}

/-- Core containment pruning over `{2,3} ∪ F` at exponent `449/100`. -/
def coreBadF (F : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ b : ℕ, (b = 2 ∨ b = 3 ∨ b ∈ F) ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Coherent.window b n A

/-- Remaining tail: non-perfect-power bases `b ≥ 5` outside `F`, including stage zero. -/
def tailBadF (F : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ b : ℕ, 5 ≤ b ∧ ¬ IsPerfPow b ∧ b ∉ F ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Coherent.window b n A

/-- Gate-6 probe gate: an exact joint core over `{2,3} ∪ F` at 4.49 with bounded finite-state
weights and block growth at least `g`.  Mirrors `NextReview.CoherentTwoThree449`. -/
def CoherentCore449F (F : Finset ℕ) (g : ℚ) : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (coreBadF F) D g

open Classical in
/-- What the exact gate-6 certificate must deliver to the wiring (the analogue of
`Coherent.wq_nonneg`, `wq ≤ 1`, the root, `good449_clean`/`clean449_alive`, and `Coherent.wq_grow`). -/
def WeightedCore449F (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) : Prop :=
  (∀ k a, 0 ≤ wt k a) ∧ Good 0 0 ∧ wt 0 0 = 1 ∧
  (∀ k a, Good k a → Count.Alive (coreBadF F) k a) ∧
  (∀ k a, Good k a →
    g ^ 6 * wt k a ≤
      ∑ j ∈ (Finset.range 64).filter (fun j => Good (k + 6) (64 * a + j)),
        wt (k + 6) (64 * a + j))

/-- A good core cell that has survived every fold-tail containment test so far. -/
def survivesF (F : Finset ℕ) (Good : ℕ → ℕ → Prop) (k a : ℕ) : Prop :=
  Good k a ∧ Count.Alive (tailBadF F) k a

open Classical in
/-- Total surviving core weight at binary level `6m`. -/
noncomputable def massF (F : Finset ℕ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survivesF F Good (6 * m)), wt (6 * m) a

open Classical in
/-- Weight of good depth-six descendants lost to the fold tail, from surviving parents. -/
noncomputable def lossF (F : Finset ℕ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survivesF F Good (6 * m)),
    ∑ j ∈ (Finset.range 64).filter (fun j =>
      Good (6 * (m + 1)) (64 * a + j) ∧
      ¬ Count.Alive (tailBadF F) (6 * (m + 1)) (64 * a + j)),
      wt (6 * (m + 1)) (64 * a + j)

/-- Gate-6 tail crux: `TailReview.TailChargeBudget449` over the fold tail, for the given core,
with the budget `g^6 - γ`.  Every finite partial budget must fit. -/
def TailChargeBudget449F (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ)
    (Good : ℕ → ℕ → Prop) : Prop :=
  ∃ gamma : ℚ, 1 < gamma ∧ ∃ charge : ℕ → ℚ,
    (∀ lag, 0 ≤ charge lag) ∧
    (∀ m, lossF F wt Good m ≤
      ∑ lag ∈ Finset.range (m + 1), charge lag * massF F wt Good (m - lag)) ∧
    (∀ m, (∑ lag ∈ Finset.range (m + 1), charge lag / gamma ^ lag) ≤ g ^ 6 - gamma)

/-- Gate-6 wiring: a weighted fold core plus a fold-tail budget bounds `cStar` by `449/100`.
Same proof shape as `TailReview.tailBudgetSuffices449_proof`. -/
def TailBudgetSuffices449F : Prop :=
  ∀ (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop),
    WeightedCore449F F g wt Good → TailChargeBudget449F F g wt Good → cStar ≤ 449 / 100

/-- **Gate 6, wiring.**  Statement frozen pending Codex's review; proof not started. -/
theorem tailBudgetSuffices449F : TailBudgetSuffices449F := by
  sorry

/-- **Gate 6, route.**  The exact `{2,3,5}` core and its tail budget at `g = 9/5`.
Screen: core growth 1.831 sampled, tail gap about 0.82 (module docstring). -/
theorem foldRoute449 : ∃ (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop),
    WeightedCore449F F5 (9 / 5) wt Good ∧ TailChargeBudget449F F5 (9 / 5) wt Good := by
  sorry

/-- The headline by the gate-6 route. -/
theorem cStar_le_449_fold : cStar ≤ 449 / 100 := by
  obtain ⟨wt, Good, hc, ht⟩ := foldRoute449
  exact tailBudgetSuffices449F F5 (9 / 5) wt Good hc ht

end NormalNumbers.UniformBadThreshold.Fold
