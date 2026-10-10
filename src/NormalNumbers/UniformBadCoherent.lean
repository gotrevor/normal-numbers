/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadNextReview

/-!
# Operator gate 4: a shared-phase {2,3} core at exponent 4.49

**Frozen target** (Ren, operator, 2026-10-10): `coherentTwoThree449`, i.e. the review node
`NextReview.CoherentTwoThree449`.  Do not weaken or restate it.  If it is false, prove
`¬ NextReview.CoherentTwoThree449` (or the measured obstruction) in a separate declaration,
leave the frozen `sorry` in place and write `ON-LINE-REQUEST.md`; the operator retires it.

## The lever

`scripts/cstar_models/abs3.js` sums over the binary children of a cell, and each child
minimizes over its own target phase bin: `Σ_child inf_phase`.  A real parent has ONE phase,
shared by every descendant, so the true block value is `inf_phase Σ_child`.
`NextReview.common_phase_sum_bound` is the elementary inequality between the two; it says
nothing about the size of the gap.  `CoherentBlockCertificate` keeps the joint row of all
surviving descendants of one concrete parent over a block of `D` levels.

## Measure first (the number to reach)

An exact block certificate with per-level growth `≥ 9/5`, a positive root weight and
weights in `[0, 1]`, first at `c = 4.5` and then at `c = 449/100`.  Use the existing
`c = 4.5` SFT (`scripts/cstar_models/sft45.json`, binary rate ≈ 1.890252) and blocks
`D = 2, 4, 8` (cap 12).  Partition the parent cells along the actual transition and window
boundaries, not along a uniform grid.  Report the smallest positive weight and the
weight-aware tail charges, then feed those charges into the base `≥ 5` engine and require a
positive margin, including a rigorous infinite-base tail.

## Controls (each must pass before a number is believed)

* base 3 disabled recovers the binary rate 1.890252;
* a singleton phase set makes the shared and separate minimizations equal;
* below `log₂ 3` the binary tree dies;
* sampled phases are an OPTIMISTIC screen only: a sampled minimum is `≥` the true infimum.

## Kill test

If the shared-phase minimum is ≈ the separate minimum on the reachable states, the lever is
irrelevant for that finite model.  That is a screening failure, NOT a proof of
`¬ CoherentTwoThree449`, which quantifies over all classifiers, weights, outcomes and `D ≤ 12`
(Codex review, 2026-10-10).  State it in Lean as the actual finite model, the tested states and
phases, and an exact rational tolerance (or as a named conjecture `Prop`), add a Maze row, and
stop.  The `c = 4.49` run needs a binary model rebuilt at 4.49 (or proved stronger than
`sft45.json`), since the binary forbidden radius grows as `c` decreases.

## Measurement, lap 1 (2026-10-10; `scripts/cstar_models/shared3*.{js,c}`, `shared3_results.txt`)

Controls pass (`shared3_controls.txt`).  **Kill test does not fire:** on the same samples the
separate minimization dies (D = 2) or collapses (D = 4: growth 0.96, root 0), while the shared
one grows 1.58 (D=2), 1.76 (D=4), 1.83 (D=6), 1.82 (D=8, N=32, K=12x6).  Sampled growth at D=8
decreases slowly with K (1.832, 1.821, 1.818, 1.815 for K = 6..48): a thin margin over 1.8, and
the c = 4.49 numbers match (1.820 at N=32, 1.840 at N=64).
**Obstruction for uniform bins:** interval value iteration and branch-and-bound of the sampled
weights both fail, because a uniform bin can contain a closed-touching point (e.g. x = 0, u = 1
for the root state) where the whole block dies, so the bin infimum is 0.  A certificate must use
a partition refined along the touching boundaries (`CoherentTwoThree45` below is the c = 4.5
staging node).

## Forbidden

Retuning local charges without the shared-phase change, and another blind base sweep.
-/

namespace NormalNumbers.UniformBadThreshold.Coherent

open NextReview

/-- Staging node (gate step 1 asks for `c = 4.5` first): the same certificate at `c = 9/2`.
Evidence: sampled shared-phase growth ≈ 1.815 at D = 8 (optimistic screen); no rigorous
certificate yet (uniform bins fail, see module doc).  Confidence it holds with an adapted
partition: 45%. -/
def CoherentTwoThree45 : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (twoThreeBad (9 / 2)) D (9 / 5)

/-- **Operator gate 4.**  A shared-phase finite-state certificate for the {2,3} core at
exponent 449/100, with block growth at least 9/5 over some block length `D ≤ 12`. -/
theorem coherentTwoThree449 : CoherentTwoThree449 := by
  sorry

end NormalNumbers.UniformBadThreshold.Coherent
