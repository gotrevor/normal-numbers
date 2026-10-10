/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailSplit

/-!
# Gate 5 kill test: per-ancestor charging of bases 5–7 on the gate-4 weights (NOT fired)

**What is obstructed.**  Not `TailChargeBudget449` (an existential over totals; the measured
totals `loss m / mass m` are 0.2300 at `m = 2` and 0.2104 at `m = 3`, exact on the finite tree,
bases 5..7).  Per-ancestor SUP charging schemes at `γ = (17/10)^6`:
each window loss is charged to one ancestor and `h_lag` is the sup over ancestors of
(charged loss)/(ancestor weight).  Sampled values of `Σ h_j/γ^j` for bases 5..7, stages
`n ≤ 7` (`scripts/cstar_models/tail5_measure.py`, outputs in `tail5_out/`), against the budget
`9.874655`:

* natural ancestor level (`2^L ≥ bⁿ`): 655 (n ≤ 6);
* one block higher: 226.5;
* **two blocks higher: 4.496 (n ≤ 7) — PASSES** (2.24, 2.84, 4.50 at n ≤ 5, 6, 7; growing).
  Correction 2026-10-10 (lap 2): lap 1 recorded "every scheme fails" and omitted this output
  (`tail5_out/peranc_b7_n7_shift2.txt`).  The kill test has therefore NOT fired: bases 5..7 do
  not exhaust the budget under the shift-2 scheme on the measured range.  Base 5 alone,
  shift 2: 2.32 (n ≤ 7), 3.71 (n ≤ 8) — still growing, saturation unknown (lap 2);
* three blocks higher, base 5, n ≤ 8: 2.64 (PASS; at this depth nearly every window charges the
  root, so this says little about the supremum);
* climb to the nearest ancestor of weight `> θ`: 174.4 (`θ = 1/100`), 81.7 (`θ = 1/20`);
* base 5 alone, `θ = 1/20`: 64.1.

These are SAMPLED lower bounds on the scheme's supremum (per-window isolation overcount), so
each FAIL is a failure of that scheme at that `γ`, never a lower bound on the true joint loss;
the shift-2 PASS is only a pass on the sampled range `n ≤ 7` (sup over larger `n` unmeasured).

**Mechanism.**  The proved weights `wq ∘ classify` are a sub-eigenvector, not a regular measure:
a Good cell can carry tiny weight while its good children are heavy
(`childConcentration_18`: ratio 5704 in one block, against the guaranteed `(9/5)^6 ≈ 34`), so a
window landing in such a subtree costs a huge multiple of any nearby ancestor's weight.

**Structural fix** (operator): fold bases 5..7 into the core (a gate-4-style certificate whose
state carries their phases), or an averaging (totals) mechanism, `TailTotalsBound449`.
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

open Coherent

open Classical in
/-- Weight of the good children of `(k, a)` one block (six levels) down. -/
noncomputable def childMass (k a : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range 64).filter (fun j => Good449 (k + 6) (64 * a + j)),
    coreWeight (k + 6) (64 * a + j)

/-- **Concentration of the gate-4 weights** (exact finite fact, not yet kernel-checked).  The Good
cell `(18, 191938)` (`x ≈ 0.73219`, weight `≈ 7.16·10⁻⁴`, about `2/3020` of the maximum) has good
children `64a + j`, `j = 56..61`, of total weight `5704.02…` times its own.  Computed exactly
(`tail5_measure.weight`, rational, δ enclosures at 60 digits, no ambiguous comparisons);
confidence 95% (the residual risk is the Python model of `classify`, checked against the
gate-4 root sum and the delete-all control).  Proof route: evaluate `classify` on the 7 cells
(`pend`, `ibin`, `jbin`, `sftRun`) and `Good449` by the `windows_sound` machinery. -/
theorem childConcentration_18 :
    Good449 18 191938 ∧ 5704 * coreWeight 18 191938 ≤ childMass 18 191938 := by
  sorry

/-- **Reopen condition**: a totals bound, the measured regime (`loss m ≤ (1/4) mass m`
holds at `m = 2, 3`).  It implies `TailChargeBudget449` (charge `1/4` at lag 0; proved below).
No mechanism is known: it needs equidistribution of base-5..∞ windows against the weighted
`{2,3}` core at every scale, with weights that are not locally regular. -/
def TailTotalsBound449 : Prop := ∀ m, loss m ≤ (1 / 4 : ℚ) * mass m

theorem tailChargeBudget449_of_totals (h : TailTotalsBound449) : TailChargeBudget449 := by
  refine ⟨(17 / 10) ^ 6, by norm_num, fun lag => if lag = 0 then 1 / 4 else 0,
    fun lag => by dsimp only; split_ifs <;> norm_num, fun m => ?_, fun m => ?_⟩
  · rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl]) (by simp)]
    simpa using h m
  · rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl]) (by simp)]
    norm_num

end NormalNumbers.UniformBadThreshold.TailReview
