/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Gate 5 relaunch: the refined counting screen misses (kill criterion fired)

The counting route for the frozen crux `TailChargeBudget449` (gate 5 lap 3) bounds the tail loss by
`loss m ≤ ∑_l h_l mass (m - l)` with
`h_l = K · ∑_b sup_φ0 ∑_{i : φ = φ0 b^i < 64} cnt(φ) · F(ρ)`, `ρ = 2 r_b 2^(6l) / φ`, `r_b = b^-4.49`,
and needs `∑_l h_l / γ^l ≤ (9/5)^6 - γ` for some `γ > 1`.  The operator relaunch (DIRECTION.md,
2026-10-11) added three refinements one at a time:

* (i)   `F` = W-weighted run sums `f(R)` (max over parents of a contiguous run of `R` children's
        weight, `tail5_runsum.py`, exhaustive over levels 5..20; `f(63) = 40.06`, not `63`);
* (ii)  layer-cake comb comparability `K = min_β β / (1 - e'(β)/γ)`,
        `e'(β) = max_p ∑_{c alive} (1 - β W_c)^+` (`tail5_layercake.py`, exhaustive over levels 5..15);
* (iii) exact window counts `⌊φ + 2 r_b⌋ + 1` per ancestor instead of `φ + 2`.

Certified gaps `inf_γ ∑/budget` (`tail5_refined.py 300 100 FLAGS`, output
`scripts/cstar_models/tail5_out/refined_screen.txt`, 4000-interval rational sweep of `γ ∈ (1, (9/5)^6)`):
crude 5.419, (i) 4.190, (iii) 4.385, (ii) 2.231, (i)+(ii) 1.725, (i)+(ii)+(iii) **1.391**.
Controls: dropping bases 5–7 closes (0.695); zero tail passes; killing every child fails (1.584).

Every number is a certified LOWER bound on what the scheme must use (finite-level maxima of sups,
bases truncated at 300, rational `φ0` grid, `r_b` lower enclosure, `β` bracketing), so a gap above 1
certifies that THIS scheme cannot close.  It is NOT a refutation of `TailChargeBudget449`, whose
measured totals (loss/mass ≈ 0.23) are far inside the budget.
-/

namespace NormalNumbers.UniformBadThreshold.TailCounting

/-- The refined counting screen's lag-sum through lag 5 with explicit rational inputs. -/
def screenSum (K γ h1 h2 h3 h4 h5 : ℚ) : ℚ :=
  K * (h1 / γ + h2 / γ ^ 2 + h3 / γ ^ 3 + h4 / γ ^ 4 + h5 / γ ^ 5)

/-- **The refined counting screen misses at its best `γ`.**  At `γ = 641/25 = 25.64` (the
minimizer of the sweep), with every refinement (i)+(ii)+(iii) on, the certified lower bounds
`K ≥ 2321/1000` and `h_1..h_5 ≥ 20, 1723, 23324, 83015, 228619` (floors of the exact values,
`tail5_refined.py`) already give a lag sum `11.598` against the budget `(9/5)^6 - γ = 8.372`:
ratio `1.385`, over the kill threshold `1`.  Lags `≥ 6` only add. -/
theorem refinedScreen_misses_at_best :
    (9 / 5 : ℚ) ^ 6 - 641 / 25 < screenSum (2321 / 1000) (641 / 25) 20 1723 23324 83015 228619 := by
  unfold screenSum; norm_num

/-- The kill is robust: even granting a `4/3` factor of slack on the whole sum, the screen misses. -/
theorem refinedScreen_misses_with_slack :
    4 / 3 * ((9 / 5 : ℚ) ^ 6 - 641 / 25) <
      screenSum (2321 / 1000) (641 / 25) 20 1723 23324 83015 228619 := by
  unfold screenSum; norm_num

/-- Open node (certified numerically, not in Lean): the counting scheme with refinements
(i)+(ii)+(iii) misses at EVERY admissible `γ`, with margin `1.39`.  `Klo γ` is the bracketed lower
bound on `min_β β/(1 - e'(β)/γ)` and `H l` the certified lag coefficients; evidence: the
4000-interval rational sweep in `tail5_refined.py` (worst interval `[25.6436, 25.6519]`, gap
`≥ 1.3910`).  Reopen condition for the counting route: a mechanism lowering the per-ancestor count
or the edge run sum of bases 5–7 by a further factor `≥ 1.4`, i.e. this Prop failing for an improved
`(Klo, H)`. -/
def CountingScreenMisses (Klo : ℚ → ℚ) (H : ℕ → ℚ) : Prop :=
  ∀ γ : ℚ, 1 < γ → γ < (9 / 5 : ℚ) ^ 6 →
    (139 / 100) * ((9 / 5 : ℚ) ^ 6 - γ) ≤ Klo γ * ∑ l ∈ Finset.Icc 1 10, H l / γ ^ l

/-- Open node (certified numerically, not in Lean; operator lever probe 2026-10-11, KILL).
Lever (L2), MASS charging: on top of (i)+(ii)+(iii), for bases 5–7 at lags 1–3 the per-family kill
`∑_a s_a` over ancestors `a` is bounded by `β · mass(m' + j) + K · E_j(β) · mass(m')`, with
`E_j(β) = max_a (s_a − β D_j(a))^+`, `D_j(a)` the depth-`j` descendant weight of `a` (`j = 0`: `W(a)`),
`s_a` per-ancestor descendant run sums (`tail5_lever_data.py 26`, exhaustive, levels ≤ 26), and the best
`j, β` taken per `(b, l)`.  Certified gap `≥ 1.2552` over every `γ` (design 1.334 at `γ ≈ 24.29`;
control `β = 0` gives 1.384 against the refined screen's 1.391), output
`scripts/cstar_models/tail5_out/lever_screen.txt`.  Mechanism: the worst run sums sit under
WEIGHT-ZERO core-alive ancestors (`E_0(β)` is flat in `β`), and charging deeper (`j ≥ 1`) costs `γ^j`
in the discount.  The `D_j` are core (not tail-alive) weights, so these `E` are lower bounds:
a sound miss, not a close.  `MassChargedTotal γ` is the certified lower bound on the L2 lag sum. -/
def MassChargingScreenMisses (MassChargedTotal : ℚ → ℚ) : Prop :=
  ∀ γ : ℚ, 1 < γ → γ < (9 / 5 : ℚ) ^ 6 → (5 / 4) * ((9 / 5 : ℚ) ^ 6 - γ) ≤ MassChargedTotal γ

/-- Lever (L1), lag-dependent `K`: no sound per-lag comparability was found.  Any such constant is
`≥ 1` (count ≥ mass since `W ≤ maxW`), and the optimistic screen with `K_l = 1` for `l ≥ 2`
(`tail5_lever_l1.py 300 100`, `tail5_out/lever_l1.txt`) gives gap `0.705`, so L1 is NOT refuted.
To close at `0.9` it needs a certified `K_{l ≥ 2} ≤ 1.4` (vs `2.32`): survivors relevant at lags
`≥ 2` of average weight `≥ 0.71 maxW`.  Open node: that comparability statement, with `Kl2 = 7/5`. -/
def LagTwoComparability (count mass : ℕ → ℚ) (Kl2 : ℚ) : Prop := ∀ m, count m ≤ Kl2 * mass m

/-- The L1 arithmetic: with the refined coefficients `h_1..h_5` and `K = 2321/1000` on lag 1 only,
`K_l = 7/5` at lags `2..5` fits under `0.9` of the budget at `γ = 24`; `K_l = 2` does not. -/
theorem lagTwoK_threshold :
    (7 / 5 : ℚ) * (1723 / 24 ^ 2 + 23324 / 24 ^ 3 + 83016 / 24 ^ 4 + 228620 / 24 ^ 5) + 2321 / 1000 * (21 / 24)
      < 9 / 10 * ((9 / 5 : ℚ) ^ 6 - 24) ∧
    9 / 10 * ((9 / 5 : ℚ) ^ 6 - 24) <
      (2 : ℚ) * (1723 / 24 ^ 2 + 23324 / 24 ^ 3 + 83015 / 24 ^ 4 + 228619 / 24 ^ 5) + 2321 / 1000 * (20 / 24) := by
  norm_num

end NormalNumbers.UniformBadThreshold.TailCounting
