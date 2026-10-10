/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailObstruction

/-!
# Gate 5 crux: a two-part mechanism (lap 2 nodes)

The crux `TailChargeBudget449` charges tail losses to PAST surviving masses.  Lap 2 splits what a
proof needs into two statements about the gate-4 core, neither involving the arithmetic of `b`:

1. `APKillUniform449` (equidistribution against shifted progressions).  For a Good ancestor and an
   arithmetic progression of base-`b` stage-`n` windows with ARBITRARY offset `θ` and spacing at
   least `2^12` times finer than the ancestor cell, the killed Good descendant weight is at most
   `C · 2b^{-4.49}` times the descendant weight.  Evidence (`scripts/cstar_models/tail5_offset_*.py`,
   `tail5_out/offset_probe.txt`; max over `θ` by an exact event sweep, float positions): ratio
   max/coverage `1.11, 1.14, 1.10` (root, bases 5, 6, 7) and `0.83, 0.73` (ancestor `(6,2)`,
   bases 5, 6).  So `C = 2` looks safe; the worst offset is within `2.3×` of the actual one.
   Because `θ` is arbitrary, this needs no Diophantine input about `b` versus `2, 3`.

2. `UpperGrowth449` (an UPPER growth bound in totals).  (1) bounds the loss by a fraction of the
   CHILD mass, `≈ 0.009 · childMassTot m` summed over bases, but the crux charges against
   `mass (m - lag)`.  Bridging needs `childMassTot m ≤ Λ · mass m`.  Per-ancestor this fails
   badly (`childConcentration_18`, ratio 5704), and any class-wise potential loses the weight
   spread `≈ 3020`; with lags the bound needs `Λ < γ ≤ (9/5)^6`, impossible.  So the totals bound
   must use the actual survivor distribution (near the Perron vector), not the sub-eigenvector.
   This is the identified hard core of gate 5.  Confidence it holds with `Λ ≤ 60`: 70%
   (measured `loss/mass ≈ 0.21–0.23` with loss fraction `≈ 0.007` of child mass gives
   `childMass/mass ≈ 30`).
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

open Coherent

/-- A base-`b` stage-`n` window shifted by `θ`. -/
noncomputable def windowAt (b n : ℕ) (θ : ℝ) (A : ℤ) : Set ℝ :=
  Set.Icc (((A : ℝ) + θ - (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n)
    (((A : ℝ) + θ + (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n)

open Classical in
/-- Good level-`K` descendant weight of `(k, a)`. -/
noncomputable def descMass (k a K : ℕ) : ℚ :=
  ∑ j ∈ (Finset.range (2 ^ (K - k))).filter (fun j => Good449 K (2 ^ (K - k) * a + j)),
    coreWeight K (2 ^ (K - k) * a + j)

open Classical in
/-- Good level-`K` descendant weight of `(k, a)` inside the shifted progression. -/
noncomputable def descKilled (k a K b n : ℕ) (θ : ℝ) : ℚ :=
  ∑ j ∈ (Finset.range (2 ^ (K - k))).filter (fun j => Good449 K (2 ^ (K - k) * a + j) ∧
      ∃ A : ℤ, Count.cell K (2 ^ (K - k) * a + j) ⊆ windowAt b n θ A),
    coreWeight K (2 ^ (K - k) * a + j)

/-- **Node 1 (conjecture, evidence above).**  Offset-uniform kill bound for fine progressions. -/
def APKillUniform449 (C : ℝ) : Prop :=
  ∀ k a K b n (θ : ℝ), Good449 k a → k ≤ K → 5 ≤ b → 2 ^ (k + 12) ≤ b ^ n →
    (descKilled k a K b n θ : ℝ) ≤ C * (2 * (b : ℝ) ^ (-(449 / 100 : ℝ))) * descMass k a K

open Classical in
/-- Good child weight of all surviving level-`6m` parents. -/
noncomputable def childMassTot (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)), descMass (6 * m) a (6 * (m + 1))

/-- **Node 2 (conjecture, the identified hard core).**  Upper growth of the weighted core in
totals.  Not implied by gate 4 (a lower, sub-eigenvector certificate). -/
def UpperGrowth449 (Λ : ℚ) : Prop := ∀ m, childMassTot m ≤ Λ * mass m

/-- The loss is part of the child mass, so a totals bound `loss ≤ ε · childMass` plus upper
growth gives the reopen node `TailTotalsBound449`. -/
theorem tailTotals_of_upperGrowth {ε Λ : ℚ} (hε : 0 ≤ ε) (hΛ : ε * Λ ≤ 1 / 4)
    (hloss : ∀ m, loss m ≤ ε * childMassTot m) (hup : UpperGrowth449 Λ)
    (hmass : ∀ m, 0 ≤ mass m) : TailTotalsBound449 := fun m =>
  calc loss m ≤ ε * childMassTot m := hloss m
    _ ≤ ε * (Λ * mass m) := mul_le_mul_of_nonneg_left (hup m) hε
    _ = (ε * Λ) * mass m := by ring
    _ ≤ 1 / 4 * mass m := mul_le_mul_of_nonneg_right hΛ (hmass m)

/-- **The crux has 140× slack in totals.**  Any uniform ratio `loss ≤ c · mass` with
`c < (9/5)^6 - 1 ≈ 33` gives the crux (take `γ = (9/5)^6 - c`).  Measured `c ≈ 0.23`
(`tail5_out/totals_b7_m3.txt`, bases 5..7, `m = 2, 3`). -/
theorem tailChargeBudget449_of_ratio {c : ℚ} (hc0 : 0 ≤ c) (hc : c < (9 / 5 : ℚ) ^ 6 - 1)
    (h : ∀ m, loss m ≤ c * mass m) : TailChargeBudget449 := by
  refine ⟨(9 / 5 : ℚ) ^ 6 - c, by linarith, fun lag => if lag = 0 then c else 0,
    fun lag => by dsimp only; split_ifs <;> linarith, fun m => ?_, fun m => ?_⟩
  · rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl]) (by simp)]
    simpa using h m
  · rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl]) (by simp)]
    simp

open Classical in
/-- Survivors' Good descendant weight `j` blocks down (tail kills inside ignored). -/
noncomputable def descTot (m j : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)), descMass (6 * m) a (6 * (m + j))

/-- **Node 3 (conjecture, refines node 2 for lag charging).**  Multi-block totals upper growth.
Charging base `b` at lag `j_b ≈ 0.75 log₂ b + 2` (where node 1 applies) costs
`≈ 2b^{-4.49} · C · Λ^{j_b+1} / γ^{j_b}` per stage; with `Λ ≈ 44` (measured one-block totals
`childMass/mass = 43.4, 44.6` at `m = 2, 3`) and `γ = 20` this is summable, `≈ 0.8` for base 5,
against the budget `(9/5)^6 - 20 ≈ 14`.  Per-ancestor sups (`≥ 5704` at one block) make the same
sum diverge, so the totals are essential.  Confidence 60%. -/
def UpperGrowthLag449 (K Λ : ℚ) : Prop := ∀ m j, descTot m j ≤ K * Λ ^ j * mass m

/-- **Node 4 (conjecture): the once-iterated potential is regular.**  The raw weights are not
(`desc₁/w` reaches 5704 at `(18, 191938)`, 604 at level 12), but the child-mass potential
`v = descMass k a (k+6)` is nearly an eigenvector: `max desc₂/desc₁ = 52.07` over all Good level-12
cells, and `42.05` at the bad cell `(18, 191938)` (`scripts/cstar_models/tail5_ratio_iter.py`,
`tail5_out/ratio_iter.txt`; SAMPLED maxima).  Confidence 65% that `R = 60` holds at every level. -/
def RegularPotential449 (R : ℚ) : Prop :=
  ∀ k a, Good449 k a → descMass k a (k + 12) ≤ R * descMass k a (k + 6)

/-- **Totals upper growth from node 4** (statement; proof is bookkeeping: survivors at `m+1` are
Good children of survivors at `m`, and `descMass` splits over children).  With the recurrence
this gives `UpperGrowth449 (R · 34/(34-c))` once `loss ≤ c · mass` is known up to `m`, so the
induction closes. -/
theorem childMassTot_succ_le {R : ℚ} (hR : RegularPotential449 R) (m : ℕ) :
    childMassTot (m + 1) ≤ R * childMassTot m := by
  sorry

end NormalNumbers.UniformBadThreshold.TailReview
