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

/-- **Node 1 (conjecture, evidence above).**  Offset-uniform kill bound for fine progressions.
Any ancestor cell (not only Good: `Good449` is not hereditary, so charged ancestors may be
non-Good).  Non-Good ancestors `(12,302)`, `(12,458)`, spacing `2^6`: max/coverage `1.25, 1.30,
1.07, 1.10` (`tail5_out/offset_probe_nongood.txt`). -/
def APKillUniform449 (s : ℕ) (C : ℝ) : Prop :=
  ∀ k a K b n (θ : ℝ), a < 2 ^ k → k ≤ K → 5 ≤ b → 2 ^ (k + s) ≤ b ^ n →
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
`v = descMass k a (k+6)` is nearly an eigenvector: `max desc₂/desc₁ = 57.30` over all Good level-12
cells, and `48.16` at the bad cell `(18, 191938)` (`scripts/cstar_models/tail5_ratio_iter.py`,
`tail5_out/ratio_iter.txt`; SAMPLED maxima).  Confidence 65% that `R = 60` holds at every level. -/
def RegularPotential449 (R : ℚ) : Prop :=
  ∀ k a, Good449 k a → descMass k a (k + 12) ≤ R * descMass k a (k + 6)

/-- Split a sum over `range (n * m)` into `n` blocks of length `m`. -/
theorem sum_range_mul_split (f : ℕ → ℚ) (n M : ℕ) :
    ∑ i ∈ Finset.range (n * M), f i = ∑ p ∈ Finset.range M, ∑ j ∈ Finset.range n, f (n * p + j) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Descendant mass splits over the 64 children one block down. -/
theorem descMass_split (k a L : ℕ) :
    descMass k a (k + 6 + L) = ∑ j ∈ Finset.range (2 ^ 6), descMass (k + 6) (2 ^ 6 * a + j) (k + 6 + L) := by
  classical
  unfold descMass
  simp only [Finset.sum_filter]
  rw [show k + 6 + L - k = L + 6 by omega, show k + 6 + L - (k + 6) = L by omega,
    pow_add, sum_range_mul_split]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show 2 ^ L * 2 ^ 6 * a + (2 ^ L * j + i) = 2 ^ L * (2 ^ 6 * a + j) + i by ring]

open Classical in
/-- Child mass of "orphan" survivors at block `m+1`: their level-`6m` parent does not survive.
`Good449` is NOT hereditary (base-3 windows of a resolved stage can meet a parent and miss the
child): 14 of 2562 Good level-12 cells and 922 of 114066 at level 18 have a non-Good ancestor one
or six levels up (lap 2 count, `tail5_measure.good`). -/
noncomputable def orphanChild (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * (m + 1)))).filter
      (fun a => survives (6 * (m + 1)) a ∧ ¬ survives (6 * m) (a / 64)),
    descMass (6 * (m + 1)) a (6 * (m + 2))

/-- **Totals upper growth from node 4** (statement; bookkeeping: non-orphan survivors at `m+1`
are Good children of survivors at `m`, and `descMass` splits over children).  Lap 2 correction:
the orphan term is needed because `Good449` is not hereditary. -/
theorem childMassTot_succ_le {R : ℚ} (hR : RegularPotential449 R) (m : ℕ) :
    childMassTot (m + 1) ≤ R * childMassTot m + orphanChild m := by
  classical
  have hd : ∀ k a K, 0 ≤ descMass k a K := fun k a K =>
    Finset.sum_nonneg fun _ _ => coreWeight_nonneg _ _
  -- split survivors at `m+1` into children of survivors and orphans
  unfold childMassTot orphanChild
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a => survives (6 * m) (a / 64)),
    Finset.filter_filter, Finset.filter_filter]
  refine add_le_add ?_ le_rfl
  rw [Finset.sum_filter]
  have e6 : 6 * (m + 1) = 6 * m + 6 := by ring
  have e12 : 6 * (m + 2) = 6 * m + 6 + 6 := by ring
  rw [show 2 ^ (6 * (m + 1)) = 2 ^ 6 * 2 ^ (6 * m) by rw [e6, pow_add, mul_comm],
    sum_range_mul_split]
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with hp
  · calc ∑ j ∈ Finset.range (2 ^ 6), (if survives (6 * (m + 1)) (2 ^ 6 * p + j) ∧
            survives (6 * m) ((2 ^ 6 * p + j) / 64) then
            descMass (6 * (m + 1)) (2 ^ 6 * p + j) (6 * (m + 2)) else 0)
          ≤ ∑ j ∈ Finset.range (2 ^ 6), descMass (6 * m + 6) (2 ^ 6 * p + j) (6 * m + 6 + 6) :=
            Finset.sum_le_sum fun j _ => by
              split_ifs
              · rw [e6, e12]
              · exact hd _ _ _
        _ = descMass (6 * m) p (6 * m + 12) := (descMass_split _ _ _).symm
        _ ≤ R * descMass (6 * m) p (6 * (m + 1)) := by
            rw [e6]; exact hR _ _ hp.1
  · rw [mul_zero]
    refine Finset.sum_nonpos (ι := ℕ) (N := ℚ) fun j hj => ?_
    split_ifs with h
    · exfalso; apply hp
      have : (2 ^ 6 * p + j) / 64 = p := by
        have := Finset.mem_range.1 hj; omega
      exact this ▸ h.2
    · exact le_rfl

/-- **Node 5 (conjecture): orphans are rare.**  Measured (tail kills ignored,
`scripts/cstar_models/tail5_orphan.py`, `tail5_out/orphan.txt`): orphan child-mass fraction 0 at
`m = 1`, `0.0052` at `m = 2`.  Confidence 70% for `η = 1/20` at every `m`. -/
def OrphanSmall449 (η : ℚ) : Prop := ∀ m, orphanChild m ≤ η * childMassTot (m + 1)

/-- Nodes 4 + 5 give geometric upper growth of the survivors' child mass. -/
theorem childMassTot_succ_le_of_orphan {R η : ℚ} (hR : RegularPotential449 R)
    (hη : OrphanSmall449 η) (m : ℕ) :
    (1 - η) * childMassTot (m + 1) ≤ R * childMassTot m := by
  have := childMassTot_succ_le hR m
  have := hη m
  linarith

/-- **Node 4′ (conjecture): the twice-iterated potential is near-Perron.**  `desc₃/desc₂`:
max `45.11` over all Good level-6 cells (`tail5_out/ratio_iter3.txt`); at level 12, max `43.79`
over the three `desc₂/desc₁`-worst cells (57.3, 52.1, 47.6 there) and 25 random Good cells, all
in `[43.19, 43.79]` (`tail5_out/ratio_r2_k12.txt`, SAMPLED).  Stated for EVERY cell (no `Good449`
hypothesis, which is not hereditary): non-Good level-12 cells give `43.21–43.44`
(`tail5_out/ratio_nongood.txt`); cells with no Good descendants give `0 ≤ 0`.  Confidence 75% for `R = 45`. -/
def RegularPotential2_449 (R : ℚ) : Prop :=
  ∀ k a, descMass k a (k + 18) ≤ R * descMass k a (k + 12)

/-- **Bookkeeping theorem (statement; the crux from nodes 1, 4, 5).**  Proof plan: strong
induction on `m` for `loss m ≤ 6 · mass m` (then `tailChargeBudget449_of_ratio`).  A base-`b`
window killing in block `m+1` is charged to the progression of its stage inside an ancestor
`j_b = ⌈4.49 log₂ b / 6⌉` blocks up (spacing `2^6`, node 1); the killed weight is
`≤ C · 2b^{-4.49}` of that ancestor's descendant mass, which nodes 4 + 5 and the recurrence
bound by `K (R/(1-η))^{j_b} / (34-c)^{j_b} · mass m` with `K ≈ R(1 + c/(34-c))`.
Numerics (`python`, lap 2): with `C = 1.85` (spacing-`2^6` probe max/coverage 1.50, 1.81, 1.40,
1.26: `tail5_out/offset_probe_sp6.txt`), `R = 57`, `η = 1/100`, `K = 70`, `c = 6`:
`Σ_b ≈ 5.9 ≤ 6` — closes with almost no margin.  With node 4′ (`R = 45`, `K = 45(1 + c/(34-c))`) the sum is `1.90` at
`c = 3` and `2.65` at `c = 6`: margin `2.3×`.  The statement below uses node 4′.
Known gaps (node 1 now allows non-Good ancestors): stage counts per block
taken as `6/log₂ b + 1`.  Confidence 55%. -/
theorem tailChargeBudget449_of_nodes (h1 : APKillUniform449 6 (37 / 20))
    (h4 : RegularPotential2_449 45) (h5 : OrphanSmall449 (1 / 100)) : TailChargeBudget449 := by
  sorry

open Classical in
/-- Survivors' Good descendant weight `d` blocks down (the depth-`d` potential in totals). -/
noncomputable def potTot (d m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)), descMass (6 * m) a (6 * m + 6 * d)

open Classical in
/-- Depth-`d` potential of orphan survivors at block `m+1`. -/
noncomputable def orphanPot (d m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * (m + 1)))).filter
      (fun a => survives (6 * (m + 1)) a ∧ ¬ survives (6 * m) (a / 64)),
    descMass (6 * (m + 1)) a (6 * (m + 1) + 6 * d)

/-- **Depth-`d` totals step** (generalizes `childMassTot_succ_le`; `d = 2` is node 4′'s). -/
theorem potTot_succ_le {d : ℕ} {R : ℚ}
    (hR : ∀ k a, Good449 k a → descMass k a (k + 6 + 6 * d) ≤ R * descMass k a (k + 6 * d))
    (m : ℕ) : potTot d (m + 1) ≤ R * potTot d m + orphanPot d m := by
  classical
  have hd : ∀ k a K, 0 ≤ descMass k a K := fun k a K =>
    Finset.sum_nonneg fun _ _ => coreWeight_nonneg _ _
  unfold potTot orphanPot
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a => survives (6 * m) (a / 64)),
    Finset.filter_filter, Finset.filter_filter]
  refine add_le_add ?_ le_rfl
  rw [Finset.sum_filter]
  have e6 : 6 * (m + 1) = 6 * m + 6 := by ring
  rw [show 2 ^ (6 * (m + 1)) = 2 ^ 6 * 2 ^ (6 * m) by rw [e6, pow_add, mul_comm],
    sum_range_mul_split]
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with hp
  · calc ∑ j ∈ Finset.range (2 ^ 6), (if survives (6 * (m + 1)) (2 ^ 6 * p + j) ∧
            survives (6 * m) ((2 ^ 6 * p + j) / 64) then
            descMass (6 * (m + 1)) (2 ^ 6 * p + j) (6 * (m + 1) + 6 * d) else 0)
          ≤ ∑ j ∈ Finset.range (2 ^ 6), descMass (6 * m + 6) (2 ^ 6 * p + j) (6 * m + 6 + 6 * d) :=
            Finset.sum_le_sum fun j _ => by
              split_ifs
              · rw [e6]
              · exact hd _ _ _
        _ = descMass (6 * m) p (6 * m + 6 + 6 * d) := (descMass_split _ _ _).symm
        _ ≤ R * descMass (6 * m) p (6 * m + 6 * d) := hR _ _ hp.1
  · rw [mul_zero]
    refine Finset.sum_nonpos (ι := ℕ) (N := ℚ) fun j hj => ?_
    split_ifs with h
    · exfalso; apply hp
      have : (2 ^ 6 * p + j) / 64 = p := by
        have := Finset.mem_range.1 hj; omega
      exact this ▸ h.2
    · exact le_rfl

/-- Node 4′ is the `d = 2` hypothesis of `potTot_succ_le`. -/
theorem potTot_two_succ_le {R : ℚ} (hR : RegularPotential2_449 R) (m : ℕ) :
    potTot 2 (m + 1) ≤ R * potTot 2 m + orphanPot 2 m :=
  potTot_succ_le (fun k a _ => by
    have := hR k a
    rwa [show k + 6 + 6 * 2 = k + 18 by ring, show k + 6 * 2 = k + 12 by ring]) m

/-- **Child mass = surviving children + lost children** (upper half): the Good children of
survivors either survive (and are counted in `mass (m+1)`) or are lost. -/
theorem childMassTot_le (m : ℕ) : childMassTot m ≤ mass (m + 1) + loss m := by
  classical
  unfold childMassTot mass loss
  set S := (Finset.range (2 ^ (6 * m))).filter (survives (6 * m))
  have hS : ∀ a ∈ S, a < 2 ^ (6 * m) := fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hsplit : ∀ a ∈ S, descMass (6 * m) a (6 * (m + 1)) =
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good449 (6 * (m + 1)) (64 * a + j) ∧ Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j)),
        coreWeight (6 * (m + 1)) (64 * a + j) +
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good449 (6 * (m + 1)) (64 * a + j) ∧ ¬ Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j)),
        coreWeight (6 * (m + 1)) (64 * a + j) := by
    intro a _
    unfold descMass
    rw [show 6 * (m + 1) - 6 * m = 6 by omega,
      show (2 : ℕ) ^ 6 = 64 by norm_num, ← Finset.sum_union]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => h2.2 h1.2
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  gcongr
  have := sum_children_le hS
    (fun a j => Good449 (6 * (m + 1)) (64 * a + j) ∧
      Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j))
    (survives (6 * (m + 1))) (fun a _ j _ h => h) (coreWeight (6 * (m + 1)))
    (coreWeight_nonneg _)
  rwa [show 6 * m + 6 = 6 * (m + 1) by ring] at this

/-- **Node 4′ propagates to every depth `d ≥ 2`** (split over the 64 children and induct). -/
theorem regularPotential_iter {R : ℚ} (hR : RegularPotential2_449 R) (hR0 : 0 ≤ R) :
    ∀ d, ∀ k a, descMass k a (k + 6 * (d + 3)) ≤ R * descMass k a (k + 6 * (d + 2))
  | 0, k, a => by simpa using hR k a
  | d + 1, k, a => by
    rw [show k + 6 * (d + 1 + 3) = k + 6 + 6 * (d + 3) by ring,
      show k + 6 * (d + 1 + 2) = k + 6 + 6 * (d + 2) by ring,
      descMass_split, descMass_split, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := regularPotential_iter hR hR0 d (k + 6) (2 ^ 6 * a + j)
      simpa [add_assoc] using this

open Classical in
/-- **Alive potential** (lap 2 architecture, no orphans): depth-`d` Good descendant weight of ALL
tail-alive level-`6m` cells (Good or not).  Aliveness is hereditary, so its one-block step needs
no orphan term; node 4′ (now for every cell) drives it. -/
noncomputable def alivePot (d m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (Count.Alive tailBad449 (6 * m)),
    descMass (6 * m) a (6 * m + 6 * d)

/-- **Orphan-free totals step** for the alive potential, from node 4′. -/
theorem alivePot_succ_le {R : ℚ} (hR : RegularPotential2_449 R) (hR0 : 0 ≤ R) (m : ℕ) :
    alivePot 2 (m + 1) ≤ R * alivePot 2 m := by
  classical
  have hd : ∀ k a K, 0 ≤ descMass k a K := fun k a K =>
    Finset.sum_nonneg fun _ _ => coreWeight_nonneg _ _
  unfold alivePot
  have e6 : 6 * (m + 1) = 6 * m + 6 := by ring
  rw [Finset.sum_filter, show 2 ^ (6 * (m + 1)) = 2 ^ 6 * 2 ^ (6 * m) by rw [e6, pow_add, mul_comm],
    sum_range_mul_split, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with hp
  · calc ∑ j ∈ Finset.range (2 ^ 6), (if Count.Alive tailBad449 (6 * (m + 1)) (2 ^ 6 * p + j) then
            descMass (6 * (m + 1)) (2 ^ 6 * p + j) (6 * (m + 1) + 6 * 2) else 0)
          ≤ ∑ j ∈ Finset.range (2 ^ 6), descMass (6 * m + 6) (2 ^ 6 * p + j) (6 * m + 6 + 12) :=
            Finset.sum_le_sum fun j _ => by
              split_ifs
              · rw [e6]
              · exact hd _ _ _
        _ = descMass (6 * m) p (6 * m + 6 + 12) := (descMass_split _ _ _).symm
        _ ≤ R * descMass (6 * m) p (6 * m + 6 * 2) := by
            have := hR (6 * m) p
            rwa [show 6 * m + 18 = 6 * m + 6 + 12 by ring, show 6 * m + 12 = 6 * m + 6 * 2 by ring]
              at this
  · rw [mul_zero]
    refine Finset.sum_nonpos (ι := ℕ) (N := ℚ) fun j hj => ?_
    split_ifs with h
    · exfalso; apply hp
      have h' := Count.alive_anc tailBad449 6 (by rwa [e6] at h)
      have : (2 ^ 6 * p + j) / 2 ^ 6 = p := by
        have := Finset.mem_range.1 hj; omega
      rwa [this] at h'
    · exact le_rfl

/-- `sum_children_le` for descendants `L` levels down. -/
theorem sum_desc_le {S : Finset ℕ} {K L : ℕ} (hS : ∀ a ∈ S, a < 2 ^ K)
    (P : ℕ → ℕ → Prop) [∀ a j, Decidable (P a j)] (Q : ℕ → Prop) [DecidablePred Q]
    (hPQ : ∀ a ∈ S, ∀ j < 2 ^ L, P a j → Q (2 ^ L * a + j)) (f : ℕ → ℚ) (hf : ∀ c, 0 ≤ f c) :
    ∑ a ∈ S, ∑ j ∈ (Finset.range (2 ^ L)).filter (P a), f (2 ^ L * a + j) ≤
      ∑ c ∈ (Finset.range (2 ^ (K + L))).filter Q, f c := by
  have hL : 0 < 2 ^ L := by positivity
  have e : ∑ a ∈ S, ∑ j ∈ (Finset.range (2 ^ L)).filter (P a), f (2 ^ L * a + j) =
      ∑ p ∈ (S ×ˢ Finset.range (2 ^ L)).filter (fun p => P p.1 p.2), f (2 ^ L * p.1 + p.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_filter]
  rw [e, ← Finset.sum_image (g := fun p : ℕ × ℕ => 2 ^ L * p.1 + p.2)
    (f := f) (fun p hp q hq h => by
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
        at hp hq
      simp only at h
      have h1 : (2 ^ L * p.1 + p.2) / 2 ^ L = p.1 := by
        rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hp.1.2, add_zero]
      have h2 : (2 ^ L * q.1 + q.2) / 2 ^ L = q.1 := by
        rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hq.1.2, add_zero]
      have h3 : (2 ^ L * p.1 + p.2) % 2 ^ L = p.2 := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp.1.2]
      have h4 : (2 ^ L * q.1 + q.2) % 2 ^ L = q.2 := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hq.1.2]
      ext
      · rw [← h1, ← h2, h]
      · rw [← h3, ← h4, h])]
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) (fun c _ _ => hf c)
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hc
    obtain ⟨⟨a, j⟩, ⟨⟨ha, hj⟩, hp⟩, rfl⟩ := hc
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hPQ a ha j hj hp⟩
    have := hS a ha
    rw [pow_add]
    calc 2 ^ L * a + j < 2 ^ L * a + 2 ^ L := by omega
      _ = 2 ^ L * (a + 1) := by ring
      _ ≤ 2 ^ L * 2 ^ K := Nat.mul_le_mul_left _ this
      _ = 2 ^ K * 2 ^ L := by ring

open Classical in
/-- **Two-block extended loss**: Good weight at level `6m+12` under tail-alive level-`6m`
cells (Good or not) that is killed by level `6m+12`. -/
noncomputable def extLoss (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (Count.Alive tailBad449 (6 * m)),
    ∑ i ∈ (Finset.range (2 ^ 12)).filter (fun i =>
      Good449 (6 * m + 12) (2 ^ 12 * a + i) ∧ ¬ Count.Alive tailBad449 (6 * m + 12) (2 ^ 12 * a + i)),
      coreWeight (6 * m + 12) (2 ^ 12 * a + i)

/-- **Mass from the alive potential**: `alivePot 2 m ≤ mass (m+2) + extLoss m`. -/
theorem alivePot_le (m : ℕ) : alivePot 2 m ≤ mass (m + 2) + extLoss m := by
  classical
  unfold alivePot extLoss mass
  set S := (Finset.range (2 ^ (6 * m))).filter (Count.Alive tailBad449 (6 * m))
  have hS : ∀ a ∈ S, a < 2 ^ (6 * m) := fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hsplit : ∀ a ∈ S, descMass (6 * m) a (6 * m + 6 * 2) =
      ∑ i ∈ (Finset.range (2 ^ 12)).filter (fun i =>
          Good449 (6 * m + 12) (2 ^ 12 * a + i) ∧ Count.Alive tailBad449 (6 * m + 12) (2 ^ 12 * a + i)),
        coreWeight (6 * m + 12) (2 ^ 12 * a + i) +
      ∑ i ∈ (Finset.range (2 ^ 12)).filter (fun i =>
          Good449 (6 * m + 12) (2 ^ 12 * a + i) ∧ ¬ Count.Alive tailBad449 (6 * m + 12) (2 ^ 12 * a + i)),
        coreWeight (6 * m + 12) (2 ^ 12 * a + i) := by
    intro a _
    unfold descMass
    rw [show 6 * m + 6 * 2 - 6 * m = 12 by omega, show 6 * m + 6 * 2 = 6 * m + 12 by ring,
      ← Finset.sum_filter_add_sum_filter_not _
        (fun i => Count.Alive tailBad449 (6 * m + 12) (2 ^ 12 * a + i)),
      Finset.filter_filter, Finset.filter_filter]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  gcongr
  have := sum_desc_le (L := 12) hS
    (fun a i => Good449 (6 * m + 12) (2 ^ 12 * a + i) ∧
      Count.Alive tailBad449 (6 * m + 12) (2 ^ 12 * a + i))
    (survives (6 * (m + 2))) (fun a _ i _ h => by
      rw [show 6 * (m + 2) = 6 * m + 12 by ring]; exact h) (coreWeight (6 * (m + 2)))
    (coreWeight_nonneg _)
  rwa [show 6 * m + 12 = 6 * (m + 2) by ring] at this

/-- Intervals of half-width `h` around the progression `(A + θ)/q`. -/
def apNbhd (q : ℕ) (θ h : ℝ) (A : ℤ) : Set ℝ :=
  Set.Icc (((A : ℝ) + θ) / q - h) (((A : ℝ) + θ) / q + h)

open Classical in
/-- Good level-`K` descendant weight of `(k, a)` inside the progression of intervals. -/
noncomputable def descInAP (k a K q : ℕ) (θ h : ℝ) : ℚ :=
  ∑ j ∈ (Finset.range (2 ^ (K - k))).filter (fun j => Good449 K (2 ^ (K - k) * a + j) ∧
      ∃ A : ℤ, Count.cell K (2 ^ (K - k) * a + j) ⊆ apNbhd q θ h A),
    coreWeight K (2 ^ (K - k) * a + j)

/-- **Node 1″ (conjecture): AP-equidistribution of the core at every width.**  Generalizes node 1
from window widths to ANY half-width `h` (needed for the edge kills of coarse windows: a level-`6m`
cell straddling the endpoint of an earlier, wider window loses the descendants inside it, i.e.
inside a one-sided `2^{-6m}`-neighbourhood of the endpoint progression; charging those at the
spacing scale costs `(2^{-6m} q) R^j ≈ (R/64ρ)^j`, which converges, whereas charging with window
coverage diverges like `(R/ρ)^j`, `R ≈ 45 > ρ = 34`).  Resonant bases (lap 2,
`tail5_out/offset_probe_resonant.txt`, root, level 24): max/coverage `1.93` (12²), `1.48` (6³),
`1.06` (6⁴), `1.55` (10²), `1.03` (5⁴).  General widths (root, level 20, `h = 2^{-13..-17}`,
`tail5_out/offset_probe_width.txt`): max/(2hq) in `[0.99, 1.49]` (worst 12² at `h = 2^{-15}`).
**Lap 2 later: very likely FALSE as stated (confidence 10%).**  At fixed `q` and shrinking `h`
the max/(2hq) ratio grows like `(hq)^{-0.09}` (root, `q = 5`: `1.18, 1.51, 1.97` at
`h = 2^{-8}, 2^{-12}, 2^{-16}`, `tail5_out/offset_probe_coarse.txt`): the offset max picks points of
local dimension below 1 (core dimension `≈ log 44 / log 64 ≈ 0.91`).  Use `APKillFrostman449`. -/
def APKillGeneral449 (s : ℕ) (C : ℝ) : Prop :=
  ∀ k a K q (θ h : ℝ), k ≤ K → 2 ^ (k + s) ≤ q → 0 ≤ h →
    (descInAP k a K q θ h : ℝ) ≤ C * (2 * h * q) * descMass k a K

/-- **Node 1‴ (conjecture): Frostman form of the AP bound.**  The killed fraction is at most
`C · (2hq)^α` with `α < 1` (fits the coarse trend with `α ≈ 0.9`).  Windows: `2hq = 2b^{-4.49}`,
so the base sum stays summable (`b^{-4.49α}`); endpoint neighbourhoods: `(2^{-6m} q)^α R^j` still
converges since `64^α ρ ≫ R`.  Single-interval Frostman at the root, level 20
(`scripts/cstar_models/tail5_frostman.py`, `tail5_out/frostman_K20.txt`): max over x of
`μ[x, x+2^{-t}]/μ` is `2^{-α_t t}` with `α_t` from 0.909 (t = 2) to 0.902 (t = 18): the weighted
core is `0.90`-Frostman with constant about 1.  Confidence 65% for `C = 2`, `α = 17/20`, `s = 0`. -/
def APKillFrostman449 (s : ℕ) (C α : ℝ) : Prop :=
  ∀ k a K q (θ h : ℝ), k ≤ K → 2 ^ (k + s) ≤ q → 0 ≤ h →
    (descInAP k a K q θ h : ℝ) ≤ C * (2 * h * q) ^ α * descMass k a K

theorem cell_anc_sub : ∀ (d k c : ℕ), Count.cell (k + d) c ⊆ Count.cell k (c / 2 ^ d)
  | 0, k, c => by simp
  | d + 1, k, c => by
    refine (Count.cell_succ_sub (k + d) c).trans ?_
    have := cell_anc_sub d k (c / 2)
    rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

/-- A cell dead at level `k+d` whose level-`k` ancestor is alive was killed at some level
`k+e`, `0 < e ≤ d`, by its own ancestor there. -/
theorem killed_between {B : ℕ → ℕ → Prop} :
    ∀ (d k c : ℕ), Count.Alive B k (c / 2 ^ d) → ¬ Count.Alive B (k + d) c →
      ∃ e, 0 < e ∧ e ≤ d ∧ B (k + e) (c / 2 ^ (d - e))
  | 0, k, c, h, hn => absurd (by simpa using h) hn
  | d + 1, k, c, h, hn => by
    by_cases hp : Count.Alive B (k + d) (c / 2)
    · refine ⟨d + 1, by omega, le_rfl, ?_⟩
      by_contra hb
      rw [Nat.sub_self, pow_zero, Nat.div_one] at hb
      exact hn ⟨hp, hb⟩
    · have h' : Count.Alive B k (c / 2 / 2 ^ d) := by
        rwa [Nat.div_div_eq_div_mul, ← pow_succ']
      obtain ⟨e, he0, hed, hbe⟩ := killed_between d k (c / 2) h' hp
      refine ⟨e, he0, by omega, ?_⟩
      rwa [Nat.div_div_eq_div_mul, ← pow_succ', show d - e + 1 = d + 1 - e by omega] at hbe

open Classical in
/-- Good weight at `6m+12` under alive `6m`-cells that lies inside some tail window. -/
noncomputable def killedTot (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (Count.Alive tailBad449 (6 * m)),
    ∑ i ∈ (Finset.range (2 ^ 12)).filter (fun i =>
      Good449 (6 * m + 12) (2 ^ 12 * a + i) ∧ tailBad449 (6 * m + 12) (2 ^ 12 * a + i)),
      coreWeight (6 * m + 12) (2 ^ 12 * a + i)

/-- **Every extended loss is a window containment at the bottom level.** -/
theorem extLoss_le_killedTot (m : ℕ) : extLoss m ≤ killedTot m := by
  classical
  unfold extLoss killedTot
  refine Finset.sum_le_sum fun a ha => ?_
  have hal := (Finset.mem_filter.1 ha).2
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
    (fun _ _ _ => coreWeight_nonneg _ _)
  obtain ⟨hir, hg, hna⟩ := Finset.mem_filter.1 hi
  refine Finset.mem_filter.2 ⟨hir, hg, ?_⟩
  have hdiv : (2 ^ 12 * a + i) / 2 ^ 12 = a := by
    have := Finset.mem_range.1 hir; omega
  obtain ⟨e, he0, he12, hb⟩ := killed_between (B := tailBad449) 12 (6 * m) (2 ^ 12 * a + i)
    (by rwa [hdiv]) hna
  obtain ⟨b, h5, hpp, n, A, hsub⟩ := hb
  refine ⟨b, h5, hpp, n, A, ?_⟩
  refine (?_ : Count.cell (6 * m + 12) (2 ^ 12 * a + i) ⊆ _).trans hsub
  have := cell_anc_sub (12 - e) (6 * m + e) (2 ^ 12 * a + i)
  rwa [show 6 * m + e + (12 - e) = 6 * m + 12 by omega] at this

end NormalNumbers.UniformBadThreshold.TailReview
