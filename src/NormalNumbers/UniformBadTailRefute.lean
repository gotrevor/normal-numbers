/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailMechanism

/-!
# Gate 5 review (lap 3): the per-cell nodes are false; the crux is a totals statement

The lap-2 architecture (`UniformBadTailMechanism.lean`) reduces the crux `TailChargeBudget449` to
RELATIVE bounds at single cells: the AP kill nodes `APKillUniform449` (node 1) and
`APKillFrostman449` (node 1‴), and the potential ratios `RegularPotential449` (node 4) and
`RegularPotential2_449` (node 4′).  Each is quantified over every cell `(k, a)`.

**Mechanism of failure: concentrated cells.**  A cell whose positive Good descendants all sit in a
short sub-interval breaks every bound normalized by the cell's own descendant mass.  Such cells are
produced by window edges.  A base-2 or base-3 window edge cuts the cell, the binary follower set of
the cell's suffix has a hull strictly inside the cell (no five equal digits), and the edge can land
next to a hull end.  The cell position `a` moves the edge in steps of about `2^-k` of the cell, so
concentration of every depth occurs at deep enough levels (`ConcentratedCells449`, believed).

**Exact witnesses** (`scripts/cstar_models/tail5_concentrate*.py`, `tail5_hull.py`,
`tail5_node1_witness.py`; integer arithmetic, `5^-4.49`/`3^-4.49` enclosed at 60 digits, no
ambiguous comparisons; EXHAUSTIVE over the stated levels, so these are certified maxima, not
samples):
* node 4: Good cell `(10, 573)`, `descMass(+12)/descMass(+6) = 71.62 > 60`; the exhaustive maximum over
  Good cells with `k ≤ 12` is `71.62` (`44.4, 46.4, 48.3, 49.3, 54.4, 71.6, 59.0, 68.8` at
  `k = 0, 6..12`), against lap 2's sampled `57.3`.
* node 4′: Good cell `(6, 61)`, ratio `45.1115 > 45` (the exhaustive maximum over `k ≤ 6`; lap 2 had
  already measured it as `45.11` and still stated `R = 45`).
* node 1‴: cell `(13, 808)` (not Good): its positive Good level-25 descendants are exactly the four
  cells `2^12 · 808 + 1460 … 1463`, a relative hull of `2^-10`; at `k = 6`, cell `(6, 2)` has hull
  `0.1035` at depth 12.
* node 1: the same cell `(13, 808)` at level 32: one base-5 stage-9 window (`5^9 ≥ 2^(13+6)`) captures
  `1.046%` of the descendant mass, against the node's allowance `(37/20) · 2 · 5^-4.49 = 0.269%`.

So `tailChargeBudget449_of_nodes` has two false hypotheses (`h1`, `h4`).  The crux itself is not
touched: in totals, `loss m / mass m ≈ 0.23` (lap 1).  What a proof needs is control of the TOTAL
survivor distribution: concentrated cells carry little mass, but no single-cell bound can see that.
`tailChargeBudget449_of_upperGrowth_kill` records the totals form with its very large slack (kill
fraction `ε` and upper growth `Λ` with `ε Λ < (9/5)^6 - 1 ≈ 33`; measured `ε ≈ 0.005`, `Λ ≈ 44`).
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

open Coherent

/-! ### Node 1‴: a concentrated cell refutes the Frostman AP bound -/

/-- `APKillFrostman449` gets weaker as `s` grows (fewer progressions are constrained). -/
theorem apKillFrostman449_mono {s s' : ℕ} {C α : ℝ} (hs : s ≤ s') (h : APKillFrostman449 s C α) :
    APKillFrostman449 s' C α := fun k a K q θ hh hkK hq h0 =>
  h k a K q θ hh hkK ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hq) h0

/-- **Hull refutation of node 1‴.**  If the positive Good level-`K` descendants of `(k, a)` lie in
the `v - u` consecutive cells `u … v - 1` (relative length `(v - u)/2^(K-k)`), the descendant mass is
positive and `C · ((v - u)/2^(K-k) · 2^s)^α < 1`, then `APKillFrostman449 s C α` fails: one interval
of the progression with spacing `2^-(k+s)` covers the whole hull. -/
theorem not_apKillFrostman449_of_hull {s : ℕ} {C α : ℝ} {k a K u v : ℕ} (hkK : k ≤ K)
    (huv : u ≤ v)
    (hin : ∀ j < 2 ^ (K - k), Good449 K (2 ^ (K - k) * a + j) →
      0 < coreWeight K (2 ^ (K - k) * a + j) → u ≤ j ∧ j < v)
    (hpos : 0 < descMass k a K)
    (hsmall : C * (((v : ℝ) - u) / 2 ^ (K - k) * 2 ^ s) ^ α < 1) :
    ¬ APKillFrostman449 s C α := by
  classical
  intro hF
  set L := K - k with hL
  have hK : (2 : ℝ) ^ K = 2 ^ L * 2 ^ k := by rw [← pow_add, hL, Nat.sub_add_cancel hkK]
  set q : ℕ := 2 ^ (k + s) with hq
  have hq0 : (0 : ℝ) < q := by rw [hq]; positivity
  set c : ℝ := ((2 : ℝ) ^ L * a + ((u : ℝ) + v) / 2) / 2 ^ K with hc
  set hh : ℝ := ((v : ℝ) - u) / 2 / 2 ^ K with hhh
  have huvR : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hh0 : 0 ≤ hh := by rw [hhh]; apply div_nonneg _ (by positivity); linarith
  have key := hF k a K q (q * c) hh hkK le_rfl hh0
  -- the descendant mass is at most the mass inside the progression
  have hle : descMass k a K ≤ descInAP k a K q (q * c) hh := by
    unfold descMass descInAP
    rw [← hL]
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun j => 0 < coreWeight K (2 ^ L * a + j)),
      Finset.filter_filter]
    have hzero : ∑ j ∈ ((Finset.range (2 ^ L)).filter (fun j => Good449 K (2 ^ L * a + j))).filter
        (fun j => ¬ 0 < coreWeight K (2 ^ L * a + j)), coreWeight K (2 ^ L * a + j) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        have := (Finset.mem_filter.1 hj).2
        exact le_antisymm (not_lt.1 this) (coreWeight_nonneg _ _)
    rw [hzero, add_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => coreWeight_nonneg _ _)
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjr, hg, hw⟩ := hj
    refine ⟨hjr, hg, 0, ?_⟩
    obtain ⟨huj, hjv⟩ := hin j hjr hg hw
    have hujR : (u : ℝ) ≤ j := by exact_mod_cast huj
    have hjvR : (j : ℝ) + 1 ≤ v := by exact_mod_cast hjv
    unfold Count.cell apNbhd
    apply Set.Icc_subset_Icc
    · rw [show ((((0 : ℤ) : ℝ) + q * c) / q) = c by rw [Int.cast_zero, zero_add]; field_simp]
      rw [hc, hhh]; push_cast
      rw [div_sub_div_same, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    · rw [show ((((0 : ℤ) : ℝ) + q * c) / q) = c by rw [Int.cast_zero, zero_add]; field_simp]
      rw [hc, hhh]; push_cast
      rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
  -- the progression's density is the hull's relative length times 2^s
  have h2 : 2 * hh * q = ((v : ℝ) - u) / 2 ^ L * 2 ^ s := by
    rw [hhh, hq]; push_cast; rw [hK, pow_add]; field_simp
  rw [h2] at key
  have hposR : (0 : ℝ) < descMass k a K := by exact_mod_cast hpos
  have hleR : (descMass k a K : ℝ) ≤ descInAP k a K q (q * c) hh := by exact_mod_cast hle
  have : C * (((v : ℝ) - u) / 2 ^ L * 2 ^ s) ^ α * descMass k a K < descMass k a K := by
    nlinarith
  linarith

/-- Exact finite fact (tail5_hull.py, independently re-derived by DFS in `/tmp/w808.py`): the cell
`(13, 808)` is NOT Good, and its positive-weight Good level-25 descendants are exactly the offsets
`1460, 1461, 1462, 1463` (weights `0.644, 0.380, 0.884, 0.567` of `maxW`), with no Good descendant of
weight zero.  Confidence 97% (the residual risk is the Python model of `classify`, checked against
the gate-4 root sum and the delete-all control in lap 1).  Proof route: evaluate `Good449` on the
`2^12` level-25 descendants by the `windows_sound` machinery. -/
theorem hull_13_808 : ∀ j < 2 ^ (25 - 13), Good449 25 (2 ^ (25 - 13) * 808 + j) →
    0 < coreWeight 25 (2 ^ (25 - 13) * 808 + j) → 1460 ≤ j ∧ j < 1464 := by
  sorry

/-- Exact finite fact: `descMass 13 808 25 = 2655262458957 / 1072633893121 > 0` (same evidence and
confidence as `hull_13_808`). -/
theorem descMass_13_808_pos : 0 < descMass 13 808 25 := by
  sorry

/-- **Node 1‴ is false at `s ≤ 8`, `C = 2`, `α = 17/20`** (lap 2 stated `s = 0` at 65%; the
bookkeeping wanted `s = 6`).  The hull of `(13, 808)` has relative length `2^-10`, so
`2 · (2^-10 · 2^8)^(17/20) = 2 · (1/4)^(17/20) < 1`. -/
theorem not_apKillFrostman449_eight : ¬ APKillFrostman449 8 2 (17 / 20) := by
  refine not_apKillFrostman449_of_hull (k := 13) (a := 808) (K := 25) (u := 1460) (v := 1464)
    (by norm_num) (by norm_num) hull_13_808 descMass_13_808_pos ?_
  have e : (((1464 : ℕ) : ℝ) - ((1460 : ℕ) : ℝ)) / 2 ^ (25 - 13) * 2 ^ 8 = 1 / 4 := by norm_num
  rw [e]
  have h1 : ((1 : ℝ) / 4) ^ ((17 : ℝ) / 20) < (1 / 4) ^ ((1 : ℝ) / 2) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)
  have h2 : ((1 : ℝ) / 4) ^ ((1 : ℝ) / 2) = 1 / 2 := by
    rw [show ((1 : ℝ) / 4) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

theorem not_apKillFrostman449_six : ¬ APKillFrostman449 6 2 (17 / 20) := fun h =>
  not_apKillFrostman449_eight (apKillFrostman449_mono (by norm_num) h)

theorem not_apKillFrostman449_zero : ¬ APKillFrostman449 0 2 (17 / 20) := fun h =>
  not_apKillFrostman449_eight (apKillFrostman449_mono (by norm_num) h)

/-- **Concentrated cells at every depth** (believed, 80%).  For every `t` some cell has positive
descendant mass at some level `K`, all of it in `2^(K-k-t)` consecutive level-`K` cells (relative
length `2^-t`).  English argument: take a cell whose binary suffix forces its followers into a hull
`[inf, sup]` strictly inside the cell, and a base-3 window edge just below `sup`; the edge's relative
position moves in steps of about `2^-k` as `a` varies over cells with that suffix, so for large `k`
some cell has its edge within `2^-t` of `sup` while the region just below `sup` still carries Good
descendants.  Evidence: exhaustive minimal hulls `2^-3.3` (`k = 6`), `2^-10` (`k = 13`, depth 12);
Good cells whose positive mass sits in a single child (`k = 14..19`, depth 6). -/
def ConcentratedCells449 : Prop :=
  ∀ t : ℕ, ∃ k a K u : ℕ, k + t ≤ K ∧
    (∀ j < 2 ^ (K - k), Good449 K (2 ^ (K - k) * a + j) →
      0 < coreWeight K (2 ^ (K - k) * a + j) → u ≤ j ∧ j < u + 2 ^ (K - k - t)) ∧
    0 < descMass k a K

/-- **No per-cell Frostman AP bound survives concentration**: under `ConcentratedCells449`,
`APKillFrostman449 s C α` is false for EVERY `s`, `C` and `α > 0`. -/
theorem not_apKillFrostman449_of_concentrated (hc : ConcentratedCells449) {s : ℕ} {C α : ℝ}
    (hα : 0 < α) : ¬ APKillFrostman449 s C α := by
  -- choose t with C · (2^(s-t))^α < 1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, C * ((1 / 2 : ℝ) ^ t * 2 ^ s) ^ α < 1 := by
    have hlim : Filter.Tendsto (fun t : ℕ => C * ((1 / 2 : ℝ) ^ t * 2 ^ s) ^ α) Filter.atTop
        (nhds (C * ((0 : ℝ) * 2 ^ s) ^ α)) := by
      refine Filter.Tendsto.const_mul _ ?_
      refine ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const
        _).rpow_const (Or.inr hα.le)
    rw [zero_mul, Real.zero_rpow hα.ne', mul_zero] at hlim
    exact (hlim.eventually (gt_mem_nhds (by norm_num))).exists
  obtain ⟨k, a, K, u, hkt, hin, hpos⟩ := hc t
  refine not_apKillFrostman449_of_hull (u := u) (v := u + 2 ^ (K - k - t)) (by omega)
    (Nat.le_add_right _ _) hin hpos ?_
  have hM : (2 : ℝ) ^ (K - k) = 2 ^ (K - k - t) * 2 ^ t := by
    rw [← pow_add]; congr 1; omega
  have e : (((u + 2 ^ (K - k - t) : ℕ) : ℝ) - u) / 2 ^ (K - k) = (1 / 2) ^ t := by
    push_cast
    rw [add_sub_cancel_left, hM, one_div, inv_pow]
    field_simp
  rw [e]; exact ht

/-! ### Nodes 1, 4 and 4′: exact counterexamples at the stated constants -/

/-- **Node 1 is false at the bookkeeping's constants** (`s = 6`, `C = 37/20`).  Witness: the
concentrated cell `(13, 808)` at `K = 32`, base 5, stage 9 (`5^9 = 1953125 ≥ 2^19`), offset centring
one window on the level-32 cell `423811625`: killed weight `2841346892346/1072633893121` (`1.046%`)
out of `descMass 13 808 32 = 271754277609887/1072633893121`, against the allowance
`(37/20) · 2 · 5^-4.49 ≤ 0.269%` (`tail5_node1_witness.py`, exact; confidence 95%). -/
theorem not_apKillUniform449 : ¬ APKillUniform449 6 (37 / 20) := by
  sorry

/-- **Node 4 is false at `R = 60`** (lap 2: 65%).  Witness: the Good cell `(10, 573)` with
`descMass 10 573 16 = 1420238965641/1072633893121` and
`descMass 10 573 22 = 101717702140853/1072633893121`, ratio `71.62` (exact; confidence 97%). -/
theorem not_regularPotential449_sixty : ¬ RegularPotential449 60 := by
  sorry

/-- **Node 4′ is false at `R = 45`** (lap 2: 75%, used by `tailChargeBudget449_of_nodes`).
Witness: the Good cell `(6, 61)` with `descMass 6 61 18 = 217633727556855/1072633893121` and
`descMass 6 61 24 = 9817794482527296/1072633893121`, ratio `45.1115` (exact; confidence 97%). -/
theorem not_regularPotential2_449_45 : ¬ RegularPotential2_449 45 := by
  sorry

/-! ### The crux in totals -/

/-- **Totals kill fraction** (open): the tail kills at most a fraction `ε` of the Good child
weight of the survivors.  Measured `≈ 0.005` (lap 1: loss/mass `0.23` with child mass `≈ 44` mass). -/
def TotalsKill449 (ε : ℚ) : Prop := ∀ m, loss m ≤ ε * childMassTot m

theorem mass_nonneg (m : ℕ) : 0 ≤ mass m :=
  Finset.sum_nonneg fun _ _ => coreWeight_nonneg _ _

/-- **The crux from two totals statements**, with very large slack: any kill fraction `ε` and
upper growth `Λ` with `ε Λ < (9/5)^6 - 1 ≈ 33` (e.g. `ε = 1/4`, `Λ = 120`) suffice. -/
theorem tailChargeBudget449_of_upperGrowth_kill {ε Λ : ℚ} (hε : 0 ≤ ε)
    (hεΛ : ε * Λ < (9 / 5 : ℚ) ^ 6 - 1) (hup : UpperGrowth449 Λ) (hk : TotalsKill449 ε) :
    TailChargeBudget449 := by
  have hΛ : 0 ≤ ε * Λ ∨ ε * Λ < 0 := le_or_gt 0 (ε * Λ)
  refine tailChargeBudget449_of_ratio (c := max (ε * Λ) 0) (le_max_right _ _)
    (max_lt hεΛ (by norm_num)) fun m => ?_
  calc loss m ≤ ε * childMassTot m := hk m
    _ ≤ ε * (Λ * mass m) := mul_le_mul_of_nonneg_left (hup m) hε
    _ = (ε * Λ) * mass m := by ring
    _ ≤ max (ε * Λ) 0 * mass m := mul_le_mul_of_nonneg_right (le_max_left _ _) (mass_nonneg m)

end NormalNumbers.UniformBadThreshold.TailReview
