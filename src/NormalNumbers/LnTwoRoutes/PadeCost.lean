/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRoutes.Screen

/-!
# The bounded Padé coefficient-cost test

Read `../../../MAZE.md` and `docs/ln-two-routes/cost-test.md`.
The explicit coefficient witness and general dual inequality are proved.
The complete finite exclusion table remains exact Python certificate evidence,
stated as a Prop below.  No claim of arbitrary-word visits follows.
-/

namespace NormalNumbers.LnTwoRoutes.PadeCost

open NormalNumbers.LnTwoRoutes

def CostWitness (n width m : ℕ) (cap : ℚ) : Prop :=
  ∃ (u : ℕ → ℤ) (z : ℤ),
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).1) = 2 ^ m ∧
    (∑ j ∈ Finset.range width, (u j : ℚ) * (padePair (n + j)).2) = z ∧
    padeErrorBudget n width u < cap

def bestCoeff : ℕ → ℤ
  | 0 => -9037
  | 1 => -86624
  | 2 => 0
  | 3 => -214899
  | 4 => -1231047
  | 5 => -4837440
  | 6 => -1
  | 7 => 159938
  | _ => 0

theorem pade_cost_window_data :
    padePair 8 = (265729, 25786503/140) ∧
    padePair 9 = (1462563, 1277351989/1260) ∧
    padePair 10 = (8097453, 336763603/60) ∧
    padePair 11 = (45046719, 432764726879/13860) ∧
    padePair 12 = (251595969, 268565276291/1540) ∧
    padePair 13 = (1409933619, 58696128257959/60060) ∧
    padePair 14 = (7923848253, 109957709376551/20020) ∧
    padePair 15 = (44642381823, 428880251564129/13860) := by
  have h0 : padePair 0 = (1, 0) := rfl
  have h1 : padePair 1 = (3, 2) := rfl
  have h2 : padePair 2 = (13, 9) := by
    rw [padePair, h0, h1]
    norm_num
  have h3 : padePair 3 = (63, 131/3) := by
    rw [padePair, h1, h2]
    norm_num
  have h4 : padePair 4 = (321, 445/2) := by
    rw [padePair, h2, h3]
    norm_num
  have h5 : padePair 5 = (1683, 34997/30) := by
    rw [padePair, h3, h4]
    norm_num
  have h6 : padePair 6 = (8989, 62307/10) := by
    rw [padePair, h4, h5]
    norm_num
  have h7 : padePair 7 = (48639, 2359979/70) := by
    rw [padePair, h5, h6]
    norm_num
  have h8 : padePair 8 = (265729, 25786503/140) := by
    rw [padePair, h6, h7]
    norm_num
  have h9 : padePair 9 = (1462563, 1277351989/1260) := by
    rw [padePair, h7, h8]
    norm_num
  have h10 : padePair 10 = (8097453, 336763603/60) := by
    rw [padePair, h8, h9]
    norm_num
  have h11 : padePair 11 = (45046719, 432764726879/13860) := by
    rw [padePair, h9, h10]
    norm_num
  have h12 : padePair 12 = (251595969, 268565276291/1540) := by
    rw [padePair, h10, h11]
    norm_num
  have h13 : padePair 13 = (1409933619, 58696128257959/60060) := by
    rw [padePair, h11, h12]
    norm_num
  have h14 : padePair 14 = (7923848253, 109957709376551/20020) := by
    rw [padePair, h12, h13]
    norm_num
  have h15 : padePair 15 = (44642381823, 428880251564129/13860) := by
    rw [padePair, h13, h14]
    norm_num
  exact ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem best_witness_equations :
    (∑ j ∈ Finset.range 8, (bestCoeff j : ℚ) * (padePair (8 + j)).1) = 2 ^ 21 ∧
    (∑ j ∈ Finset.range 8, (bestCoeff j : ℚ) * (padePair (8 + j)).2) = 1453635 := by
  rcases pade_cost_window_data with ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩
  norm_num [Finset.sum_range_succ, bestCoeff, h8, h9, h10, h11, h12, h13, h14, h15]

theorem best_witness_budget :
    padeErrorBudget 8 8 bestCoeff = (2468804318 : ℚ) / 30517578125 := by
  norm_num [padeErrorBudget, Finset.sum_range_succ, bestCoeff]

/-- A finite success for the proposed construction, stronger than the 1/4 gate.
This is not the all-k PadeCheapDyadic claim. -/
@[blueprint (title := "Log-two Pade synthesis: exact finite budget below one eighth")]
theorem best_witness_passes : CostWitness 8 8 21 (1 / 8) := by
  refine ⟨bestCoeff, 1453635, best_witness_equations.1,
    best_witness_equations.2, ?_⟩
  rw [best_witness_budget]
  norm_num

/-- The rational enclosure underlying the probe is an instance of this
already-proved Mercator remainder estimate. -/
theorem mercator_enclosure (N : ℕ) :
    lnTwoPartial N ≤ Real.log 2 ∧
    Real.log 2 ≤ lnTwoPartial N + 1 / (((N : ℝ) + 1) * 2 ^ N) := by
  refine ⟨lnTwoPartial_le_log_two N, ?_⟩
  have ht := lnTwoTail_le N
  rw [lnTwoTail] at ht
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have hr : Real.log 2 - lnTwoPartial N ≤ (1 / ((N : ℝ) + 1)) / 2 ^ N :=
    (le_div_iff₀ hp).2 (by simpa [mul_comm] using ht)
  rw [div_div] at hr
  linarith

/-- General weighted dual bound.  The probe bounds each exact error by R
times its cost weight, then lower-bounds the distance of the dyadic target
to every integer.  Thus its exclusions quantify over ALL coefficient vectors. -/
theorem weighted_dual_bound (s : Finset ℕ) (u E w : ℕ → ℝ) (R δ : ℝ)
    (hR : 0 < R) (hδ : δ ≤ |∑ j ∈ s, u j * E j|)
    (hE : ∀ j ∈ s, |E j| ≤ R * w j) :
    δ / R ≤ ∑ j ∈ s, |u j| * w j := by
  have hb : |∑ j ∈ s, u j * E j| ≤ R * ∑ j ∈ s, |u j| * w j := by
    calc
      _ ≤ ∑ j ∈ s, |u j * E j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ s, |u j| * |E j| := by simp only [abs_mul]
      _ ≤ ∑ j ∈ s, |u j| * (R * w j) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hE j hj) (abs_nonneg _))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  apply (div_le_iff₀ hR).2
  nlinarith [hδ.trans hb]

/-- Frozen finite result of the 512-term rational enclosure and exact dual
certificates.  It is not yet kernel-checked for all 242 excluded grid points.
The n=8,m=21 and m=22 cases have explicit passing witnesses in the probe. -/
def BoundedCostExclusions : Prop :=
  ∀ n ∈ ([4, 8, 16, 32] : List ℕ), ∀ m : ℕ, m ≤ 4 * n →
    (n, m) ∉ ([(8, 21), (8, 22)] : List (ℕ × ℕ)) →
      ¬ CostWitness n n m (1 / 4)

/-- Full finite outcome, with the second positive witness checked by Python.
The first conjunct is separately proved by best_witness_passes. -/
def BoundedCostResult : Prop :=
  CostWitness 8 8 21 (1 / 8) ∧ CostWitness 8 8 22 (1 / 4) ∧
    BoundedCostExclusions

/-- Rounded DOWN rational lower bounds for the best cost in three finite
exponent windows.  Exact bounds and their full rational certificates are
stored in cost-probe.json.  No assertion is made outside these windows. -/
def WindowCostLowerBounds : Prop :=
  ∀ sample ∈ ([(4, (3057 : ℚ) / 10000), (16, 3079 / 10000),
      (32, 24151 / 10000)] : List (ℕ × ℚ)),
    ∀ (m : ℕ) (u : ℕ → ℤ) (z : ℤ), m ≤ 4 * sample.1 →
      (∑ j ∈ Finset.range sample.1, (u j : ℚ) * (padePair (sample.1 + j)).1) = 2 ^ m →
      (∑ j ∈ Finset.range sample.1, (u j : ℚ) * (padePair (sample.1 + j)).2) = z →
      sample.2 ≤ padeErrorBudget sample.1 sample.1 u

end NormalNumbers.LnTwoRoutes.PadeCost

