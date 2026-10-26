/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirComparison
import NormalNumbers.DisjunctiveCorollaries

/-!
# Rational comparison models with any prescribed finite BBP prefix

The comparison can keep the initial value and any finite prefix exactly,
preserve the reservoir and its odd-prime poles thereafter, and approximate
the exact BBP forcing within any prescribed positive error schedule.
Its limiting target can still be rational.  Exact infinite forcing, or other
information not preserved here, is therefore essential for this strategy.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

/-- Exact rational realization of the reservoir used throughout the route. -/
def rationalReservoir (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (16 : ℚ)^(n-j) *
    ((if Nat.Prime (8*j+1) ∧ s*n < 8*j+1 then 4/(8*(j : ℚ)+1) else 0) -
     (if Nat.Prime (8*j+5) ∧ s*n < 8*j+5 then 1/(8*(j : ℚ)+5) else 0))

theorem rationalReservoir_cast (s n : ℕ) :
    (rationalReservoir s n : ℝ) = reservoirS s n := by
  unfold rationalReservoir reservoirS
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> push_cast <;> rfl

noncomputable def comparisonHead (x : ℝ) (n : ℕ) : ℝ :=
  16^n * x - 16^n * piTail n

theorem comparisonHead_succ (x : ℝ) (n : ℕ) :
    comparisonHead x (n+1) - 16 * comparisonHead x n = 16 * bbpKick n := by
  unfold comparisonHead piTail piPartial
  rw [Finset.sum_range_succ, bbpTerm, pow_succ]
  have h16 : (16 : ℝ)^n ≠ 0 := by positivity
  field_simp
  ring

theorem bbpRationalHead_cast (n : ℕ) :
    (bbpRationalHead n : ℝ) = 16^n * piPartial n := by
  unfold bbpRationalHead piPartial
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
  have hpow : (16 : ℝ)^(n-j) = 16^n * (1 / 16^j) := by
    have hn : (16 : ℝ)^j ≠ 0 := by positivity
    field_simp
    rw [← pow_add, Nat.sub_add_cancel hjn]
  rw [hpow, bbpTerm, bbpKick]
  ring

/-- A positive sequence has a positive lower tolerance on any finite prefix. -/
theorem finite_prefix_tolerance (η : ℕ → ℝ) (hη : ∀ n, 0 < η n) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n ≤ N, δ < η n := by
  induction N with
  | zero =>
    refine ⟨η 0 / 2, div_pos (hη 0) (by norm_num), fun n hn => ?_⟩
    have : n = 0 := by omega
    subst n
    linarith [hη 0]
  | succ N ih =>
    obtain ⟨δ, hδ, hδN⟩ := ih
    refine ⟨min δ (η (N+1)/2), lt_min hδ (div_pos (hη (N+1)) (by norm_num)), fun n hn => ?_⟩
    by_cases h : n ≤ N
    · exact lt_of_le_of_lt (min_le_left _ _) (hδN n h)
    · have : n = N+1 := by omega
      subst n
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hη (N+1)])

theorem exists_rational_target_for_prefix (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (N : ℕ) :
    ∃ q : ℚ, ∀ n ≤ N,
      |(bbpRationalHead n : ℝ) - comparisonHead q n| < ε n := by
  obtain ⟨δ, hδ, hδN⟩ := finite_prefix_tolerance
    (fun n => ε n / (16 : ℝ)^n) (fun n => div_pos (hε n) (by positivity)) N
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show Real.pi - δ < Real.pi + δ by linarith)
  have hq : |Real.pi - (q : ℝ)| < δ := by rw [abs_lt]; constructor <;> linarith
  refine ⟨q, fun n hn => ?_⟩
  have hp : (0 : ℝ) < 16^n := by positivity
  have hδn := (lt_div_iff₀ hp).mp (hδN n hn)
  have heq : (bbpRationalHead n : ℝ) - comparisonHead q n =
      16^n * (Real.pi - q) := by
    rw [bbpRationalHead_cast, comparisonHead, piTail]
    ring
  rw [heq, abs_mul, abs_of_pos hp]
  nlinarith

/-- The finite prefix is literal equality of rationals.  After it, ALL odd-prime
poles of the prescribed reservoir survive.  The target q is rational, while
the head shadows its orbit with the SAME BBP tail, to arbitrary tolerance.
The forcing error is explicitly small but need not be zero. -/
@[blueprint (title := "Finite BBP data, odd-prime poles, and arbitrarily accurate forcing admit rational targets")]
theorem rational_comparison_with_prefix (R : ℕ → ℚ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (N : ℕ) :
    ∃ q : ℚ, ∃ S : ℕ → ℚ,
      (¬ IsDisjunctive 16 (q : ℝ)) ∧
      (∀ n ≤ N, R n + S n = bbpRationalHead n) ∧
      (∀ n, |((R n + S n : ℚ) : ℝ) - comparisonHead q n| < ε n) ∧
      (∀ n, N < n → ∀ p : ℕ, Nat.Prime p → p ≠ 2 → 1 < padicNorm p (R n) →
        padicNorm p (R n + S n) = padicNorm p (R n)) ∧
      (∀ n, |(((R (n+1) + S (n+1) : ℚ) : ℝ) -
        16 * ((R n + S n : ℚ) : ℝ)) - 16 * bbpKick n| < ε (n+1) + 16*ε n) := by
  classical
  obtain ⟨q, hq⟩ := exists_rational_target_for_prefix ε hε N
  obtain ⟨D, hD⟩ := exists_rational_residual_shadow R (comparisonHead q) ε hε
  let S : ℕ → ℚ := fun n => if n ≤ N then bbpRationalHead n - R n else D n
  have hPrefix : ∀ n ≤ N, R n + S n = bbpRationalHead n := by
    intro n hn
    simp [S, hn]
  have hShadow : ∀ n, |((R n + S n : ℚ) : ℝ) - comparisonHead q n| < ε n := by
    intro n
    by_cases hn : n ≤ N
    · rw [hPrefix n hn]
      exact hq n hn
    · simpa [S, hn] using (hD n).1
  refine ⟨q, S, ?_, hPrefix, hShadow, ?_, ?_⟩
  · intro h
    exact h.irrational ⟨q, rfl⟩
  · intro n hn p hp hp2 hR
    simpa [S, show ¬ n ≤ N by omega] using (hD n).2 p hp hp2 hR
  · intro n
    have h := forcing_defect_bound (fun n => ((R n + S n : ℚ) : ℝ))
      (comparisonHead q) ε hShadow n
    simpa only [comparisonHead_succ] using h

/-- The exact information retained by the rational comparison.  This explicitly
includes zero-seeded finite BBP data, the whole prescribed reservoir, and all
its nonintegral odd-prime poles beyond the fixed prefix. -/
structure ApproximateBBPModel (R : ℕ → ℚ) (η : ℕ → ℝ) (N : ℕ)
    (x : ℝ) (S : ℕ → ℚ) : Prop where
  prefix_eq : ∀ n ≤ N, R n + S n = bbpRationalHead n
  shadow : ∀ n, |((R n + S n : ℚ) : ℝ) - comparisonHead x n| < η n
  poles : ∀ n, N < n → ∀ p : ℕ, Nat.Prime p → p ≠ 2 → 1 < padicNorm p (R n) →
    padicNorm p (R n + S n) = padicNorm p (R n)
  forcing : ∀ n, |(((R (n+1) + S (n+1) : ℚ) : ℝ) -
    16 * ((R n + S n : ℚ) : ℝ)) - 16 * bbpKick n| < η n

theorem exists_rational_approximateBBPModel (R : ℕ → ℚ) (η : ℕ → ℝ)
    (hη : ∀ n, 0 < η n) (N : ℕ) :
    ∃ q : ℚ, ∃ S : ℕ → ℚ, ¬ IsDisjunctive 16 (q : ℝ) ∧
      ApproximateBBPModel R η N q S := by
  let ε : ℕ → ℝ := fun n => min (η n / 64) (η (n-1) / 4)
  have hε : ∀ n, 0 < ε n := fun n =>
    lt_min (div_pos (hη n) (by norm_num)) (div_pos (hη (n-1)) (by norm_num))
  obtain ⟨q, S, hq, hp, hs, hPole, hf⟩ := rational_comparison_with_prefix R ε hε N
  refine ⟨q, S, hq, ⟨hp, ?_, hPole, ?_⟩⟩
  · intro n
    have he : ε n ≤ η n / 64 := min_le_left _ _
    have := hs n
    linarith [hη n]
  · intro n
    have he : ε n ≤ η n / 64 := min_le_left _ _
    have he' : ε (n+1) ≤ η n / 4 := by
      simpa only [ε, Nat.add_sub_cancel] using (min_le_right (η (n+1)/64) (η (n+1-1)/4))
    have := hf n
    linarith [hη n]

/-- Candidate strategy: some positive error budget and finite exact prefix,
together with the fixed reservoir and its surviving poles, force disjunctivity.
This is FALSE, including for the actual cutoff-six rational reservoir. -/
def RobustBBPCouplingCriterion (R : ℕ → ℚ) : Prop :=
  ∃ η : ℕ → ℝ, (∀ n, 0 < η n) ∧ ∃ N : ℕ,
    ∀ x : ℝ, ∀ S : ℕ → ℚ, ApproximateBBPModel R η N x S → IsDisjunctive 16 x

@[blueprint (title := "No positive forcing-error budget plus finite BBP data and prime poles forces disjunctivity")]
theorem not_robustBBPCouplingCriterion (R : ℕ → ℚ) : ¬ RobustBBPCouplingCriterion R := by
  rintro ⟨η, hη, N, h⟩
  obtain ⟨q, S, hq, hModel⟩ := exists_rational_approximateBBPModel R η hη N
  exact hq (h q S hModel)

theorem not_cutoffSix_robustBBPCouplingCriterion :
    ¬ RobustBBPCouplingCriterion (rationalReservoir 6) :=
  not_robustBBPCouplingCriterion _

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
