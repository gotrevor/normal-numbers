/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirDenominator
import NormalNumbers.PiDisjunctiveRoutes.BBPBackward

/-!
# Real approximation on a prescribed numerator congruence class

A fixed denominator D and a numerator class modulo M leave real grid spacing
M/D.  For M=2^K and odd D, this retains K digits of 2-adic agreement.
This tests what the backward BBP cancellation can buy without exact forcing.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.BBPAdelicGrid

open CutoffSix

@[blueprint (title := "A fixed denominator and numerator congruence allow approximation at spacing M over D")]
theorem exists_congruence_grid_close (a : ℤ) (D M : ℕ)
    (hD : 0 < D) (hM : 0 < M) (y : ℝ) :
    ∃ m : ℤ,
      (((a + (M : ℤ)*m : ℤ) : ℚ) / D).den ∣ D ∧
      |((((a + (M : ℤ)*m : ℤ) : ℚ) / D : ℚ) : ℝ) - y| < (M : ℝ)/D := by
  let m : ℤ := ⌊(y*D-a)/M⌋
  refine ⟨m, fraction_den_dvd _ _, ?_⟩
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hlo : (m : ℝ)*M ≤ y*D-a :=
    (le_div_iff₀ hm).mp (Int.floor_le _)
  have hhi : y*D-a < ((m : ℝ)+1)*M :=
    (div_lt_iff₀ hm).mp (Int.lt_floor_add_one _)
  push_cast
  rw [abs_sub_lt_iff]
  constructor
  · have hq : ((a : ℝ)+M*m)/D ≤ y := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    have : (0 : ℝ) < (M : ℝ)/D := div_pos hm hd
    linarith
  · have hq : y-(M : ℝ)/D < ((a : ℝ)+M*m)/D := by
      apply (lt_div_iff₀ hd).mpr
      have hc : ((M : ℝ)/D)*D = M := div_mul_cancel₀ _ hd.ne'
      nlinarith
    linarith

@[blueprint (title := "Numerator congruence preserves p-adic precision when p misses the denominator")]
theorem congruence_grid_padic (a m : ℤ) (D M p : ℕ) [Fact p.Prime]
    (hD : ¬ p ∣ D) :
    padicNorm p ((((a + (M : ℤ)*m : ℤ) : ℚ) / D) - (a : ℚ)/D) ≤
      padicNorm p (M : ℚ) := by
  have he : (((a + (M : ℤ)*m : ℤ) : ℚ) / D) - (a : ℚ)/D =
      (M : ℚ) * ((m : ℚ)/D) := by push_cast; ring
  rw [he, padicNorm.mul, padicNorm.div, (padicNorm.nat_eq_one_iff D).mpr hD,
    div_one]
  exact mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_int m)

/-- The center is any exact rational r, including a genuine BBP head.
This keeps its actual reduced denominator budget and numerator class.
It does not assert that the rounded numerator is coprime to that denominator. -/
@[blueprint (title := "Genuine rational denominator budgets and finite 2-adic precision still admit any real target at grid scale")]
theorem rational_center_grid (r : ℚ) (K : ℕ) (y : ℝ) (hr : ¬ 2 ∣ r.den) :
    ∃ q : ℚ, q.den ∣ r.den ∧
      |(q : ℝ)-y| < (2 : ℝ)^K/r.den ∧
      padicNorm 2 (q-r) ≤ padicNorm 2 ((2 : ℚ)^K) := by
  obtain ⟨m, hden, hclose⟩ := exists_congruence_grid_close r.num r.den (2^K)
    r.pos (by positivity) y
  refine ⟨((r.num+(2^K : ℕ)*m : ℤ) : ℚ)/r.den, hden, ?_, ?_⟩
  · simpa using hclose
  · have h := congruence_grid_padic r.num m r.den (2^K) 2 hr
    simpa only [Rat.num_div_den, Nat.cast_pow, Nat.cast_ofNat] using h

private theorem odd_den_add (q r : ℚ) (hq : ¬ 2 ∣ q.den) (hr : ¬ 2 ∣ r.den) :
    ¬ 2 ∣ (q+r).den := by
  intro h
  exact ((Nat.prime_two.dvd_mul).mp (dvd_trans h (Rat.add_den_dvd q r))).elim hq hr

private theorem odd_den_mul (q r : ℚ) (hq : ¬ 2 ∣ q.den) (hr : ¬ 2 ∣ r.den) :
    ¬ 2 ∣ (q*r).den := by
  intro h
  exact ((Nat.prime_two.dvd_mul).mp (dvd_trans h (Rat.mul_den_dvd q r))).elim hq hr

private theorem odd_den_sum {α : Type*} (s : Finset α) (f : α → ℚ)
    (hf : ∀ j ∈ s, ¬ 2 ∣ (f j).den) : ¬ 2 ∣ (∑ j ∈ s, f j).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact odd_den_add _ _ (hf a (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem kick_den_odd (j : ℕ) : ¬ 2 ∣ (BBPBackward.kick j).den := by
  have he : BBPBackward.kick j =
      ((120*j^2+151*j+47 : ℕ) : ℚ) /
        (((8*j+1)*(2*j+1)*(8*j+5)*(4*j+3) : ℕ) : ℚ) := by
    rw [BBPBackward.kick_factored _ (by positivity) (by positivity)
      (by positivity) (by positivity)]
    push_cast
    rfl
  rw [he]
  have hd := fraction_den_dvd ((120*j^2+151*j+47 : ℕ) : ℤ)
    ((8*j+1)*(2*j+1)*(8*j+5)*(4*j+3))
  push_cast at hd
  intro h
  push_cast at h
  have hmul := dvd_trans h hd
  simp only [Nat.prime_two.dvd_mul] at hmul
  omega

theorem bbp_head_den_odd (n : ℕ) : ¬ 2 ∣ (bbpRationalHead n).den := by
  unfold bbpRationalHead
  apply odd_den_sum
  intro j _
  apply odd_den_mul
  · have he : (16 : ℚ)^(n-j) = ((16^(n-j) : ℕ) : ℚ) := by simp
    rw [he]
    simp
  · exact kick_den_odd j

@[blueprint (title := "BBP head denominators and 2-adic prefixes permit arbitrary real targets at their grid scale")]
theorem bbp_head_grid (n K : ℕ) (y : ℝ) :
    ∃ q : ℚ, q.den ∣ (bbpRationalHead n).den ∧
      |(q : ℝ)-y| < (2 : ℝ)^K/(bbpRationalHead n).den ∧
      padicNorm 2 (q-bbpRationalHead n) ≤ padicNorm 2 ((2 : ℚ)^K) :=
  rational_center_grid _ K y (bbp_head_den_odd n)

noncomputable def gridError (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  2^(K n)/(bbpRationalHead n).den

theorem gridError_pos (K : ℕ → ℕ) (n : ℕ) : 0 < gridError K n := by
  unfold gridError
  positivity

/-- Any finite genuine prefix, actual denominator budgets, arbitrarily
prescribed finite 2-adic precisions, and approximate BBP forcing still admit
a rational target, at the explicit M/D approximation scale.
No decay of that scale is claimed for an arbitrary precision schedule K.
No equality of reduced denominators or exact infinite forcing is claimed. -/
@[blueprint (title := "Finite 2-adic BBP precision and actual denominators admit rational targets at the grid scale")]
theorem rational_grid_comparison (K : ℕ → ℕ) (N : ℕ) :
    ∃ x : ℚ, ∃ Q : ℕ → ℚ,
      (¬ IsDisjunctive 16 (x : ℝ)) ∧
      (∀ n ≤ N, Q n = bbpRationalHead n) ∧
      (∀ n, (Q n).den ∣ (bbpRationalHead n).den) ∧
      (∀ n, padicNorm 2 (Q n-bbpRationalHead n) ≤ padicNorm 2 ((2 : ℚ)^(K n))) ∧
      (∀ n, |(Q n : ℝ)-comparisonHead x n| < gridError K n) ∧
      (∀ n, |(Q (n+1) : ℝ)-16*(Q n : ℝ)-16*bbpKick n| <
        gridError K (n+1)+16*gridError K n) := by
  classical
  obtain ⟨x, hx⟩ := exists_rational_target_for_prefix (gridError K) (gridError_pos K) N
  have hg := fun n => bbp_head_grid n (K n) (comparisonHead x n)
  choose A hden hclose hpadic using hg
  let Q : ℕ → ℚ := fun n => if n ≤ N then bbpRationalHead n else A n
  have hpref : ∀ n ≤ N, Q n = bbpRationalHead n := by
    intro n hn
    simp [Q, hn]
  have hshadow : ∀ n, |(Q n : ℝ)-comparisonHead x n| < gridError K n := by
    intro n
    by_cases hn : n ≤ N
    · simpa [Q, hn] using hx n hn
    · simpa [Q, hn, gridError] using hclose n
  refine ⟨x, Q, ?_, hpref, ?_, ?_, hshadow, ?_⟩
  · intro h
    exact h.irrational ⟨x, rfl⟩
  · intro n
    by_cases hn : n ≤ N
    · simp [Q, hn]
    · simpa [Q, hn] using hden n
  · intro n
    by_cases hn : n ≤ N
    · rw [hpref n hn, sub_self, padicNorm.zero]
      exact padicNorm.nonneg _
    · simpa [Q, hn] using hpadic n
  · intro n
    have h := forcing_defect_bound (fun n => (Q n : ℝ)) (comparisonHead x)
      (gridError K) hshadow n
    simpa only [comparisonHead_succ] using h

end NormalNumbers.PiDisjunctiveRoutes.BBPAdelicGrid
