/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterKicked
import Architect

/-!
# Rational spans of BBP-type series

The polynomial-ratio kick class used by Bailey--Crandall is closed under rational linear
combinations.  This is the kernel witness behind the Maze verdict that a factor-map entropy
argument for a pair of BBP constants does not escape the single-constant Hypothesis A wall.
Source and research context: `docs/joint-bc-orbits-2026-10-16.md`, R1.
-/

namespace NormalNumbers.MasterConjectures

open Polynomial

/-- A kick sequence represented by a quotient of integer polynomials at every positive index. -/
def PolynomialRatioKick (r : ℕ → ℝ) : Prop :=
  ∃ p q : ℤ[X],
    (∀ n : ℕ, 1 ≤ n → q.eval (n : ℤ) ≠ 0) ∧
    ∀ n : ℕ, 1 ≤ n →
      ((p.eval (n : ℤ) : ℤ) : ℝ) / ((q.eval (n : ℤ) : ℤ) : ℝ) = r n

/-- Polynomial-ratio kicks are closed under addition by taking a common denominator. -/
theorem polynomialRatioKick_add {r s : ℕ → ℝ}
    (hr : PolynomialRatioKick r) (hs : PolynomialRatioKick s) :
    PolynomialRatioKick (fun n => r n + s n) := by
  obtain ⟨p₁, q₁, hq₁, hr⟩ := hr
  obtain ⟨p₂, q₂, hq₂, hs⟩ := hs
  refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, ?_, ?_⟩
  · intro n hn
    simp only [eval_mul]
    exact mul_ne_zero (hq₁ n hn) (hq₂ n hn)
  · intro n hn
    simp only [eval_add, eval_mul, Int.cast_add, Int.cast_mul]
    rw [← hr n hn, ← hs n hn]
    have h1 : ((q₁.eval (n : ℤ) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq₁ n hn
    have h2 : ((q₂.eval (n : ℤ) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq₂ n hn
    field_simp

/-- Polynomial-ratio kicks are closed under rational scaling after clearing its denominator. -/
theorem polynomialRatioKick_rat_mul (a : ℚ) {r : ℕ → ℝ}
    (hr : PolynomialRatioKick r) :
    PolynomialRatioKick (fun n => (a : ℝ) * r n) := by
  obtain ⟨p, q, hq, hr⟩ := hr
  refine ⟨C a.num * p, C (a.den : ℤ) * q, ?_, ?_⟩
  · intro n hn
    simp only [eval_mul, eval_C]
    exact mul_ne_zero (by exact_mod_cast a.den_nz) (hq n hn)
  · intro n hn
    simp only [eval_mul, eval_C, Int.cast_mul]
    have hqR : ((q.eval (n : ℤ) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq n hn
    have hdenR : ((a.den : ℤ) : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
    have ha : (((a.num : ℤ) : ℝ) / ((a.den : ℕ) : ℝ)) = (a : ℝ) := by
      exact_mod_cast a.num_div_den
    calc
      ((a.num : ℤ) : ℝ) * ((p.eval (n : ℤ) : ℤ) : ℝ) /
          (((a.den : ℤ) : ℝ) * ((q.eval (n : ℤ) : ℤ) : ℝ)) =
          (((a.num : ℤ) : ℝ) / ((a.den : ℕ) : ℝ)) *
            (((p.eval (n : ℤ) : ℤ) : ℝ) / ((q.eval (n : ℤ) : ℤ) : ℝ)) := by
              push_cast
              field_simp
      _ = (a : ℝ) * r n := by rw [ha, hr n hn]

/-- Every rational linear combination of two polynomial-ratio kicks has the same form. -/
theorem polynomialRatioKick_rat_linear (a c : ℚ) {r s : ℕ → ℝ}
    (hr : PolynomialRatioKick r) (hs : PolynomialRatioKick s) :
    PolynomialRatioKick (fun n => (a : ℝ) * r n + (c : ℝ) * s n) :=
  polynomialRatioKick_add (polynomialRatioKick_rat_mul a hr)
    (polynomialRatioKick_rat_mul c hs)

/-- A base-`b` BBP-type series with an integer-polynomial ratio kick. -/
def IsBBPTypeSeries (b : ℕ) (x : ℝ) : Prop :=
  ∃ r : ℕ → ℝ, PolynomialRatioKick r ∧
    HasSum (fun n : ℕ => r (n + 1) / (b : ℝ) ^ (n + 1)) x

/-- Reopen condition for the BBP factor-map entropy route: a normal BBP-type seed. -/
def NormalBBPSeed : Prop :=
  ∃ b : ℕ, ∃ x : ℝ, 2 ≤ b ∧ IsBBPTypeSeries b x ∧ IsNormal b x

/-- BBP-type series are closed under arbitrary rational linear combinations. -/
@[blueprint (title := "Rational spans of BBP-type series stay BBP-type")]
theorem isBBPTypeSeries_rat_linear (b : ℕ) (a c : ℚ) {x y : ℝ}
    (hx : IsBBPTypeSeries b x) (hy : IsBBPTypeSeries b y) :
    IsBBPTypeSeries b ((a : ℝ) * x + (c : ℝ) * y) := by
  obtain ⟨r, hr, hsumr⟩ := hx
  obtain ⟨s, hs, hsums⟩ := hy
  refine ⟨fun n => (a : ℝ) * r n + (c : ℝ) * s n,
    polynomialRatioKick_rat_linear a c hr hs, ?_⟩
  simpa only [mul_div, ← add_div] using
    (hsumr.mul_left (a : ℝ)).add (hsums.mul_left (c : ℝ))

/-- The nonzero-coefficient form used by the R1 factor-map entropy route. -/
theorem isBBPTypeSeries_nonzero_rat_linear (b : ℕ) (a c : ℚ) {x y : ℝ}
    (_hac : a ≠ 0 ∨ c ≠ 0) (hx : IsBBPTypeSeries b x) (hy : IsBBPTypeSeries b y) :
    IsBBPTypeSeries b ((a : ℝ) * x + (c : ℝ) * y) :=
  isBBPTypeSeries_rat_linear b a c hx hy

end NormalNumbers.MasterConjectures
