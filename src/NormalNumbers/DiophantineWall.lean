/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# The Diophantine wall interface (Track D, the wall)

Companion to `docs/diophantine-wall.md`.  `LnTwoRuns.lean` states its two
frozen tiers through `lnTwoNorm`, which is defined via the orbit.  This
file proves the **interface edge**: `lnTwoNorm n` is exactly the distance
of `2ⁿ·ln 2` to the nearest integer, so `LnTwoDyadicSep f N₀` is
equivalent to the pure number-theoretic statement

> `∀ n ≥ N₀, ∀ p : ℤ,  f n ≤ |ln 2 · 2ⁿ − p|`

with no orbit, digit, or dynamics language.  Any Diophantine construction
(shifted-Legendre, Rhin kernels, a cited measure) can discharge the tiers
through this door with zero repo context — and the collatz-moonshot repo's
`sep_two_three` knocks at the same wall in the polynomial-coefficient
regime (see the wall doc for the regime map).
-/

namespace NormalNumbers

open Filter Set

/-- The doubling orbit of `ln 2`, unwrapped: `orbit 2 (ln 2) n` is the
fractional part of `ln 2 · 2ⁿ`. -/
theorem orbit_log_two_eq_fract (n : ℕ) :
    orbit 2 (Real.log 2) n = Int.fract (Real.log 2 * 2 ^ n) := by
  unfold orbit
  norm_num

/-- `lnTwoNorm` bounds the distance to EVERY integer:
`‖2ⁿ·ln 2‖ ≤ |ln 2 · 2ⁿ − p|` for all `p`. -/
theorem lnTwoNorm_le_abs_int (n : ℕ) (p : ℤ) :
    lnTwoNorm n ≤ |Real.log 2 * 2 ^ n - p| := by
  set y : ℝ := Real.log 2 * 2 ^ n with hy
  have horb : orbit 2 (Real.log 2) n = Int.fract y := orbit_log_two_eq_fract n
  have hfr : Int.fract y = y - ⌊y⌋ := rfl
  rcases le_or_gt p ⌊y⌋ with hp | hp
  · have hpy : (p : ℝ) ≤ y := le_trans (by exact_mod_cast hp) (Int.floor_le y)
    have h1 : Int.fract y ≤ y - p := by
      rw [hfr]
      have : (p : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hp
      linarith
    calc lnTwoNorm n ≤ orbit 2 (Real.log 2) n := min_le_left _ _
      _ = Int.fract y := horb
      _ ≤ y - p := h1
      _ ≤ |y - p| := le_abs_self _
  · have hp1 : (⌊y⌋ : ℝ) + 1 ≤ p := by exact_mod_cast hp
    have hylt : y < p := lt_of_lt_of_le (Int.lt_floor_add_one y) hp1
    have h1 : 1 - Int.fract y ≤ p - y := by
      rw [hfr]
      linarith
    calc lnTwoNorm n ≤ 1 - orbit 2 (Real.log 2) n := min_le_right _ _
      _ = 1 - Int.fract y := by rw [horb]
      _ ≤ p - y := h1
      _ ≤ |y - p| := by rw [abs_sub_comm]; exact le_abs_self _

/-- `lnTwoNorm` is ATTAINED at an integer: some `p` realizes
`‖2ⁿ·ln 2‖ = |ln 2 · 2ⁿ − p|`. -/
theorem exists_int_abs_eq_lnTwoNorm (n : ℕ) :
    ∃ p : ℤ, |Real.log 2 * 2 ^ n - p| = lnTwoNorm n := by
  set y : ℝ := Real.log 2 * 2 ^ n with hy
  have horb : orbit 2 (Real.log 2) n = Int.fract y := orbit_log_two_eq_fract n
  have hf0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hf1 : Int.fract y < 1 := Int.fract_lt_one y
  have hfr : Int.fract y = y - ⌊y⌋ := rfl
  rcases le_total (Int.fract y) (1 - Int.fract y) with hc | hc
  · refine ⟨⌊y⌋, ?_⟩
    rw [show y - (⌊y⌋ : ℝ) = Int.fract y from by rw [hfr],
      abs_of_nonneg hf0]
    unfold lnTwoNorm
    rw [horb, min_eq_left hc]
  · refine ⟨⌊y⌋ + 1, ?_⟩
    have : y - ((⌊y⌋ + 1 : ℤ) : ℝ) = Int.fract y - 1 := by
      push_cast
      rw [hfr]
      ring
    rw [this, abs_of_nonpos (by linarith), neg_sub]
    unfold lnTwoNorm
    rw [horb, min_eq_right hc]

/-- **The wall interface**: the dyadic separation hypothesis in pure
number-theoretic form.  `LnTwoDyadicSep f N₀` holds iff every integer is
`f n`-far from `ln 2 · 2ⁿ` for `n ≥ N₀` — the statement a Diophantine
construction proves, with no orbit or digit language. -/
theorem lnTwoDyadicSep_iff_int (f : ℕ → ℝ) (N₀ : ℕ) :
    LnTwoDyadicSep f N₀ ↔
      ∀ n, N₀ ≤ n → ∀ p : ℤ, f n ≤ |Real.log 2 * 2 ^ n - p| := by
  constructor
  · intro hsep n hn p
    exact (hsep n hn).trans (lnTwoNorm_le_abs_int n p)
  · intro hint n hn
    obtain ⟨p, hp⟩ := exists_int_abs_eq_lnTwoNorm n
    rw [← hp]
    exact hint n hn p

end NormalNumbers
