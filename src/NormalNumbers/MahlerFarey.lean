/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerPrimeHalf

/-!
# Farey separation: the shadow of quality `1/(2Q)` is unique 🧮

Infrastructure for the multi-scale attack on the prime-base upper bound
(`DIRECTION.md`'s named next move, and the remaining factor `2` localized in
`PENDING_WORK.md`).

The covering method as used in `MahlerMultiplier.lean` and
`MahlerPrimeHalf.lean` follows ONE rational shadow `ρ` forward under `×g`, and
its whole strength is spent at the single time where the shadow's defect last
sits below `1/Q`.  What it never uses is the times where the shadow has already
LEFT that window: there `x_n` is no longer close to `ρ`, but it is close to some
*other* rational — a Farey neighbour of larger denominator — which carries its
own covering constraint.  Turning "the orbit visits every scale" into a
conjunction of constraints is the attack; this file is its first brick.

* `defect_pair_ge` — for distinct rationals `p/q ≠ p'/q'`,
  `q'·|qx − p| + q·|q'x − p'| ≥ 1`.  (One line, from `|pq' − p'q| ≥ 1`: the
  integer is nonzero, and it telescopes as `q'(p − qx) + q(q'x − p')`.)
* `approx_unique` — hence at most one rational of denominator `≤ Q` has defect
  `< 1/(2Q)` at any given `x`: the "quality `1/(2Q)` shadow" is a *function* of
  `x`, not a choice.
* `orbit_approx_unique` — the same, stated on the orbit, which is where the
  escape argument needs it: the shadow chain of `orbit_escapes` is forced, so a
  constraint derived at one time cannot be dodged by switching shadows.
-/

namespace NormalNumbers.Mahler

open NormalNumbers

/-- **Farey separation, defect form.**  If `p/q` and `p'/q'` are distinct
rationals (`p q' ≠ p' q`) with `q, q' ≥ 1`, then for every real `x`

    `q'·|q x − p| + q·|q' x − p'| ≥ 1`.

Two rationals of denominators `q, q'` are at distance `≥ 1/(q q')`, and a real
cannot be nearer than half of that to both. -/
theorem defect_pair_ge (x : ℝ) (p p' : ℤ) (q q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hne : p * (q' : ℤ) ≠ p' * (q : ℤ)) :
    1 ≤ (q' : ℝ) * |(q : ℝ) * x - p| + (q : ℝ) * |(q' : ℝ) * x - p'| := by
  have hqR : (0 : ℝ) ≤ q := by positivity
  have hq'R : (0 : ℝ) ≤ q' := by positivity
  -- the integer `p q' − p' q` is nonzero, hence of absolute value at least one
  have hZ : (1 : ℤ) ≤ |p * (q' : ℤ) - p' * (q : ℤ)| := by
    rcases lt_trichotomy (p * (q' : ℤ) - p' * (q : ℤ)) 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd (by omega : p * (q' : ℤ) = p' * (q : ℤ)) hne
    · rw [abs_of_pos h]; omega
  have hR : (1 : ℝ) ≤ |(p : ℝ) * q' - p' * q| := by
    have := (Int.cast_le (R := ℝ)).2 hZ
    rwa [Int.cast_abs, Int.cast_one, Int.cast_sub, Int.cast_mul, Int.cast_mul,
      Int.cast_natCast, Int.cast_natCast] at this
  -- and it telescopes
  have htel : (p : ℝ) * q' - p' * q
      = (q' : ℝ) * ((p : ℝ) - q * x) + (q : ℝ) * ((q' : ℝ) * x - p') := by ring
  calc (1 : ℝ) ≤ |(p : ℝ) * q' - p' * q| := hR
    _ = |(q' : ℝ) * ((p : ℝ) - q * x) + (q : ℝ) * ((q' : ℝ) * x - p')| := by rw [htel]
    _ ≤ |(q' : ℝ) * ((p : ℝ) - q * x)| + |(q : ℝ) * ((q' : ℝ) * x - p')| :=
        abs_add_le _ _
    _ = (q' : ℝ) * |(q : ℝ) * x - p| + (q : ℝ) * |(q' : ℝ) * x - p'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hqR, abs_of_nonneg hq'R,
          show ((p : ℝ) - q * x) = -((q : ℝ) * x - p) by ring, abs_neg]

/-- **Uniqueness of the quality-`1/(2Q)` shadow.**  At most one rational with
denominator `≤ Q` approximates `x` with defect below `1/(2Q)`. -/
theorem approx_unique (x : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (p p' : ℤ) (q q' : ℕ)
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (h : |(q : ℝ) * x - p| < 1 / (2 * Q))
    (h' : |(q' : ℝ) * x - p'| < 1 / (2 * Q)) :
    p * (q' : ℤ) = p' * (q : ℤ) := by
  by_contra hne
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hq'R : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq'0 : (0 : ℝ) ≤ q' := by positivity
  have key := defect_pair_ge x p p' q q' hq hq' hne
  have h1 : (q' : ℝ) * |(q : ℝ) * x - p| ≤ (Q : ℝ) * (1 / (2 * Q)) := by
    apply mul_le_mul hq'R h.le (abs_nonneg _) (by linarith)
  have h2 : (q : ℝ) * |(q' : ℝ) * x - p'| ≤ (Q : ℝ) * (1 / (2 * Q)) := by
    apply mul_le_mul hqR h'.le (abs_nonneg _) (by linarith)
  have hhalf : (Q : ℝ) * (1 / (2 * Q)) = 1 / 2 := by field_simp
  rw [hhalf] at h1 h2
  -- strictness: at least one of the two products is strictly below `1/2`
  have hstrict : (q' : ℝ) * |(q : ℝ) * x - p| < 1 / 2 := by
    rcases eq_or_lt_of_le hq'0 with h0 | h0
    · rw [← h0]; simp only [zero_mul]; norm_num
    · calc (q' : ℝ) * |(q : ℝ) * x - p| < (q' : ℝ) * (1 / (2 * Q)) := by
            exact mul_lt_mul_of_pos_left h h0
        _ ≤ (Q : ℝ) * (1 / (2 * Q)) := by
            apply mul_le_mul_of_nonneg_right hq'R (by positivity)
        _ = 1 / 2 := hhalf
  linarith

/-- **The shadow is forced along the orbit.**  Stated where the escape argument
uses it: at each time `n` there is at most one rational of denominator `≤ Q`
whose defect at `orbit g α n` is below `1/(2Q)`.  So the covering constraints
collected at different times all refer to a canonical shadow — they cannot be
dodged by choosing a different approximation at each scale. -/
theorem orbit_approx_unique (g : ℕ) (α : ℝ) (n Q : ℕ) (hQ : 1 ≤ Q) (ρ σ : ℚ)
    (hρ : ρ.den ≤ Q) (hσ : σ.den ≤ Q)
    (hρd : |(ρ.den : ℝ) * orbit g α n - ρ.num| < 1 / (2 * Q))
    (hσd : |(σ.den : ℝ) * orbit g α n - σ.num| < 1 / (2 * Q)) :
    ρ = σ := by
  have h := approx_unique (orbit g α n) Q hQ ρ.num σ.num ρ.den σ.den ρ.pos σ.pos
    hρ hσ hρd hσd
  exact Rat.eq_iff_mul_eq_mul.2 (by exact_mod_cast h)

end NormalNumbers.Mahler
