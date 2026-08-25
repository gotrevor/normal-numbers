/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# Disjunctivity: the topological twin of Wall's theorem (Track D, brick D0)

Companion to `docs/conditional-disjunctivity.md` §0 ("the orbit dictionary").
Where `IsNormal b x` asks for the multiply-by-`b` orbit `n ↦ bⁿ·x mod 1` to be
*equidistributed* mod 1 (Wall's theorem), **disjunctivity** asks only for the
orbit to be *dense* in `[0,1)`.  Equivalently, every finite base-`b` block occurs
somewhere in the expansion of `x` (density ⟺ every cylinder is visited).

This module is deliberately elementary and self-contained: it introduces
`IsDisjunctive` in the interval-visit form directly analogous to `Equidistributed`,
records that the orbit lives in `[0,1)`, and proves the equivalence with the
topological "dense orbit" statement (`isDisjunctive_iff_denseOrbit`).  Nothing
here depends on the CF or Khinchin machinery; it sits beside `Wall.lean`.
-/

namespace NormalNumbers

open Filter Set

/-- The multiply-by-`b` orbit only sees the fractional part of `x` (local copy of
`Wall.orbit_fract`, kept here to avoid importing the full Wall stack). -/
theorem orbit_fract (b : ℕ) (x : ℝ) (n : ℕ) :
    orbit b (Int.fract x) n = orbit b x n := by
  unfold orbit
  have h : Int.fract x * (b : ℝ) ^ n
      = x * (b : ℝ) ^ n - ((⌊x⌋ * (b ^ n : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- The multiply-by-`b` orbit always lands in `[0,1)` — it is a fractional part. -/
theorem orbit_mem_Ico (b : ℕ) (x : ℝ) (n : ℕ) : orbit b x n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **Disjunctive in base `b`** (interval-visit form).  Every subinterval
`[a, c) ⊆ [0, 1)` is visited by the multiply-by-`b` orbit `n ↦ bⁿ·x mod 1`.
This is the topological weakening of `Equidistributed (orbit b x)`: the latter
pins the *frequency* of every subinterval, the former only its non-emptiness of
visits.  As with `IsNormal`, the property only sees `Int.fract x`
(`isDisjunctive_fract`). -/
def IsDisjunctive (b : ℕ) (x : ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → ∃ n, orbit b x n ∈ Set.Ico a c

/-- The orbit only sees the fractional part, so disjunctivity is a property of
`Int.fract x`. -/
theorem isDisjunctive_fract (b : ℕ) (x : ℝ) :
    IsDisjunctive b (Int.fract x) ↔ IsDisjunctive b x := by
  simp only [IsDisjunctive]
  have key : ∀ n, orbit b (Int.fract x) n = orbit b x n := orbit_fract b x
  constructor
  · intro h a c ha hac hc
    obtain ⟨n, hn⟩ := h a c ha hac hc
    rw [key] at hn; exact ⟨n, hn⟩
  · intro h a c ha hac hc
    obtain ⟨n, hn⟩ := h a c ha hac hc
    rw [← key] at hn; exact ⟨n, hn⟩

/-- **Disjunctivity is the dense-orbit condition** (the topological twin of
Wall's theorem).  `x` is disjunctive in base `b` iff every point of `[0,1)` is a
limit of orbit points, i.e. `[0,1) ⊆ closure {bⁿ·x mod 1 : n}`.

Since the orbit is contained in `[0,1)` (`orbit_mem_Ico`), this says exactly that
the orbit is dense in the unit interval — the ω-limit set of the orbit is all of
`[0,1)`. -/
theorem isDisjunctive_iff_denseOrbit (b : ℕ) (x : ℝ) :
    IsDisjunctive b x ↔ Set.Ico (0 : ℝ) 1 ⊆ closure (Set.range (orbit b x)) := by
  constructor
  · -- disjunctive ⟹ dense: shrink to a half-open interval `[y, min 1 (y+ε))`.
    intro hdisj y hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := hdisj y (min 1 (y + ε)) hy.1
      (lt_min hy.2 (by linarith)) (min_le_left _ _)
    refine ⟨orbit b x n, ⟨n, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hlo : y ≤ orbit b x n := hn.1
    have hhi : orbit b x n < y + ε := lt_of_lt_of_le hn.2 (min_le_right _ _)
    exact ⟨by linarith, by linarith⟩
  · -- dense ⟹ disjunctive: aim at the midpoint of `[a, c)` with radius `(c-a)/2`.
    intro hdense a c ha hac hc
    set y : ℝ := (a + c) / 2 with hy
    have hya : a < y := by rw [hy]; linarith
    have hyc : y < c := by rw [hy]; linarith
    have hymem : y ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt (lt_of_le_of_lt ha hya),
      lt_of_lt_of_le hyc hc⟩
    have := hdense hymem
    rw [Metric.mem_closure_iff] at this
    obtain ⟨z, hzrange, hz⟩ := this ((c - a) / 2) (by linarith)
    obtain ⟨n, rfl⟩ := hzrange
    rw [Real.dist_eq, abs_lt] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [hy] at hz1 hz2
    have hlow : a < orbit b x n := by linarith [hz2]
    have hhigh : orbit b x n < c := by linarith [hz1]
    exact ⟨n, le_of_lt hlow, hhigh⟩

end NormalNumbers
