/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DeterministicBD

/-!
# Galois conjugates share their digit complexity

Trevor, 2026-10-05: *"some arbitrary set of numbers - picked in some clever way - that have some
interesting property in this realm"*, with `π + e`, `π e` as the model ("one of them is
transcendental") and `^` as a transformation to try.

The mechanism: the deterministic (zero-entropy) numbers form a group under `+` (B-D Cor. 4.11(2),
`DetSub`) containing `ℚ`.  So any finite set whose sum is rational cannot have exactly one
non-deterministic member.  The real conjugates of an algebraic integer are such a set, and so are
their `n`-th powers for every `n` (the power sums are integers, Newton's identities).  That is where
`^` enters: it is not finite-state on digits (Manai: a deterministic `X` with `X²` normal), but on a
Galois orbit the power sums pin the powers to a rational hyperplane, which is finite-state.

* `isDeterministic_of_sum_rat`: `x + y + z ∈ ℚ`, `y, z` deterministic ⟹ `x` deterministic.
* `not_exactly_one_nondet`: the three-term set has zero or at least two non-deterministic members.
* `isDeterministic_iff_of_add_rat`: the two-term case, conjugate twins (`φ` and `-1/φ`, `√2` and
  `-√2`): one is deterministic iff the other is.

Reading for a totally real cubic integer with conjugates `α₁, α₂, α₃` (e.g. the roots of
`X³ - 3X + 1`): for every `n`, `{α₁ⁿ, α₂ⁿ, α₃ⁿ}` has zero or at least two members of positive
entropy.  Each member's status is open individually.  Novelty: an immediate corollary of `DetSub`;
possibly literature-adjacent, not swept.
-/

namespace NormalNumbers.Deterministic

open Literature.BergelsonDownarowicz

/-- A three-term rational sum with two deterministic terms has a deterministic third term. -/
theorem isDeterministic_of_sum_rat {b : ℕ} (hb : 2 ≤ b) (hsub : DetSub b) {x y z : ℝ} (q : ℚ)
    (hsum : x + y + z = q) (hy : IsDeterministic b y) (hz : IsDeterministic b z) :
    IsDeterministic b x := by
  have h1 := hsub _ _ (isDeterministic_ratCast b hb q) hy
  have h2 := hsub _ _ h1 hz
  have hx : x = (q : ℝ) - y - z := by linarith
  rwa [hx]

/-- **No lone complex conjugate.**  If `x + y + z` is rational, then it is impossible that
exactly one of `x, y, z` is non-deterministic. -/
theorem not_exactly_one_nondet {b : ℕ} (hb : 2 ≤ b) (hsub : DetSub b) {x y z : ℝ} (q : ℚ)
    (hsum : x + y + z = q) :
    ¬ (¬ IsDeterministic b x ∧ IsDeterministic b y ∧ IsDeterministic b z) := by
  rintro ⟨hx, hy, hz⟩
  exact hx (isDeterministic_of_sum_rat hb hsub q hsum hy hz)

/-- **Conjugate twins.**  If `x + y` is rational, `x` is deterministic iff `y` is. -/
theorem isDeterministic_iff_of_add_rat {b : ℕ} (hb : 2 ≤ b) (hsub : DetSub b) {x y : ℝ} (q : ℚ)
    (hsum : x + y = q) : IsDeterministic b x ↔ IsDeterministic b y := by
  constructor
  · intro hx
    have := hsub _ _ (isDeterministic_ratCast b hb q) hx
    rwa [show (q : ℝ) - x = y by linarith] at this
  · intro hy
    have := hsub _ _ (isDeterministic_ratCast b hb q) hy
    rwa [show (q : ℝ) - y = x by linarith] at this

end NormalNumbers.Deterministic
