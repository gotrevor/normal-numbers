/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SchmidtGames
import Mathlib.Computability.Partrec

/-!
# Stretch: a computable point of `U ∩ BAD` in the middle-third Cantor set

Kept apart from `SchmidtGames.lean`: a stretch conjecture, not a frozen headline.

**Context.**  Temur, *Simultaneously small continued fraction entropy and base `b` entropy*,
arXiv:2609.16362 (14 Sep 2026), answering Bugeaud 2012 Problem 10.53, constructs a COMPUTABLE
irrational `ξ` with `‖bᵏξ‖ > δ_b := 154^{−2^b}` for every `b ≥ 2`, `k ≥ 0`, a doubly
exponential bound.  `UniformBad.bugeaud_10_36` gives `b^{−24}`, a polynomial bound, with no
computability claim.

**Conjecture.**  Some computable `e : ℕ → Bool` gives a point `Σ 2·e(n)·3^{−(n+1)}` of the
middle-third Cantor set lying in `U ∩ Bad`: polynomial `b^{−C}` for every base, badly
approximable, Cantor, and computable at once.

**Mechanism.**  Play the BFS potential game with a computable Bob: Bob descends through triadic
Cantor intervals and picks a child whose potential (Alice's deletions from `potentialWinning_E`
and BFS Lemma 3.10, weighted as in BFS §5) stays below threshold.  The potentials are infinite
sums over bases, computable to any precision from explicit tails `Σ_{b > B} b^{−C/2}`.  So Bob
compares rational over-approximations with a margin; the averaging step in BFS Theorem 5.5
leaves room for that margin.  Known-false sibling it must fail on: the same descent with
target "normal in base 2" (`not_potentialWinning_isNormal`).

Confidence: true 75%; Lean 25% (several laps, after headline 1).
-/

namespace NormalNumbers.SchmidtGames

/-- The point of the middle-third Cantor set with ternary digits `2·e(n)`. -/
noncomputable def cantorPoint (e : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, (if e n then (2 : ℝ) else 0) / 3 ^ (n + 1)

/-- **Stretch conjecture.**  A computable point of `U ∩ Bad` in the middle-third Cantor set. -/
theorem exists_computable_cantorPoint_mem_U_inter_Bad :
    ∃ e : ℕ → Bool, Computable e ∧ cantorPoint e ∈ U ∩ Bad := by
  sorry

end NormalNumbers.SchmidtGames
