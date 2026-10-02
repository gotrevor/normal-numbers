/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLog

/-!
# Where the novelty of `zetaY_isNormal` is not: soft diagonalization (believed, 80%)

The prior-art pass (`docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md` §7, novelty 70%) found
that the bare statement "some `ζ_Y` with `Y → ∞` is normal" should already follow from the
constant-`Y` case by a soft diagonalization: raise `Y` only after the previous stage's digit
frequencies have settled to within `1/j`, at an unnamed (fast-decaying) rate.  So the new content
of `zetaY_isNormal` is the **explicit rate** `π(Y n) ≤ (1−ε) log₂ log n` and the uniformity in the
prime set, not unboundedness; `exists_unbounded_zetaY` is a cheap corollary either way.

`exists_unbounded_of_constant` records that belief.  Its hypothesis is the constant-`Y` case only
(every initial-segment prime set `{2, 3, …, p}`), which the explicit theorem already supplies, so
the edge is independent of Vandehey.  English proof: choose stages `M₁ < M₂ < …` with `Y = c_j` on
`[M_j, M_{j+1})`; the tail beyond `n` contributes `O(1/n)`, and the retained-index set up to `M_j`
is finite, so each stage's orbit is an `O(2^{M_j−n})`-perturbation of the stage constant's orbit
plus a rational shift; pick `M_{j+1}` so that the stage-`j` Weyl means are within `1/j` on most of
`[M_j, M_{j+1})`.  80% (the agent's estimate; the rational-shift step is the one to check).
-/

namespace NormalNumbers.GrowingLocalizedLog

open Filter

/-- **Soft diagonalization.**  If every constant-`Y` localized logarithm is normal, some monotone
`Y → ∞` gives a normal `ζ_Y`, with no rate.  Believed, 80%. -/
theorem exists_unbounded_of_constant
    (h : ∀ c : ℕ, 3 ≤ c → IsNormal 2 (zetaY (fun _ => c))) :
    ∃ Y : ℕ → ℕ, Monotone Y ∧ (∀ m, 3 ≤ Y m) ∧ Tendsto Y atTop atTop ∧ IsNormal 2 (zetaY Y) := by
  sorry

end NormalNumbers.GrowingLocalizedLog
