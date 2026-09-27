/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature

/-!
# Vandehey 2017, Theorem 1.1: non-trivial matrix actions preserve CF-normality

Discharges the cited `Literature.vandehey_matrix_action` (side quest, 2026-09-27).

⚠️ **Known gap in the published proof.**  Vandehey's Lemma 3.3 (3.2 in arXiv v1) is the
Pyatetskii-Shapiro hot-spot criterion, proved as "a simple consequence of
[Moshchevitin–Shkredov 2003, Theorem 1]".  Airey–Mance (arXiv:1912.10265) show that
theorem is FALSE on non-compact spaces, and the CF space is non-compact.  The repair:
add a tightness hypothesis (Airey–Mance Theorem A/B) and prove that the empirical
measures of a CF-normal point are tight (digit-`≤ K` cylinder frequencies converge to
Gauss measure, and `γ(a₁ > K) = O(1/K)`).  Full write-up:
`papers/vandehey-2017-open-problem-attack-map.md` §6.1; paper notes:
`papers/vandehey-2017-matrix-actions-cf-normality.md`.

Available machinery: `Literature.philipp_psi_mixing_holds` (ψ-mixing, `CFPsiPin.lean`),
Rényi-type bounds, the CF cylinder / digit-law stack, `HotSpot.lean` (base-`b` only).
-/

namespace NormalNumbers.Literature

open NormalNumbers

/-- **Vandehey 2017, Theorem 1.1**: integer Möbius maps with nonzero determinant
preserve CF-normality. -/
theorem vandehey_matrix_action_holds : vandehey_matrix_action := by
  sorry

end NormalNumbers.Literature
