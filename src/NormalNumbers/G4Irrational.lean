/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBAssembly
import NormalNumbers.DisjunctiveCorollaries

/-!
# Irrationality and arbitrarily-late occurrence for the G4 constants

The general facts are in `DisjunctiveCorollaries.lean` (`IsDisjunctive.irrational`,
`IsDisjunctive.exists_ge`, `IsDisjunctive.exists_occursAt_ge`); here they are applied to
`G4.isDisjunctive_base`, giving unconditionally and axiom-clean, for every `b ≥ 3`:

* `G4.irrational_primeLambertAtBase` — `∑_n ω(n)/bⁿ` is irrational;
* `G4.irrational_primeSum` — **`∑_{p prime} 1/(bᵖ − 1)` is irrational**;
* `G4.irrational_primeLambertFour` — the campaign's own constant `G₄ = ∑_p 1/(4ᵖ−1)`;
* `G4.every_word_occurs_base_late` — every finite base-`b` word occurs **arbitrarily late**
  in the expansion, hence infinitely often; and the base-two form
  `G4.every_binary_word_occurs_late` for `G₄`.

The base-two member of the *family* (`∑_p 1/(2ᵖ−1)`) is out of reach here: the base-two route
is refuted (`rowL1 2 K = 1`, `DIRECTION.md`).  Its irrationality is Tao–Teräväinen,
arXiv 2512.01739 Thm 1.3; what is proved here is the `b ≥ 3` half of that family, by a
different (digit-structure) route, and strictly stronger for those bases — `isDisjunctive_base`
gives every finite word, at arbitrarily late positions.
-/

open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-! ### Irrationality -/

/-- **`∑_n ω(n)/bⁿ` is irrational for every `b ≥ 3`.** -/
theorem irrational_primeLambertAtBase {b : ℕ} (hb : 3 ≤ b) :
    Irrational (primeLambertAtBase b) :=
  (isDisjunctive_base hb).irrational

/-- **`∑_{p prime} 1/(bᵖ − 1)` is irrational for every `b ≥ 3`.** -/
theorem irrational_primeSum {b : ℕ} (hb : 3 ≤ b) : Irrational (primeSumAtBase b) :=
  (isDisjunctive_primeSum hb).irrational

/-- The campaign's constant `G₄ = ∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ` is irrational. -/
theorem irrational_primeLambertFour : Irrational primeLambertFour :=
  isDisjunctive_four.irrational

/-! ### Arbitrarily late occurrences -/

/-- **Every finite base-`b` word occurs arbitrarily late** in `∑_n ω(n)/bⁿ`, `b ≥ 3` — hence
infinitely often. -/
theorem every_word_occurs_base_late {b : ℕ} (hb : 3 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b)
    (N : ℕ) : ∃ n, N ≤ n ∧ OccursAt b (primeLambertAtBase b) w n :=
  (isDisjunctive_base hb).exists_occursAt_ge (by omega) w hw N

/-- **Every finite binary word occurs arbitrarily late** in `G₄ = ∑_p 1/(4ᵖ−1)`. -/
theorem every_binary_word_occurs_late (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (N : ℕ) :
    ∃ n, N ≤ n ∧ OccursAt 2 primeLambertFour w n :=
  isDisjunctive_two.exists_occursAt_ge le_rfl w hw N

end NormalNumbers.G4
