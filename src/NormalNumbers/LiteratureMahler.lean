/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.MahlerMultiplier
import NormalNumbers.MahlerMultiplierStrict

/-!
# Ledger edges from Mahler's multiplier theorem 📚→✅

`MahlerMultiplier.lean` proves `mahler_multiplier`: some `m ≤ g^(k+1)`
has the block `w` (of length `k`) occurring i.o. in `m·α`.  This file wires
that theorem into the literature ledger:

* `mahler_theoremM_holds` — **Mahler 1973, Theorem M** (`m ≤ g^(2k+1)`) is
  independently verified for all `g ≥ 2` and all nonempty blocks, since
  `g^(k+1) ≤ g^(2k+1)`.
* `berendBoshernitzan_bound_holds` — the **Berend–Boshernitzan 1994**
  sharpening `m ≤ 2·g^(k+1)` (as transcribed from secondary sources)
  follows for every `g ≥ 2`, since `g^(k+1) ≤ 2·g^(k+1)`.  Our constant is
  half theirs; the earlier `(g+3)·gᵏ` proof (commit `8afbd05`) only reached
  `g ≥ 3`.
* `berendBoshernitzan_strict_holds` — the paper's **open question** (p. 320,
  *"We do not know whether it is true in general that `M(g,k) < g^(k+1)`"*),
  stated as `berendBoshernitzan_strict` and discharged by
  `Mahler.mahler_multiplier_lt` (`MahlerMultiplierStrict.lean`).
-/

namespace NormalNumbers.Literature

open NormalNumbers

/-- **Wired edge: Mahler's Theorem M** (all `g ≥ 2`, all nonempty blocks),
from `mahler_multiplier` and `g^(k+1) ≤ g^(2k+1)`. -/
theorem mahler_theoremM_holds : mahler_theoremM := by
  intro α hα g hg w _ hwd
  obtain ⟨m, hm1, hmM, hio⟩ := Mahler.mahler_multiplier g hg α hα w hwd
  exact ⟨m, hm1, le_trans hmM (Nat.pow_le_pow_right (by omega) (by omega)), hio⟩

/-- **Wired edge: the Berend–Boshernitzan bound `m ≤ 2·g^(k+1)`** for every
`g ≥ 2`, from `mahler_multiplier` since `g^(k+1) ≤ 2·g^(k+1)`. -/
theorem berendBoshernitzan_bound_holds : berendBoshernitzan_bound := by
  intro α hα g hg w _ hwd
  obtain ⟨m, hm1, hmM, hio⟩ := Mahler.mahler_multiplier g hg α hα w hwd
  exact ⟨m, hm1, le_trans hmM (by omega), hio⟩

/-- The `g ≥ 3` form kept for reference (now a special case of
`berendBoshernitzan_bound_holds`). -/
theorem berendBoshernitzan_bound_holds_of_three_le (α : ℝ) (hα : Irrational α)
    (g : ℕ) (hg : 3 ≤ g) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 * g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨m, hm1, hmM, hio⟩ := Mahler.mahler_multiplier g (by omega) α hα w hwd
  exact ⟨m, hm1, le_trans hmM (by omega), hio⟩

/-- **Berend–Boshernitzan 1994, the open question of p. 320**: is
`M(g,k) < g^(k+1)` in general?  I.e. for every irrational `α`, base `g ≥ 2`
and nonempty `g`-block `w`, is there `1 ≤ m < g^(k+1)` with `w` occurring
infinitely often in `m·α`?  provenance: primary
(`papers/berend-boshernitzan-1994-mahler-multiples.pdf`, p. 320). -/
def berendBoshernitzan_strict : Prop :=
  ∀ (α : ℝ), Irrational α → ∀ (g : ℕ), 2 ≤ g → ∀ (w : List ℕ), w ≠ [] →
    (∀ d ∈ w, d < g) →
    ∃ m : ℕ, 1 ≤ m ∧ m < g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n

/-- **Wired edge: the open question is answered YES**, from
`Mahler.mahler_multiplier_lt`. -/
theorem berendBoshernitzan_strict_holds : berendBoshernitzan_strict := by
  intro α hα g hg w _ hwd
  exact Mahler.mahler_multiplier_lt g hg α hα w hwd

end NormalNumbers.Literature
