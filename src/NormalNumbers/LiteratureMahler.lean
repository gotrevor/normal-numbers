/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.MahlerMultiplier

/-!
# Ledger edges from Mahler's multiplier theorem 📚→✅

`MahlerMultiplier.lean` proves `mahler_multiplier`: some `m ≤ (g+3)·gᵏ`
has the block `w` (of length `k`) occurring i.o. in `m·α`.  This file wires
that theorem into the literature ledger:

* `mahler_theoremM_holds` — **Mahler 1973, Theorem M** (`m ≤ g^(2k+1)`) is
  now independently verified for all `g ≥ 2`, `k ≥ 1`: the bound
  `(g+3)gᵏ ≤ g^(2k+1)` holds except at `(g,k) = (2,1)`, where single bits
  trivially recur (`adamczewskiRampersad_boundary_holds`, `m = 1`).
* `berendBoshernitzan_bound_holds_of_three_le` — the **Berend–Boshernitzan
  1994** sharpening `m ≤ 2·g^(k+1)` (as transcribed from secondary sources)
  follows for every `g ≥ 3`, since `(g+3)gᵏ ≤ 2g·gᵏ ⟺ g ≥ 3`.  The case
  `g = 2` (`5·2ᵏ` vs `4·2ᵏ`) is NOT covered by the present constant and
  stays a cited-only gap.
-/

namespace NormalNumbers.Literature

open NormalNumbers

/-- **Wired edge: Mahler's Theorem M** (all `g ≥ 2`, all nonempty blocks),
from `mahler_multiplier` plus the single-bit boundary case. -/
theorem mahler_theoremM_holds : mahler_theoremM := by
  intro α hα g hg w hw hwd
  have hk1 : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  by_cases h21 : g = 2 ∧ w.length = 1
  · -- base 2, single bits: `m = 1` by the Adamczewski–Rampersad boundary
    obtain ⟨hg2, hlen⟩ := h21
    subst hg2
    obtain ⟨d, rfl⟩ : ∃ d, w = [d] := by
      rcases w with _ | ⟨d, _ | ⟨e, w'⟩⟩
      · simp at hlen
      · exact ⟨d, rfl⟩
      · simp at hlen
    have hd : d < 2 := hwd d (by simp)
    refine ⟨1, le_rfl, by norm_num, ?_⟩
    intro N
    have hmem : [d] ∈ [[0], [1], [0, 1], [1, 0]] := by
      interval_cases d <;> simp
    obtain ⟨n, hn, hocc⟩ := adamczewskiRampersad_boundary_holds α hα [d] hmem N
    exact ⟨n, hn, by simpa using hocc⟩
  · obtain ⟨m, hm1, hmM, hio⟩ := Mahler.mahler_multiplier g hg α hα w hwd
    refine ⟨m, hm1, le_trans hmM ?_, hio⟩
    have hkey : g + 3 ≤ g ^ (w.length + 1) := by
      rcases Nat.lt_or_ge w.length 2 with hk2 | hk2
      · have hlen : w.length = 1 := by omega
        have hg3 : 3 ≤ g := by
          by_contra h
          push Not at h
          exact h21 ⟨by omega, hlen⟩
        rw [hlen, pow_two]
        have : 3 * g ≤ g * g := Nat.mul_le_mul_right g hg3
        omega
      · have h4 : 2 * 2 * g ≤ g * g * g := Nat.mul_le_mul_right g (Nat.mul_le_mul hg hg)
        calc g + 3 ≤ g * g * g := by omega
          _ = g ^ 3 := by ring
          _ ≤ g ^ (w.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (g + 3) * g ^ w.length ≤ g ^ (w.length + 1) * g ^ w.length :=
          Nat.mul_le_mul_right _ hkey
      _ = g ^ (2 * w.length + 1) := by rw [← pow_add]; congr 1; ring

/-- **Wired edge (g ≥ 3): the Berend–Boshernitzan bound `m ≤ 2·g^(k+1)`**,
from `mahler_multiplier` since `(g+3)·gᵏ ≤ 2g·gᵏ` for `g ≥ 3`.  The base-2
case is not covered by the constant `(g+3)gᵏ` (open gap). -/
theorem berendBoshernitzan_bound_holds_of_three_le (α : ℝ) (hα : Irrational α)
    (g : ℕ) (hg : 3 ≤ g) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 * g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨m, hm1, hmM, hio⟩ := Mahler.mahler_multiplier g (by omega) α hα w hwd
  refine ⟨m, hm1, le_trans hmM ?_, hio⟩
  calc (g + 3) * g ^ w.length ≤ (2 * g) * g ^ w.length :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 2 * g ^ (w.length + 1) := by ring

end NormalNumbers.Literature
