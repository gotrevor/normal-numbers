/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertStatement

/-!
# Frozen count for the quantitative joint Lambert theorem

`jointWordCount S lengths values N` counts the offsets `n < N` at which **every**
prescribed word starts simultaneously in its own `E_b`.  The predicate is literally the
one frozen in `JointLambertStatement.JointWords`, so `orbit` and `E_b` keep exactly their
existing meaning; only the quantifier is changed from "some late `n`" to "how many `n < N`".

Conventions, fixed here once and for all:

* `n` is an *offset*: the first requested digit is `n + 1`.  A word may run past digit `N`.
* A repeated base is represented once, because `S` is a `Finset`; no incompatible
  repeated-coordinate demand can be expressed.
* Leading-zero words are legitimate (`values b = 0`).
* `S = ∅` imposes no constraint, so the count is `N` (`jointWordCount_empty`).
-/

namespace NormalNumbers.JointLambert

open Finset

/-- The number of offsets `n < N` at which all the prescribed words start at once. -/
noncomputable def jointWordCount (S : Finset ℕ) (lengths values : ℕ → ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun n => ∀ b ∈ S,
    ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) n⌋
      = (values b : ℤ))).card

/-- Membership in the counted set is exactly the `JointWords` predicate at `n`. -/
theorem jointWordCount_eq_card_filter (S : Finset ℕ) (lengths values : ℕ → ℕ) (N : ℕ) :
    jointWordCount S lengths values N =
      ((Finset.range N).filter (fun n => ∀ b ∈ S,
        ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) n⌋
          = (values b : ℤ))).card := by
  classical
  rfl

/-- Boundary control: an empty base set constrains nothing. -/
@[simp] theorem jointWordCount_empty (lengths values : ℕ → ℕ) (N : ℕ) :
    jointWordCount (∅ : Finset ℕ) lengths values N = N := by
  classical
  rw [jointWordCount_eq_card_filter]
  simp

/-- Boundary control: nothing is counted below `0`. -/
@[simp] theorem jointWordCount_zero (S : Finset ℕ) (lengths values : ℕ → ℕ) :
    jointWordCount S lengths values 0 = 0 := by
  classical
  rw [jointWordCount_eq_card_filter]; simp

/-- The count never exceeds the length of the window. -/
theorem jointWordCount_le (S : Finset ℕ) (lengths values : ℕ → ℕ) (N : ℕ) :
    jointWordCount S lengths values N ≤ N := by
  classical
  rw [jointWordCount_eq_card_filter]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- The count is monotone in the window. -/
theorem jointWordCount_mono (S : Finset ℕ) (lengths values : ℕ → ℕ) {M N : ℕ} (h : M ≤ N) :
    jointWordCount S lengths values M ≤ jointWordCount S lengths values N := by
  classical
  rw [jointWordCount_eq_card_filter, jointWordCount_eq_card_filter]
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn.1) h), hn.2⟩

/-- A witness at `n < N` is counted.  This is the bridge from `JointWords`-style
statements to the count. -/
theorem one_le_jointWordCount_of_witness {S : Finset ℕ} {lengths values : ℕ → ℕ} {N n : ℕ}
    (hn : n < N)
    (hw : ∀ b ∈ S, ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) n⌋
      = (values b : ℤ)) :
    1 ≤ jointWordCount S lengths values N := by
  classical
  rw [jointWordCount_eq_card_filter]
  exact Finset.card_pos.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hw⟩⟩

/-- Cardinality lower bound from any finite set of witnesses: this is the form the
counting argument produces (a whole good set, not one witness). -/
theorem jointWordCount_ge_of_subset {S : Finset ℕ} {lengths values : ℕ → ℕ} {N : ℕ}
    (T : Finset ℕ) (hT : ∀ n ∈ T, n < N)
    (hw : ∀ n ∈ T, ∀ b ∈ S,
      ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) n⌋ = (values b : ℤ)) :
    T.card ≤ jointWordCount S lengths values N := by
  classical
  rw [jointWordCount_eq_card_filter]
  refine Finset.card_le_card ?_
  intro n hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hT n hn), hw n hn⟩

end NormalNumbers.JointLambert
