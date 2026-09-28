/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyCocycle

/-!
# The class automaton: the Gauss map read modulo `D`

`PROBE-2026-09-27-transducer-not-synchronizing.md` shows that the det-`±D` CF transducer is
**not** synchronizing, and that mergeability of two states is exactly equality of the row
lattice `ℤ²M` up to scaling.  This module identifies the resulting class dynamics in closed
form, and the answer is as clean as it could be.

A row lattice of index `D` in `ℤ²` is either `L_b = {(u,v) : v ≡ b u}` for `b ∈ ℤ/D`, or
`L_∞ = {(u,v) : u ≡ 0}`.  Ingesting a digit multiplies on the right by `B_a = [[0,1],[1,a]]`,
i.e. `(u,v) ↦ (v, u + a v)`, and matching coefficients gives

* `L_b ↦ L_{a + b⁻¹}` when `b` is invertible,
* `L_0 ↦ L_∞`,
* `L_∞ ↦ L_a`.

So **the class cocycle is the continued-fraction map `s ↦ a + 1/s` read modulo `D`**, acting on
`ℙ¹(ℤ/D)` in slope coordinates.  (Verified against the transducer itself in
`probes/cf_transducer_class.py`: 8488 transitions over `D = 2, 3, 5` and four different
matrices, zero mismatches.)

That identification is what makes the crux concrete.  The two facts the Markov step needs are
proved here:

* **`exists_word_reach`** — the walk is transitive, and in at most three steps: every class
  reaches `∞` in `≤ 2` digits (steer `b ↦ a + b⁻¹` to `0` by choosing `a ≡ −b⁻¹`, then `0 ↦ ∞`
  for free), and `∞ ↦ a` reaches every class in one more.  Note the steering digit depends on
  the current class — which is exactly why the automaton is transitive but **not**
  synchronizing, in one line.
* **`classStep_of_cast_eq`** — the automaton reads a digit only modulo `D`.
-/

namespace NormalNumbers

namespace VandeheyClass

open VandeheyAut

/-- `ℙ¹(ℤ/D)` in slope coordinates: `none` is the point at infinity. -/
abbrev ClassSpace (D : ℕ) := Option (ZMod D)

/-- **The class automaton**: the continued-fraction map `s ↦ a + 1/s` modulo `D`. -/
def classStep (D : ℕ) : ClassSpace D → ℕ → ClassSpace D
  | none, a => some (a : ZMod D)
  | some s, a => if s = 0 then none else some ((a : ZMod D) + s⁻¹)

@[simp] lemma classStep_none (D : ℕ) (a : ℕ) :
    classStep D none a = some (a : ZMod D) := rfl

@[simp] lemma classStep_zero (D : ℕ) (a : ℕ) : classStep D (some 0) a = none := by
  simp [classStep]

lemma classStep_some_of_ne (D : ℕ) {s : ZMod D} (hs : s ≠ 0) (a : ℕ) :
    classStep D (some s) a = some ((a : ZMod D) + s⁻¹) := by
  simp [classStep, hs]

/-- The automaton reads its digit only modulo `D` — the reason the class walk is a finite
object at all. -/
lemma classStep_of_cast_eq (D : ℕ) (c : ClassSpace D) {a b : ℕ}
    (h : (a : ZMod D) = (b : ZMod D)) : classStep D c a = classStep D c b := by
  cases c with
  | none => simp [h]
  | some s => by_cases hs : s = 0 <;> simp [classStep, hs, h]

/-! ## Every residue is spelled by a genuine (positive) digit -/

/-- Any target residue is realized by a CF digit, i.e. by a natural number `≥ 1`.  This is
where `D ≥ 1` is used: the residue `0` is spelled by the digit `D` itself, never by `0`. -/
lemma exists_digit_cast (D : ℕ) (hD : 1 ≤ D) (z : ZMod D) :
    ∃ a : ℕ, 1 ≤ a ∧ (a : ZMod D) = z := by
  haveI : NeZero D := ⟨by omega⟩
  rcases eq_or_ne z 0 with hz | hz
  · exact ⟨D, hD, by simp [hz]⟩
  · refine ⟨z.val, ?_, ZMod.natCast_rightInverse z⟩
    rcases Nat.eq_zero_or_pos z.val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse z, h0]; simp) hz
    · exact h0

/-! ## Transitivity of the class walk -/

/-- Every class reaches the point at infinity in at most two digits.

The steering digit `a ≡ −b⁻¹` **depends on the current class** — which is precisely why the
walk is transitive yet admits no synchronizing word (`PROBE-2026-09-27-…`). -/
theorem exists_word_reach_none (D : ℕ) [Fact (Nat.Prime D)] (c : ClassSpace D) :
    ∃ w : List ℕ, w ≠ [] ∧ w.length ≤ 2 ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState (classStep D) c w = none := by
  have hD : 1 ≤ D := le_of_lt (Fact.out : Nat.Prime D).one_lt
  cases c with
  | none =>
    -- `∞ ↦ 0 ↦ ∞`
    obtain ⟨a, ha, hacast⟩ := exists_digit_cast D hD 0
    refine ⟨[a, 1], by simp, by simp, ?_, ?_⟩
    · intro b hb; rcases List.mem_cons.mp hb with h | h
      · omega
      · simp at h; omega
    · simp [runState, hacast]
  | some s =>
    by_cases hs : s = 0
    · exact ⟨[1], by simp, by simp, by intro b hb; simp at hb; omega, by simp [runState, hs]⟩
    · -- steer `b ↦ a + b⁻¹` to `0`
      obtain ⟨a, ha, hacast⟩ := exists_digit_cast D hD (-s⁻¹)
      refine ⟨[a, 1], by simp, by simp, ?_, ?_⟩
      · intro b hb; rcases List.mem_cons.mp hb with h | h
        · omega
        · simp at h; omega
      · simp [runState, classStep_some_of_ne D hs, hacast]

/-- **Transitivity**: any class reaches any class along a genuine CF word of length `≤ 3`. -/
theorem exists_word_reach (D : ℕ) [Fact (Nat.Prime D)] (c c' : ClassSpace D) :
    ∃ w : List ℕ, w ≠ [] ∧ w.length ≤ 3 ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState (classStep D) c w = c' := by
  have hD : 1 ≤ D := le_of_lt (Fact.out : Nat.Prime D).one_lt
  obtain ⟨w, hwne, hwlen, hwpos, hw⟩ := exists_word_reach_none D c
  cases c' with
  | none => exact ⟨w, hwne, by omega, hwpos, hw⟩
  | some z =>
    obtain ⟨a, ha, hacast⟩ := exists_digit_cast D hD z
    refine ⟨w ++ [a], by simp [hwne], ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact hwpos b h
      · simp at h; omega
    · rw [runState_append, hw]
      simp [runState, hacast]

/-- The walk is **aperiodic on the class space**: from `∞` one returns to `∞` in two steps and
in three.  (Every class reaches `∞`, so this pins the period of the whole chain to `1`.) -/
theorem exists_return_two_and_three (D : ℕ) [Fact (Nat.Prime D)] :
    (∃ w : List ℕ, w.length = 2 ∧ (∀ a ∈ w, 1 ≤ a) ∧
        runState (classStep D) (none : ClassSpace D) w = none) ∧
      (∃ w : List ℕ, w.length = 3 ∧ (∀ a ∈ w, 1 ≤ a) ∧
        runState (classStep D) (none : ClassSpace D) w = none) := by
  have hD : 1 ≤ D := le_of_lt (Fact.out : Nat.Prime D).one_lt
  haveI : Fact (Nat.Prime D) := inferInstance
  obtain ⟨a, ha, hacast⟩ := exists_digit_cast D hD 0
  obtain ⟨a', ha', ha'cast⟩ := exists_digit_cast D hD (-1)
  have hone : (1 : ZMod D) ≠ 0 := one_ne_zero
  refine ⟨⟨[a, 1], by simp, ?_, by simp [runState, hacast]⟩,
    ⟨[1, a', 1], by simp, ?_, ?_⟩⟩
  · intro b hb; rcases List.mem_cons.mp hb with h | h
    · omega
    · simp at h; omega
  · intro b hb
    rcases List.mem_cons.mp hb with h | h
    · omega
    · rcases List.mem_cons.mp h with h' | h'
      · omega
      · simp at h'; omega
  · show classStep D (classStep D (classStep D none 1) a') 1 = none
    rw [classStep_none, Nat.cast_one, classStep_some_of_ne D hone, ha'cast, inv_one]
    simp

/-! ## Anchors against the measured transducer

These pin the Lean definition to the transducer's *actual* measured behaviour
(`probes/cf_transducer_class.py`, which agrees with the slope model on 8488 transitions over
`D = 2, 3, 5` with zero mismatches).  Without them `classStep` would be an unchecked
transcription of a hand computation. -/

example : classStep 2 none 1 = some 1 := by simp
example : classStep 2 (some 0) 1 = none := by simp

/-- `D = 2`, class `b = 1`, digit `1`: `1 + 1⁻¹ = 0`.  Measured: `(1,1,2) → (1,0,2)`. -/
example : classStep 2 (some 1) 1 = some 0 := by
  rw [classStep_some_of_ne 2 (by decide), Nat.cast_one, inv_one]; decide

/-- `D = 2`, class `b = 1`, digit `2`: `0 + 1⁻¹ = 1`.  Measured: `(1,1,2) → (1,1,2)`. -/
example : classStep 2 (some 1) 2 = some 1 := by
  rw [classStep_some_of_ne 2 (by decide), inv_one]; decide

/-- `D = 3`, class `b = 1`, digit `1`: `1 + 1⁻¹ = 2`.  Measured: `(1,1,3) → (1,2,3)`. -/
example : classStep 3 (some 1) 1 = some 2 := by
  rw [classStep_some_of_ne 3 (by decide), Nat.cast_one, inv_one]; decide

/-- `D = 3`, class `b = 1`, digit `2`: `2 + 1⁻¹ = 0`.  Measured: `(1,1,3) → (1,0,3)`. -/
example : classStep 3 (some 1) 2 = some 0 := by
  rw [classStep_some_of_ne 3 (by decide), inv_one]; decide

/-- `D = 3`, class `b = 2`, digit `1`: `1 + 2⁻¹ = 1 + 2 = 0`.
Measured: `(1,2,3) → (1,0,3)`. -/
example : classStep 3 (some 2) 1 = some 0 := by
  rw [classStep_some_of_ne 3 (by decide), Nat.cast_one]
  have : (2 : ZMod 3)⁻¹ = 2 :=
    inv_eq_of_mul_eq_one_right (by decide : (2 : ZMod 3) * 2 = 1)
  rw [this]; decide

/-- `D = 3`, the point at infinity, digit `1`.  Measured: `(3,0,1) → (1,1,3)`. -/
example : classStep 3 none 1 = some 1 := by simp

end VandeheyClass

end NormalNumbers
