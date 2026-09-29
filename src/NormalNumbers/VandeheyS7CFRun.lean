/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CR2: the input word of a real number, as a `MapState`

S7-EA's hypotheses are abstract: a sequence of input words of unbounded length whose composite
state carries a fixed irrational value.  This module instantiates them from a real `x` with a full
irrational Gauss orbit, so nothing abstract is left on that side.

* `cylMap_append` — `cylMap` turns concatenation into composition.
* `readMap_cfDigit_mob` — reading the `n`-th CF digit sends `Gⁿ⁺¹x` back to `Gⁿx`.
* `cylMap_digitWord_mob` — **the run identity**: `cylMap (digitWord x n)` sends `Gⁿx` back to `x`.
* `exists_emit_eventually_cf` — hence, for any state `s` whose value `s.mob x` is irrational,
  the transducer state after `n` reads emits for all large `n`.

That last is `StatePin.clockUnbounded` for a concrete input, with the only remaining hypothesis
being irrationality of the image point `s.mob x` — which for `s = Φ = diag(φ,1)` is irrationality
of `φx`, already available on the §7 front.
-/
import NormalNumbers.VandeheyS7EmitAll

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

theorem cylMap_append : ∀ (w w' : List ℕ), (∀ e ∈ w, 1 ≤ e) →
    cylMap (w ++ w') = (cylMap w).comp (cylMap w')
  | [], w', _ => by
      refine ext_entries ?_ ?_ ?_ ?_ <;>
        simp [cylMap_nil, comp_a, comp_b, comp_c, comp_d, idMap]
  | a :: w, w', hpos => by
      have ha : 1 ≤ a := hpos a (by simp)
      have hw : ∀ e ∈ w, 1 ≤ e := fun e he => hpos e (by simp [he])
      rw [List.cons_append, cylMap_cons ha, cylMap_cons ha, cylMap_append w w' hw, comp_assoc]

/-- Every CF digit of an irrational of `(0,1)` is genuine. -/
lemma one_le_cfDigit {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    1 ≤ cfDigit x n := by
  have h0 : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) 1 := hx n
  have hone : (1:ℝ) < (gaussMap^[n] x)⁻¹ := by
    rw [lt_inv_comm₀ one_pos h0.1]; simpa using h0.2
  rw [cfDigit, Nat.le_floor_iff (by positivity)]
  exact_mod_cast hone.le

/-- **Reading a digit** sends `Gⁿ⁺¹x` back to `Gⁿx`. -/
theorem readMap_cfDigit_mob {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    (readMap ((cfDigit x n : ℕ) : ℝ)
      (by exact_mod_cast one_le_cfDigit hx n)).mob (gaussMap^[n + 1] x) = gaussMap^[n] x := by
  have h0 : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) 1 := hx n
  have hstep : gaussMap^[n + 1] x = Int.fract (gaussMap^[n] x)⁻¹ := by
    rw [Function.iterate_succ_apply', gaussMap, if_neg h0.1.ne']
  have hcast : ((cfDigit x n : ℕ) : ℝ) = (⌊(gaussMap^[n] x)⁻¹⌋ : ℝ) := by
    rw [cfDigit]
    exact natCast_floor_eq_intCast_floor (le_of_lt (inv_pos.2 h0.1))
  rw [readMap_mob, hstep, hcast, Int.fract, sub_add_cancel, one_div, inv_inv]

/-- **The run identity.**  The input word read so far sends the current orbit point back to `x`. -/
theorem cylMap_digitWord_mob {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    (cylMap (digitWord x n)).mob (gaussMap^[n] x) = x := by
  induction n with
  | zero => simp [digitWord, cylMap_nil]
  | succ n ih =>
      have hsplit : digitWord x (n + 1) = digitWord x n ++ [cfDigit x n] := by
        simp [digitWord, List.range_succ]
      have hpos : ∀ e ∈ digitWord x n, 1 ≤ e := by
        intro e he
        simp only [digitWord, List.mem_map, List.mem_range] at he
        obtain ⟨k, _, rfl⟩ := he
        exact one_le_cfDigit hx k
      have hd : cylMap [cfDigit x n]
          = readMap ((cfDigit x n : ℕ) : ℝ) (by exact_mod_cast one_le_cfDigit hx n) := by
        rw [cylMap_cons (one_le_cfDigit hx n), cylMap_nil]
        refine ext_entries ?_ ?_ ?_ ?_ <;>
          simp [comp_a, comp_b, comp_c, comp_d, idMap, readMap]
      rw [hsplit, cylMap_append _ _ hpos, hd,
        mob_comp (cylMap (digitWord x n)) _ (⟨(hx (n + 1)).1.le, (hx (n + 1)).2.le⟩),
        readMap_cfDigit_mob hx n, ih]

/-- **S7-CR2.**  For a concrete input with a full irrational orbit and a state whose value at `x`
is irrational, the transducer emits at all large input times. -/
theorem exists_emit_eventually_cf (s : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hmem : s.mob x ∈ Ioo (0:ℝ) 1) (hirr : Irrational (s.mob x)) :
    ∀ᶠ n in atTop, ∃ (b : ℕ) (hb : 1 ≤ b) (u : MapState),
      (readMap (b : ℝ) (by exact_mod_cast hb)).comp u = s.comp (cylMap (digitWord x n)) := by
  refine exists_emit_eventually s hmem hirr (v := fun n => digitWord x n) ?_ ?_
    (z := fun n => gaussMap^[n] x) (fun n => ⟨(hx n).1.le, (hx n).2.le⟩) ?_
  · intro n e he
    simp only [digitWord, List.mem_map, List.mem_range] at he
    obtain ⟨k, _, rfl⟩ := he
    exact one_le_cfDigit hx k
  · simp only [digitWord_length]
    exact tendsto_id
  · intro n
    rw [mob_comp _ _ ⟨(hx n).1.le, (hx n).2.le⟩, cylMap_digitWord_mob hx n]

end MapState

section Audit

#print axioms MapState.cylMap_digitWord_mob
#print axioms MapState.exists_emit_eventually_cf

end Audit

end NormalNumbers.VandeheyS7
