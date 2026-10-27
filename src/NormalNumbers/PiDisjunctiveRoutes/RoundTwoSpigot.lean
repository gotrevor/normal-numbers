/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.RoundTwoPilotTargets

/-!
# Spigot pilot: positive-width states postpone words arbitrarily

Proves the frozen target `PositiveWidthAlternatingPrefix`.  The mechanism is the
two-step affine identity `spigotStep_two_alternating`: on any state with
`q = 3r`, `0 < p`, `8p < r`, the machine emits `0` then `1` without reading,
and the net action is `p ↦ 4p`.  See `docs/pi-routes/pilots/spigot-result.md`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots

/-- The two-step mechanism: emit 0, emit 1, net `(p,r,q) ↦ (4p,r,q)`. -/
theorem spigotStep_two_alternating (s : SpigotState) (hp : 0 < s.p)
    (hq : s.q = 3 * s.r) (hr : 8 * s.p < s.r) :
    spigotStep (spigotStep s) =
      { s with p := 4 * s.p, output := s.output ++ [0, 1] } := by
  obtain ⟨n, p, r, q, o⟩ := s
  simp only at hp hq hr; subst hq
  have h0 : CanEmit ⟨n, p, r, 3 * r, o⟩ 0 := by
    refine ⟨?_, by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith
  have h1 : ¬ CanEmit (emit ⟨n, p, r, 3 * r, o⟩ 0) 0 := by
    rintro ⟨-, -, -, h⟩; simp [emit] at h; linarith
  have h2 : CanEmit (emit ⟨n, p, r, 3 * r, o⟩ 0) 1 := by
    refine ⟨?_, by norm_num, ?_, ?_⟩ <;> simp [emit] <;> linarith
  simp only [spigotStep, if_pos h0, if_neg h1, if_pos h2]
  simp [emit]; constructor <;> ring

/-- Closed form of the alternating run for `k ≤ L`. -/
theorem iterate_alternatingSeed (L k : ℕ) (hk : k ≤ L) :
    iterateSpigot (2 * k) (alternatingSeed L) =
      ⟨0, (4 : ℤ) ^ k, (4 : ℤ) ^ (L + 1), 3 * (4 : ℤ) ^ (L + 1),
        (List.replicate k [0, 1]).flatten⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, iterateSpigot, iterateSpigot, ih (by omega),
      spigotStep_two_alternating _ (by positivity) rfl]
    · simp [List.replicate_succ', pow_succ]; ring
    · show 8 * (4 : ℤ) ^ k < 4 ^ (L + 1)
      have : (4 : ℤ) ^ (k + 1) ≤ 4 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ] at this ⊢; nlinarith [pow_pos (by norm_num : (0:ℤ) < 4) k]

theorem positiveWidthAlternatingPrefix : PositiveWidthAlternatingPrefix := by
  intro L
  refine ⟨by simp [alternatingSeed], by simp [alternatingSeed], ?_, ?_⟩ <;>
    rw [iterate_alternatingSeed L L le_rfl]

theorem alt_flatten_eq (k : ℕ) :
    (List.replicate k [0, 1]).flatten = (List.range (2 * k)).map (· % 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', List.flatten_append, ih,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp [Nat.add_mod]

/-- No adjacent equal letters in the alternating word. -/
theorem alt_avoids_pair (k x : ℕ) (a b : List ℕ) :
    (List.replicate k [0, 1]).flatten ≠ a ++ [x, x] ++ b := by
  intro h
  rw [alt_flatten_eq] at h
  have hl : a.length + 1 < 2 * k := by
    have := congrArg List.length h; simp at this; omega
  have e1 := congrArg (·[a.length]?) h
  have e2 := congrArg (·[a.length + 1]?) h
  simp [hl, show a.length < 2 * k by omega] at e1 e2
  omega

/-- Explicit-quantifier obstruction: no waiting bound depending only on the
input index (here `n = 0`) holds uniformly over states with `0 < p`, `0 < q`:
for every `B` there is such a state whose first `2B` steps read no coefficient
and whose output avoids both `[0,0]` and `[1,1]`.  Not a statement about
`spigotInitial`; these states are not claimed reachable from it. -/
@[blueprint (title := "No index-only spigot waiting bound over positive-width states")]
theorem no_index_uniform_waiting_bound (B : ℕ) :
    ∃ s : SpigotState, s.n = 0 ∧ 0 < s.p ∧ 0 < s.q ∧
      (iterateSpigot (2 * B) s).n = 0 ∧
      (iterateSpigot (2 * B) s).output.length = 2 * B ∧
      (¬ ∃ a b, (iterateSpigot (2 * B) s).output = a ++ [0, 0] ++ b) ∧
      (¬ ∃ a b, (iterateSpigot (2 * B) s).output = a ++ [1, 1] ++ b) := by
  obtain ⟨hp, hq, hn, ho⟩ := positiveWidthAlternatingPrefix B
  refine ⟨alternatingSeed B, rfl, hp, hq, hn, ?_, ?_, ?_⟩ <;> rw [ho]
  · simp [mul_comm]
  · rintro ⟨a, b, h⟩; exact alt_avoids_pair B 0 a b h
  · rintro ⟨a, b, h⟩; exact alt_avoids_pair B 1 a b h

/-- Auxiliary control (p = 0): an exact two-cycle `(0,r,3r) ↦ (0,r,3r)`. -/
theorem zeroWidth_twoCycle (r : ℤ) (hr : 0 < r) :
    spigotStep (spigotStep ⟨0, 0, r, 3 * r, []⟩) = ⟨0, 0, r, 3 * r, [0, 1]⟩ := by
  have h0 : CanEmit ⟨0, 0, r, 3 * r, []⟩ 0 := by
    refine ⟨?_, by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith
  have h1 : ¬ CanEmit (emit ⟨0, 0, r, 3 * r, []⟩ 0) 0 := by
    rintro ⟨-, -, -, h⟩; simp [emit] at h; linarith
  have h2 : CanEmit (emit ⟨0, 0, r, 3 * r, []⟩ 0) 1 := by
    refine ⟨?_, by norm_num, ?_, ?_⟩ <;> simp [emit] <;> linarith
  simp only [spigotStep, if_pos h0, if_neg h1, if_pos h2]
  simp [emit]; ring

/-- The precise rank family this excludes: any rank `ρ(s)` that is bounded by a
function of `s.n` alone and strictly drops at each emit step. -/
theorem no_index_only_emit_rank :
    ¬ ∃ f : ℕ → ℕ, ∀ s : SpigotState, 0 < s.p → 0 < s.q →
      ∀ t, (iterateSpigot t s).n = s.n → t ≤ f s.n := by
  rintro ⟨f, hf⟩
  obtain ⟨hp, hq, hn, -⟩ := positiveWidthAlternatingPrefix (f 0 + 1)
  have := hf _ hp hq _ hn
  simp [alternatingSeed] at this; omega

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots
