/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RC3: the clock of the run is unbounded

The last field of a `StatePin`.  Suppose the machine stalls from input time `n₀` on.  Then for
every `k` the state is literally `runState n₀ ∘ cylMap (the next k input digits)`
(`runState_add_of_stall`), and S7-CR2 says such a state must emit for large `k`, because its value
`runValue n₀` is an irrational of `(0,1)` (S7-RO) and the input word contracts (S7-CM).  So the
stall is impossible, emissions recur, and the clock tends to infinity.

No width floor, no distortion bound, no equidistribution: only that the image orbit point is
irrational.
-/
import NormalNumbers.VandeheyS7RunOrbit

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

lemma cfDigit_shift (x : ℝ) (n₀ k : ℕ) : cfDigit (gaussMap^[n₀] x) k = cfDigit x (n₀ + k) := by
  rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm]

lemma readAt_eq {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    readAt x n = readMap ((cfDigit x n : ℕ) : ℝ) (by exact_mod_cast one_le_cfDigit hx n) := by
  refine ext_entries ?_ ?_ ?_ ?_ <;>
    simp [readAt, readMap, inDigit_eq_cfDigit hx n]

/-- **A stalling suffix composes reads on the right.** -/
theorem runState_add_of_stall (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {n₀ : ℕ}
    (hstall : ∀ m, n₀ ≤ m → runWord Φ x m = []) : ∀ k : ℕ,
    runState Φ x (n₀ + k) = (runState Φ x n₀).comp (cylMap (digitWord (gaussMap^[n₀] x) k)) := by
  intro k
  induction k with
  | zero => simp [digitWord, cylMap_nil, comp_idMap]
  | succ k ih =>
      have hem : ¬ Emittable ((runState Φ x (n₀ + k)).comp (readAt x (n₀ + k))) := by
        intro hcon
        obtain ⟨b, -, hword⟩ := step_emitStep hcon
        have : runWord Φ x (n₀ + k) = [b] := hword
        rw [hstall _ (by omega)] at this
        exact absurd this (by simp)
      have hst : runState Φ x (n₀ + k + 1)
          = (runState Φ x (n₀ + k)).comp (readAt x (n₀ + k)) := by
        show (step _).1 = _
        rw [step_of_not_emittable hem]
      have hxo : ∀ j, gaussMap^[j] (gaussMap^[n₀] x) ∈ Set.Ioo (0:ℝ) 1 := by
        intro j
        rw [← Function.iterate_add_apply]
        exact hx _
      have hpos : ∀ e ∈ digitWord (gaussMap^[n₀] x) k, 1 ≤ e := by
        intro e he
        simp only [digitWord, List.mem_map, List.mem_range] at he
        obtain ⟨j, -, rfl⟩ := he
        exact one_le_cfDigit hxo j
      have hsplit : digitWord (gaussMap^[n₀] x) (k + 1)
          = digitWord (gaussMap^[n₀] x) k ++ [cfDigit (gaussMap^[n₀] x) k] := by
        simp [digitWord, List.range_succ]
      have hdig : cfDigit (gaussMap^[n₀] x) k = cfDigit x (n₀ + k) := cfDigit_shift x n₀ k
      have hlast : cylMap [cfDigit (gaussMap^[n₀] x) k] = readAt x (n₀ + k) := by
        rw [hdig, cylMap_singleton (one_le_cfDigit hx (n₀ + k)), readAt_eq hx]
      rw [show n₀ + (k + 1) = n₀ + k + 1 from rfl, hst, ih, hsplit,
        cylMap_append _ _ hpos, hlast, comp_assoc]

/-- **Emissions recur.** -/
theorem exists_emit_ge (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (n₀ : ℕ) :
    ∃ m, n₀ ≤ m ∧ runWord Φ x m ≠ [] := by
  by_contra hcon
  push_neg at hcon
  have hstall : ∀ m, n₀ ≤ m → runWord Φ x m = [] := hcon
  have hxo : ∀ j, gaussMap^[j] (gaussMap^[n₀] x) ∈ Set.Ioo (0:ℝ) 1 := by
    intro j
    rw [← Function.iterate_add_apply]
    exact hx _
  obtain ⟨hmem, hirr, -⟩ := runValue_spec Φ hx hy hyirr n₀
  have hval : (runState Φ x n₀).mob (gaussMap^[n₀] x) = runValue Φ x n₀ := rfl
  have hev := exists_emit_eventually_cf (runState Φ x n₀) hxo (by rw [hval]; exact hmem)
    (by rw [hval]; exact hirr)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨b, hb, u, hu⟩ := hK (K + 1) (by omega)
  -- that state is the one the machine sees at input time `n₀ + K`, which must therefore emit
  have hstate : (runState Φ x n₀).comp (cylMap (digitWord (gaussMap^[n₀] x) (K + 1)))
      = runState Φ x (n₀ + (K + 1)) := (runState_add_of_stall Φ hx hstall (K + 1)).symm
  have hem : Emittable ((runState Φ x (n₀ + K)).comp (readAt x (n₀ + K))) := by
    have hnext : runState Φ x (n₀ + (K + 1))
        = (runState Φ x (n₀ + K)).comp (readAt x (n₀ + K)) := by
      have hemk : ¬ Emittable ((runState Φ x (n₀ + K)).comp (readAt x (n₀ + K))) := by
        intro hc
        obtain ⟨c, -, hword⟩ := step_emitStep hc
        have : runWord Φ x (n₀ + K) = [c] := hword
        rw [hstall _ (by omega)] at this
        exact absurd this (by simp)
      have hidx : n₀ + (K + 1) = (n₀ + K) + 1 := by omega
      rw [hidx]
      show (step _).1 = _
      rw [step_of_not_emittable hemk]
    exact ⟨b, u, (emitStep_iff hb).2 (by rw [← hnext, ← hstate]; exact hu)⟩
  obtain ⟨c, -, hword⟩ := step_emitStep hem
  have : runWord Φ x (n₀ + K) = [c] := hword
  rw [hstall _ (by omega)] at this
  exact absurd this (by simp)

/-- **S7-RC3.**  The clock of the run tends to infinity. -/
theorem runClock_tendsto (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) :
    Tendsto (runClock Φ x) atTop atTop := by
  have hgrow : ∀ M : ℕ, ∃ n : ℕ, M ≤ runClock Φ x n := by
    intro M
    induction M with
    | zero => exact ⟨0, by simp⟩
    | succ M ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm, hne⟩ := exists_emit_ge Φ hx hy hyirr n
        refine ⟨m + 1, ?_⟩
        have h1 : 1 ≤ (runWord Φ x m).length := List.length_pos_iff.2 hne
        have h2 : runClock Φ x n ≤ runClock Φ x m := runClock_mono Φ x hm
        rw [runClock_succ]
        omega
  refine tendsto_atTop_atTop.2 fun M => ?_
  obtain ⟨n, hn⟩ := hgrow M
  exact ⟨n, fun m hm => le_trans hn (runClock_mono Φ x hm)⟩

end MapState

section Audit

#print axioms MapState.runState_add_of_stall
#print axioms MapState.exists_emit_ge
#print axioms MapState.runClock_tendsto

end Audit

end NormalNumbers.VandeheyS7
