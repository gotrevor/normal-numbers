/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-AG: the stall clock — `width < η` is *literally* "stalling for longer than `K(η)`"

S7-SA proved the stall bound for a run that stalls *forever*, because that is the hypothesis
`runState_add_of_stall` (S7-RC) was stated with.  For `WidthFreqBound` one needs it for the
CURRENT stall, so this module

* re-proves the right-composition identity with the **finite-range** stall hypothesis
  (`runState_add_of_stall'`), and
* introduces the stall clock `stallAge` — steps since the last emission — and shows it certifies
  its own stall (`stall_of_stallAge`),

giving the pointwise statement the decomposition actually needs:

    `width_le_of_stallAge` :  width (runState Φ x n)  ≤  36 / fib (stallAge n + 1)²  ,
    `stallAge_lt_of_width` :  η ≤ width  ⟹  fib (stallAge n + 1)² ≤ 36/η .

So "the state is narrow at time `n`" is not a geometric condition at all — it says exactly that
the transducer has not emitted for `≳ log(1/η)/log φ` steps.  `WidthFreqBound` is therefore
equivalent to a statement about the **emission schedule alone**: the times lying deeper than
`K(η)` inside a stall have frequency `→ 0` as `η → 0`.  That is Vandehey's Lemma 6.1
(`ℓ(n) = c₁·n(1+o(1))`) and nothing else; no geometry, no state space, no cells.
-/
import NormalNumbers.VandeheyS7Stall

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## The finite-range stall identity -/

/-- **A stall over a finite range composes reads on the right.**  Same proof as
`runState_add_of_stall`, but only assuming the stall on the range actually used. -/
theorem runState_add_of_stall' (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {n₀ : ℕ} : ∀ k : ℕ,
    (∀ i, i < k → runWord Φ x (n₀ + i) = []) →
    runState Φ x (n₀ + k) = (runState Φ x n₀).comp (cylMap (digitWord (gaussMap^[n₀] x) k)) := by
  intro k
  induction k with
  | zero => intro _; simp [digitWord, cylMap_nil, comp_idMap]
  | succ k ih =>
      intro hstall
      have ihh := ih (fun i hi => hstall i (by omega))
      have hem : ¬ Emittable ((runState Φ x (n₀ + k)).comp (readAt x (n₀ + k))) := by
        intro hcon
        obtain ⟨b, -, hword⟩ := step_emitStep hcon
        have hb : runWord Φ x (n₀ + k) = [b] := hword
        rw [hstall k (by omega)] at hb
        exact absurd hb.symm (by simp)
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
      rw [show n₀ + (k + 1) = n₀ + k + 1 from rfl, hst, ihh, hsplit,
        cylMap_append _ _ hpos, hlast, comp_assoc]

/-- The finite-range version of `d_stall_ge`. -/
theorem d_stall_ge' (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {n₀ k : ℕ}
    (hstall : ∀ i, i < k → runWord Φ x (n₀ + i) = []) :
    (runState Φ x n₀).minDen * (Nat.fib (k + 1) : ℝ) ≤ (runState Φ x (n₀ + k)).d := by
  have hxo : ∀ j, gaussMap^[j] (gaussMap^[n₀] x) ∈ Set.Ioo (0:ℝ) 1 := by
    intro j; rw [← Function.iterate_add_apply]; exact hx _
  have hpos : ∀ e ∈ digitWord (gaussMap^[n₀] x) k, 1 ≤ e := by
    intro e he
    simp only [digitWord, List.mem_map, List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact one_le_cfDigit hxo j
  have heq := runState_add_of_stall' Φ hx k hstall
  obtain ⟨-, hfd⟩ := fib_le_cylMap (digitWord (gaussMap^[n₀] x) k) hpos
  rw [digitWord_length] at hfd
  have hmin : 0 < (runState Φ x n₀).minDen := minDen_pos _
  calc (runState Φ x n₀).minDen * (Nat.fib (k + 1) : ℝ)
      ≤ (runState Φ x n₀).minDen * (cylMap (digitWord (gaussMap^[n₀] x) k)).d :=
        mul_le_mul_of_nonneg_left hfd hmin.le
    _ ≤ ((runState Φ x n₀).comp (cylMap (digitWord (gaussMap^[n₀] x) k))).d :=
        minDen_mul_le_comp_d _ _
    _ = (runState Φ x (n₀ + k)).d := by rw [heq]

/-- The finite-range version of `width_stall_le`. -/
theorem width_stall_le' (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {j k : ℕ}
    (hstall : ∀ i, i < k → runWord Φ x (j + 2 + i) = []) :
    (runState Φ x (j + 2 + k)).width ≤ 36 / (Nat.fib (k + 1) : ℝ) ^ 2 := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hfibpos : (0:ℝ) < (Nat.fib (k + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hsq : Real.sqrt (|Φ.det| / 6) ^ 2 = |Φ.det| / 6 := Real.sq_sqrt (by positivity)
  have hmin : Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (j + 2)).minDen :=
    runState_minDen_ge Φ x j
  have hlow := d_stall_ge' Φ hx (n₀ := j + 2) (k := k) hstall
  have hdge : Real.sqrt (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ) ≤ (runState Φ x (j + 2 + k)).d := by
    refine le_trans ?_ hlow
    exact mul_le_mul_of_nonneg_right hmin hfibpos.le
  have hdpos : (0:ℝ) < (runState Φ x (j + 2 + k)).d := (runState Φ x (j + 2 + k)).hd
  have hup : (runState Φ x (j + 2 + k)).width
      ≤ 6 * |Φ.det| / (runState Φ x (j + 2 + k)).d ^ 2 := by
    have h := (width_runState_bounds Φ x (j + k)).2
    rwa [show j + k + 2 = j + 2 + k from by ring] at h
  refine le_trans hup ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hd2 : (Real.sqrt (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ)) ^ 2
      ≤ (runState Φ x (j + 2 + k)).d ^ 2 := pow_le_pow_left₀ (by positivity) hdge 2
  have hexp : (Real.sqrt (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ)) ^ 2
      = (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ) ^ 2 := by rw [mul_pow, hsq]
  nlinarith [hd2, hexp, hdet, hfibpos]

/-! ## The stall clock -/

/-- Steps since the transducer last emitted. -/
noncomputable def stallAge (Φ : MapState) (x : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if runWord Φ x n = [] then stallAge Φ x n + 1 else 0

lemma stallAge_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    stallAge Φ x (n + 1) = if runWord Φ x n = [] then stallAge Φ x n + 1 else 0 := rfl

/-- **The stall clock certifies its own stall.** -/
theorem stall_of_stallAge (Φ : MapState) (x : ℝ) :
    ∀ (k j : ℕ), stallAge Φ x (j + k) = k → ∀ i, i < k → runWord Φ x (j + i) = [] := by
  intro k
  induction k with
  | zero => intro _ _ i hi; omega
  | succ k ih =>
      intro j hage i hi
      have hsucc : stallAge Φ x (j + k + 1) = k + 1 := by
        rwa [show j + (k + 1) = j + k + 1 from by ring] at hage
      rw [stallAge_succ] at hsucc
      by_cases hw : runWord Φ x (j + k) = []
      · rw [if_pos hw] at hsucc
        have hprev : stallAge Φ x (j + k) = k := by omega
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact ih j hprev i h
        · rw [h]; exact hw
      · rw [if_neg hw] at hsucc; omega

/-- **S7-AG, the headline.**  The width at time `n` is controlled by the stall clock alone. -/
theorem width_le_of_stallAge (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {j k : ℕ}
    (hage : stallAge Φ x (j + 2 + k) = k) :
    (runState Φ x (j + 2 + k)).width ≤ 36 / (Nat.fib (k + 1) : ℝ) ^ 2 :=
  width_stall_le' Φ hx (stall_of_stallAge Φ x k (j + 2) hage)

/-- **The contrapositive.**  A wide state has a small stall clock. -/
theorem stallAge_lt_of_width (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {j k : ℕ} {η : ℝ} (hη : 0 < η)
    (hage : stallAge Φ x (j + 2 + k) = k)
    (hw : η ≤ (runState Φ x (j + 2 + k)).width) :
    ((Nat.fib (k + 1) : ℝ)) ^ 2 ≤ 36 / η := by
  have h := width_le_of_stallAge Φ hx hage
  have hfibpos : (0:ℝ) < (Nat.fib (k + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hle : η ≤ 36 / (Nat.fib (k + 1) : ℝ) ^ 2 := le_trans hw h
  rw [le_div_iff₀ (by positivity)] at hle
  rw [le_div_iff₀ hη]
  linarith

end MapState

section Audit

#print axioms MapState.runState_add_of_stall'
#print axioms MapState.width_stall_le'
#print axioms MapState.stall_of_stallAge
#print axioms MapState.width_le_of_stallAge
#print axioms MapState.stallAge_lt_of_width

end Audit

end NormalNumbers.VandeheyS7
