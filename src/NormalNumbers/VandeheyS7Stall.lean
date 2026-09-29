/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SA: wide states are RECENTLY-EMITTED states — the stall shrinks the width, absolutely

`WidthFreqBound` (S7-CL) asks how often the run's state is narrow.  This module answers the
*structural* half of that question, unconditionally and with no constant depending on `Φ`:

    a stall of length `k` forces  width ≤ 36 / fib(k+1)²        (`width_stall_le`)

Equivalently — the contrapositive, which is the usable form — **a state of width `≥ η` has been
stalling for at most `O(log(1/η))` steps**: wide states occur only shortly after an emission.

The mechanism is the continuant, in two steps.

* `fib_le_cylMap` — reading `k` digits is composition with a `cylMap` whose `(b,d)` obey the
  Fibonacci recursion `(b,d) ↦ (d, b + a·d)` exactly (`readMap a = (0,1;1,a)`), so
  `fib k ≤ b` and `fib (k+1) ≤ d`.
* `minDen_mul_le_comp_d` — composing on the right can only *grow* the denominator, by at least
  `minDen`: `(s ∘ Q).d = s.c·Q.b + s.d·Q.d ≥ min(s.d, s.c+s.d)·Q.d`, using `0 ≤ Q.b ≤ Q.d`.
  This is the one place the `MapState` interval condition on the *inner* map is used, and it is
  what makes the bound sign-robust (`s.c` may be negative).

Combining with `runState_minDen_ge` (S7-NR: `minDen ≥ √(|det Φ|/6)` from step 2 on, uncondition-
ally) and `width_runState_bounds` (S7-HT: `width ≤ 6|det Φ|/d²`), the two occurrences of
`|det Φ|` cancel and the bound is absolute.

`runState_add_of_stall` (S7-RC) is what turns a stall into a single right composition; the whole
argument is three lines once that is in hand.
-/
import NormalNumbers.VandeheyS7Ledger
import NormalNumbers.VandeheyS7RunClock

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## The continuant lower bound -/

/-- **Reading `k` digits multiplies the denominator by at least `fib (k+1)`.** -/
theorem fib_le_cylMap : ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    (Nat.fib w.length : ℝ) ≤ (cylMap w).b ∧ (Nat.fib (w.length + 1) : ℝ) ≤ (cylMap w).d
  | [], _ => by
      constructor
      · simp [cylMap_nil, idMap]
      · simp [cylMap_nil, idMap]
  | a :: w, hpos => by
      have ha : 1 ≤ a := hpos a (by simp)
      have ha1 : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      obtain ⟨hb, hd⟩ := fib_le_cylMap w (fun e he => hpos e (by simp [he]))
      have hQd : (0:ℝ) < (cylMap w).d := (cylMap w).hd
      rw [cylMap_cons ha]
      constructor
      · show (Nat.fib (a :: w).length : ℝ) ≤ 0 * (cylMap w).b + 1 * (cylMap w).d
        simp only [List.length_cons]
        linarith
      · show (Nat.fib ((a :: w).length + 1) : ℝ)
            ≤ 1 * (cylMap w).b + ((a : ℕ) : ℝ) * (cylMap w).d
        simp only [List.length_cons]
        rw [show w.length + 1 + 1 = w.length + 2 from rfl, Nat.fib_add_two]
        push_cast
        nlinarith [hb, hd, hQd, ha1]

/-! ## Composition can only grow the denominator -/

/-- **Right composition grows the denominator by `minDen`.**  Sign-robust: `s.c` may be
negative, and then `0 ≤ Q.b ≤ Q.d` is what saves the bound. -/
theorem minDen_mul_le_comp_d (s Q : MapState) : s.minDen * Q.d ≤ (s.comp Q).d := by
  have hQb : 0 ≤ Q.b := Q.hb0
  have hQbd : Q.b ≤ Q.d := Q.hbd
  have hQd : (0:ℝ) < Q.d := Q.hd
  have h1 : s.minDen ≤ s.d := min_le_left _ _
  have h2 : s.minDen ≤ s.c + s.d := min_le_right _ _
  show s.minDen * Q.d ≤ s.c * Q.b + s.d * Q.d
  rcases le_or_gt 0 s.c with hc | hc
  · nlinarith
  · nlinarith

/-! ## The stall bound -/

/-- **A stall grows the denominator like a continuant.** -/
theorem d_stall_ge (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {n₀ : ℕ}
    (hstall : ∀ m, n₀ ≤ m → runWord Φ x m = []) (k : ℕ) :
    (runState Φ x n₀).minDen * (Nat.fib (k + 1) : ℝ) ≤ (runState Φ x (n₀ + k)).d := by
  have hxo : ∀ j, gaussMap^[j] (gaussMap^[n₀] x) ∈ Set.Ioo (0:ℝ) 1 := by
    intro j; rw [← Function.iterate_add_apply]; exact hx _
  have hpos : ∀ e ∈ digitWord (gaussMap^[n₀] x) k, 1 ≤ e := by
    intro e he
    simp only [digitWord, List.mem_map, List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact one_le_cfDigit hxo j
  have heq := runState_add_of_stall Φ hx hstall k
  obtain ⟨-, hfd⟩ := fib_le_cylMap (digitWord (gaussMap^[n₀] x) k) hpos
  rw [digitWord_length] at hfd
  have hmin : 0 < (runState Φ x n₀).minDen := minDen_pos _
  calc (runState Φ x n₀).minDen * (Nat.fib (k + 1) : ℝ)
      ≤ (runState Φ x n₀).minDen * (cylMap (digitWord (gaussMap^[n₀] x) k)).d :=
        mul_le_mul_of_nonneg_left hfd hmin.le
    _ ≤ ((runState Φ x n₀).comp (cylMap (digitWord (gaussMap^[n₀] x) k))).d :=
        minDen_mul_le_comp_d _ _
    _ = (runState Φ x (n₀ + k)).d := by rw [heq]

/-- **S7-SA, the headline.**  After stalling `k` steps from a time `≥ 2`, the width is at most
`36 / fib(k+1)²`.  No dependence on `Φ`, on `x`, or on normality: the two occurrences of
`|det Φ|` cancel. -/
theorem width_stall_le (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {j : ℕ}
    (hstall : ∀ m, j + 2 ≤ m → runWord Φ x m = []) (k : ℕ) :
    (runState Φ x (j + 2 + k)).width ≤ 36 / (Nat.fib (k + 1) : ℝ) ^ 2 := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hfibpos : (0:ℝ) < (Nat.fib (k + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hsq : Real.sqrt (|Φ.det| / 6) ^ 2 = |Φ.det| / 6 :=
    Real.sq_sqrt (by positivity)
  have hmin : Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (j + 2)).minDen :=
    runState_minDen_ge Φ x j
  have hlow := d_stall_ge Φ hx hstall k
  have hsqrtpos : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
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
      ≤ (runState Φ x (j + 2 + k)).d ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hdge
  have hexp : (Real.sqrt (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ)) ^ 2
      = (|Φ.det| / 6) * (Nat.fib (k + 1) : ℝ) ^ 2 := by
    rw [mul_pow, hsq]
  nlinarith [hd2, hexp, hdet, hfibpos]

/-- **The usable form.**  A state of width `≥ η` cannot have been stalling for long. -/
theorem stall_length_lt_of_width (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {j : ℕ}
    (hstall : ∀ m, j + 2 ≤ m → runWord Φ x m = []) {η : ℝ} (hη : 0 < η) {k : ℕ}
    (hw : η ≤ (runState Φ x (j + 2 + k)).width) :
    ((Nat.fib (k + 1) : ℝ)) ^ 2 ≤ 36 / η := by
  have h := width_stall_le Φ hx hstall k
  have hfibpos : (0:ℝ) < (Nat.fib (k + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hle : η ≤ 36 / (Nat.fib (k + 1) : ℝ) ^ 2 := le_trans hw h
  rw [le_div_iff₀ (by positivity)] at hle
  rw [le_div_iff₀ hη]
  linarith

end MapState

section Audit

#print axioms MapState.fib_le_cylMap
#print axioms MapState.minDen_mul_le_comp_d
#print axioms MapState.d_stall_ge
#print axioms MapState.width_stall_le
#print axioms MapState.stall_length_lt_of_width

end Audit

end NormalNumbers.VandeheyS7
