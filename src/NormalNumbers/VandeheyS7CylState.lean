/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CY: the cylinder state, and `R.d = cfK w` — the last analytic gap on the lag side closed

S7-E2 reduced the emission gain to `2 log R.d`, where `R` is the emitted block's cylinder map, and
flagged the one remaining gap: identifying `R.d` with the continuant `cfK w` of the emitted word.
This module closes it.

`cylState w` is the composition `readState a₁ ∘ ⋯ ∘ readState aₙ`, i.e. the map
`t ↦ [0; a₁, …, aₙ + t]`.  Its matrix is the convergent matrix, and the identification is the
classical one:

    (cylState w).d = cfK w       (the convergent denominator `qₙ`)
    (cylState w).b = cfNum w     (the convergent numerator `pₙ`)
    (cylState w).a = cfNum (w.drop 1),  (cylState w).c = cfK (w.drop 1)

proved as one simultaneous induction (`cylState_bd`), because the continuant recursion
`cfK (a::b::l) = a·cfK (b::l) + cfK l` is exactly the `comp` recursion
`d (a::w) = a·d w + b w` together with `b (a::w) = d w`.  The repo's `cfNum` convention
(`cfNum [] = 0`, `cfNum (_::l) = cfK l`) is the one that makes this come out right — `cfP [] = 1`
would not.

Consequences, both immediate:

* `cylState_det` — `|det| = 1`, so `deficit_comp_ge`'s unimodularity hypothesis is discharged.
* `deficit_comp_cylState_ge` — **the emission gain with no free parameters**:
  emitting the word `w` buys `2 log (cfK w)` of lag.
* `deficit_comp_cylState_fib_ge` — and `cfK w ≥ fib (|w|+1)` turns that into `2 log fib(L+1)`,
  matching lap 74's `fib_sq_mul_width_le_of_forced` exactly.

**With this, `deficit_telescope_le`'s `hstep` is discharged into kernel theorems end to end**, for
the read (S7-RC) and the emission (S7-E2 + here) alike, with no remaining analytic gap on the
lag/clock side of the §7 front.
-/
import NormalNumbers.VandeheyS7Emit2
import NormalNumbers.VandeheyS7Dioph

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- The cylinder map of a digit word: `t ↦ [0; a₁, …, aₙ + t]`. -/
noncomputable def cylState : List ℕ → MobState
  | [] => idState
  | a :: w =>
      if ha : 0 < a then (readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w)
      else idState

@[simp] lemma cylState_nil : cylState [] = idState := rfl

lemma cylState_cons {a : ℕ} (ha : 0 < a) (w : List ℕ) :
    cylState (a :: w) = (readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w) := by
  rw [cylState]
  exact dif_pos ha

/-- **The convergent identification**, as a simultaneous induction. -/
theorem cylState_bd : ∀ w : List ℕ, (∀ a ∈ w, 1 ≤ a) →
    (cylState w).d = (cfK w : ℝ) ∧ (cylState w).b = (cfNum w : ℝ)
  | [], _ => by refine ⟨?_, ?_⟩ <;> simp [idState, cfK, cfNum]
  | a :: w, hpos => by
      have ha : 0 < a := hpos a (by simp)
      obtain ⟨hd, hb⟩ := cylState_bd w (fun e he => hpos e (by simp [he]))
      have hcons := cylState_cons ha w
      refine ⟨?_, ?_⟩
      · -- `d (a :: w) = a · d w + b w`, and that is the continuant recursion
        rw [hcons]
        show (readState (a : ℝ) _).c * (cylState w).b + (readState (a : ℝ) _).d * (cylState w).d
          = (cfK (a :: w) : ℝ)
        show (1:ℝ) * (cylState w).b + (a : ℝ) * (cylState w).d = (cfK (a :: w) : ℝ)
        rw [hb, hd]
        cases w with
        | nil => simp [cfK]
        | cons b l =>
            show (1:ℝ) * (cfNum (b :: l) : ℝ) + (a : ℝ) * (cfK (b :: l) : ℝ) = _
            show (1:ℝ) * (cfK l : ℝ) + (a : ℝ) * (cfK (b :: l) : ℝ) = (cfK (a :: b :: l) : ℝ)
            rw [show cfK (a :: b :: l) = a * cfK (b :: l) + cfK l from rfl]
            push_cast; ring
      · -- `b (a :: w) = d w`, and `cfNum (a :: w) = cfK w`
        rw [hcons]
        show (readState (a : ℝ) _).a * (cylState w).b + (readState (a : ℝ) _).b * (cylState w).d
          = (cfNum (a :: w) : ℝ)
        show (0:ℝ) * (cylState w).b + (1:ℝ) * (cylState w).d = (cfNum (a :: w) : ℝ)
        rw [hd, show cfNum (a :: w) = cfK w from rfl]
        ring

lemma cylState_d {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    (cylState w).d = (cfK w : ℝ) := (cylState_bd w hpos).1

lemma cylState_b {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    (cylState w).b = (cfNum w : ℝ) := (cylState_bd w hpos).2

/-- The cylinder map is unimodular: each `readState` has determinant `−1`, and `comp` multiplies
determinants. -/
theorem cylState_det : ∀ w : List ℕ, (∀ a ∈ w, 1 ≤ a) →
    |(cylState w).a * (cylState w).d - (cylState w).b * (cylState w).c| = 1
  | [], _ => by norm_num [idState]
  | a :: w, hpos => by
      have ha : 0 < a := hpos a (by simp)
      have hw := cylState_det w (fun e he => hpos e (by simp [he]))
      rw [cylState_cons ha w]
      have hid : ((readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w)).a
            * ((readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w)).d
          - ((readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w)).b
            * ((readState (a : ℝ) (by exact_mod_cast ha)).comp (cylState w)).c
          = ((readState (a : ℝ) (by exact_mod_cast ha)).a
              * (readState (a : ℝ) (by exact_mod_cast ha)).d
            - (readState (a : ℝ) (by exact_mod_cast ha)).b
              * (readState (a : ℝ) (by exact_mod_cast ha)).c)
            * ((cylState w).a * (cylState w).d - (cylState w).b * (cylState w).c) := by
        simp only [comp_a, comp_b, comp_c, comp_d]; ring
      rw [hid, abs_mul, hw, mul_one]
      show |(0:ℝ) * (a : ℝ) - 1 * 1| = 1
      norm_num

/-- **The emission gain, with no free parameters.**  Emitting the word `w` buys `2 log (cfK w)` of
lag: `deficit (pre) ≥ deficit (post) + 2 log (cfK w)`. -/
theorem deficit_comp_cylState_ge (t : MobState) {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    t.deficit + 2 * Real.log (cfK w) ≤ ((cylState w).comp t).deficit := by
  have hK : 1 ≤ cfK w := one_le_cfK w hpos
  have hKR : (0:ℝ) < (cfK w : ℝ) := by exact_mod_cast hK
  exact deficit_comp_ge (cylState w) t (cylState_det w hpos) hKR
    (le_of_eq (cylState_d hpos).symm)

/-- The `fib` form, matching lap 74's `fib_sq_mul_width_le_of_forced`. -/
theorem deficit_comp_cylState_fib_ge (t : MobState) {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a)
    (hfib : Nat.fib (w.length + 1) ≤ cfK w) :
    t.deficit + 2 * Real.log (Nat.fib (w.length + 1)) ≤ ((cylState w).comp t).deficit := by
  have hK : 1 ≤ cfK w := one_le_cfK w hpos
  have hKR : (0:ℝ) < (cfK w : ℝ) := by exact_mod_cast hK
  refine le_trans ?_ (deficit_comp_cylState_ge t hpos)
  have hfR : (Nat.fib (w.length + 1) : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast hfib
  rcases Nat.eq_zero_or_pos (Nat.fib (w.length + 1)) with h0 | hp
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero]
    have : 0 ≤ Real.log (cfK w) := Real.log_nonneg (by exact_mod_cast hK)
    linarith
  · have hpR : (0:ℝ) < (Nat.fib (w.length + 1) : ℝ) := by exact_mod_cast hp
    have := Real.log_le_log hpR hfR
    linarith

section Audit

#print axioms MobState.cylState_bd
#print axioms MobState.cylState_det
#print axioms MobState.deficit_comp_cylState_ge
#print axioms MobState.deficit_comp_cylState_fib_ge

end Audit

end MobState

end NormalNumbers.VandeheyS7
