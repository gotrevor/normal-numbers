/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-GR: the GREEDY transducer — emit while you can, then read

The lap-91 probe (`experiments/PROBE-2026-09-29-lap91-stall-and-width-walk.md`, Finding 3) showed
that route A's width debts are artifacts of the repo's `step`, which emits **at most one** digit per
read (`runWord_length_le_one`).  Vandehey's transducer emits a variable-length word, and with
maximal emission the same exact simulation keeps `log (1/width)` inside `[0, 12]` over 8000 reads
(inside `[0, 3.4]` for the rational map), against `25 … 590` and rising for the throttled run.

This module builds the greedy emission in Lean.  The only real issue is **termination**, and the
width supplies it: if `n` iterations of `step` emit the word `u`, then `t` factors as
`cylMap u ∘ (state)`, so

    width t ≤ width (cylMap u) ≤ (1/4)^(|u|/2)                   (`width_le_of_emitAcc`)

by S7-CM's cylinder decay — a state of positive width cannot emit forever.  Hence

* `exists_not_emittable_iterate` — some iterate of `step` is non-emittable;
* `flushLen`/`flushState`/`flushWord` — the least such iterate, the state it leaves (REDUCED: it
  cannot emit), and the word emitted on the way;
* `factor_flushWord` — `cylMap (flushWord t) ∘ flushState t = t`, the transducer identity;
* `grunState`/`grunWord` — the greedy run of an input, reduced at every time
  (`not_emittable_grunState`), with the step identity `grunState_succ`.

`flushWord` is the Raney-normal-form output word of one read, which is what makes the greedy state
reduced and (by the probe) keeps its width bounded — the property `WidthAfford` and `MeanSlack`
were trying to assert and which the throttled run does not have (S7-WQ).

## Guard rule

**Content locator.**  `width_le_of_emitAcc` is the whole content: everything else is bookkeeping
around `Nat.find`.  The cylinder decay it uses is S7-CM's `width_cylMap_le`, and the containment
step is `abs_sub_le_width` (two points of `[0,1]` never spread further than the endpoints).

**Degenerate cases.**  A non-emittable `t` has `flushLen t = 0`, `flushWord t = []` and
`flushState t = t`.  `width t = 0` is impossible (`det ≠ 0`), and that is exactly what makes the
flush finite.
-/
import NormalNumbers.VandeheyS7Run
import NormalNumbers.VandeheyS7CylMap
import NormalNumbers.VandeheyS7Box

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

attribute [local instance] Classical.propDecidable

namespace MapState

/-! ## Iterating the emission -/

/-- The state after `n` emission attempts (no reading). -/
noncomputable def stepFst (t : MapState) : MapState := (step t).1

/-- The word emitted by `n` emission attempts. -/
noncomputable def emitAcc (t : MapState) : ℕ → List ℕ
  | 0 => []
  | n + 1 => emitAcc t n ++ (step (stepFst^[n] t)).2

/-- The raw transducer identity for one emission attempt. -/
theorem cylMap_step_comp (t : MapState) :
    (cylMap (step t).2).comp (stepFst t) = t := by
  by_cases h : Emittable t
  · obtain ⟨b, hemit, hword⟩ := step_emitStep h
    have hb : 1 ≤ b := hemit.1
    rw [hword, cylMap_singleton hb, stepFst]
    exact (emitStep_iff hb).1 hemit
  · rw [step_of_not_emittable h, stepFst, step_of_not_emittable h, cylMap_nil, idMap_comp]

lemma emitAcc_pos (t : MapState) (n : ℕ) : ∀ a ∈ emitAcc t n, 1 ≤ a := by
  induction n with
  | zero => intro a ha; simp [emitAcc] at ha
  | succ k ih =>
      intro a ha
      rw [emitAcc, List.mem_append] at ha
      rcases ha with ha | ha
      · exact ih a ha
      · by_cases h : Emittable (stepFst^[k] t)
        · obtain ⟨b, hemit, hword⟩ := step_emitStep h
          rw [hword] at ha
          have : a = b := by simpa using ha
          subst this
          exact hemit.1
        · rw [step_of_not_emittable h] at ha
          simp at ha

/-- **The factorisation.**  After `n` emission attempts the emitted word is split off on the
left. -/
theorem factor_emitAcc (t : MapState) (n : ℕ) :
    (cylMap (emitAcc t n)).comp (stepFst^[n] t) = t := by
  induction n with
  | zero => simp [emitAcc, cylMap_nil, idMap_comp]
  | succ k ih =>
      have hsplit : stepFst^[k + 1] t = stepFst (stepFst^[k] t) := by
        rw [Function.iterate_succ_apply']
      rw [emitAcc, cylMap_append _ _ (emitAcc_pos t k), hsplit, comp_assoc,
        cylMap_step_comp (stepFst^[k] t), ih]

/-! ## Termination: a state of positive width cannot emit forever -/

/-- **The burst bound.**  The width caps the emitted length. -/
theorem width_le_of_emitAcc (t : MapState) (n : ℕ) :
    t.width ≤ (1 / 4 : ℝ) ^ ((emitAcc t n).length / 2) := by
  have hfac := factor_emitAcc t n
  have hpos := emitAcc_pos t n
  have hcyl := width_cylMap_le (emitAcc t n) hpos
  refine le_trans ?_ hcyl
  -- the image of `t` lies inside the image of `cylMap (emitAcc t n)`
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hv0 := (stepFst^[n] t).mapsTo h0
  have hv1 := (stepFst^[n] t).mapsTo h1
  have e0 : (cylMap (emitAcc t n)).mob ((stepFst^[n] t).mob 0) = t.mob 0 := by
    rw [← mob_comp _ _ h0, hfac]
  have e1 : (cylMap (emitAcc t n)).mob ((stepFst^[n] t).mob 1) = t.mob 1 := by
    rw [← mob_comp _ _ h1, hfac]
  rw [width, ← e0, ← e1]
  exact abs_sub_le_width _ hv1 hv0

/-- Emitting forever is impossible. -/
theorem exists_not_emittable_iterate (t : MapState) :
    ∃ n : ℕ, ¬ Emittable (stepFst^[n] t) := by
  by_contra hcon
  push_neg at hcon
  -- every attempt emits, so the emitted length is `n`
  have hlen : ∀ n : ℕ, (emitAcc t n).length = n := by
    intro n
    induction n with
    | zero => simp [emitAcc]
    | succ k ih =>
        obtain ⟨b, -, hword⟩ := step_emitStep (hcon k)
        rw [emitAcc, List.length_append, hword, ih]
        simp
  have hw : 0 < t.width := width_pos t
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 4 : ℝ) ^ n < t.width := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num)
    exact ((h.eventually (eventually_lt_nhds hw)).exists)
  have hb := width_le_of_emitAcc t (2 * n + 1)
  rw [hlen] at hb
  have hidx : (2 * n + 1) / 2 = n := by omega
  rw [hidx] at hb
  linarith

/-- The number of emissions the flush performs. -/
noncomputable def flushLen (t : MapState) : ℕ :=
  Nat.find (exists_not_emittable_iterate t)

/-- The reduced state the flush leaves. -/
noncomputable def flushState (t : MapState) : MapState := stepFst^[flushLen t] t

/-- The word the flush emits. -/
noncomputable def flushWord (t : MapState) : List ℕ := emitAcc t (flushLen t)

theorem not_emittable_flushState (t : MapState) : ¬ Emittable (flushState t) :=
  Nat.find_spec (exists_not_emittable_iterate t)

theorem factor_flushWord (t : MapState) :
    (cylMap (flushWord t)).comp (flushState t) = t :=
  factor_emitAcc t (flushLen t)

theorem flushWord_pos (t : MapState) : ∀ a ∈ flushWord t, 1 ≤ a :=
  emitAcc_pos t (flushLen t)

/-- A non-emittable state is its own flush. -/
theorem flushLen_eq_zero {t : MapState} (h : ¬ Emittable t) : flushLen t = 0 :=
  Nat.eq_zero_of_le_zero (Nat.find_le (by simpa using h))

@[simp] theorem flushState_of_not_emittable {t : MapState} (h : ¬ Emittable t) :
    flushState t = t := by
  rw [flushState, flushLen_eq_zero h]
  simp

@[simp] theorem flushWord_of_not_emittable {t : MapState} (h : ¬ Emittable t) :
    flushWord t = [] := by
  rw [flushWord, flushLen_eq_zero h]
  simp [emitAcc]

/-- The flush's burst length is capped by the width. -/
theorem width_le_of_flushWord (t : MapState) :
    t.width ≤ (1 / 4 : ℝ) ^ ((flushWord t).length / 2) :=
  width_le_of_emitAcc t (flushLen t)

/-! ## The greedy run -/

/-- The greedy state after reading `n` input digits: flushed after every read (and at the
start). -/
noncomputable def grunState (Φ : MapState) (x : ℝ) : ℕ → MapState
  | 0 => flushState Φ
  | n + 1 => flushState ((grunState Φ x n).comp (readAt x n))

/-- The word the greedy run emits while reading the `n`-th input digit. -/
noncomputable def grunWord (Φ : MapState) (x : ℝ) (n : ℕ) : List ℕ :=
  flushWord ((grunState Φ x n).comp (readAt x n))

theorem not_emittable_grunState (Φ : MapState) (x : ℝ) (n : ℕ) :
    ¬ Emittable (grunState Φ x n) := by
  cases n with
  | zero => exact not_emittable_flushState Φ
  | succ k => exact not_emittable_flushState _

theorem grunWord_pos (Φ : MapState) (x : ℝ) (n : ℕ) : ∀ a ∈ grunWord Φ x n, 1 ≤ a :=
  flushWord_pos _

/-- **The greedy step identity.** -/
theorem grunState_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    (cylMap (grunWord Φ x n)).comp (grunState Φ x (n + 1))
      = (grunState Φ x n).comp (readAt x n) :=
  factor_flushWord _

/-- **The initial factorisation.** -/
theorem grunState_zero (Φ : MapState) (x : ℝ) :
    (cylMap (flushWord Φ)).comp (grunState Φ x 0) = Φ :=
  factor_flushWord Φ

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.factor_emitAcc
#print axioms NormalNumbers.VandeheyS7.MapState.width_le_of_emitAcc
#print axioms NormalNumbers.VandeheyS7.MapState.exists_not_emittable_iterate
#print axioms NormalNumbers.VandeheyS7.MapState.not_emittable_flushState
#print axioms NormalNumbers.VandeheyS7.MapState.factor_flushWord
#print axioms NormalNumbers.VandeheyS7.MapState.grunState_succ

end Audit
