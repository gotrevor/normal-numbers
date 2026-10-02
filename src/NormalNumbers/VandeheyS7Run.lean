/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RN: the transducer run, defined

Everything needed to *run* the machine is now in the kernel: `MapState` is closed under composition
(S7-MS), emission is available whenever the image lies in a cylinder (S7-MS), and the state cannot
stay un-emittable (S7-EA/S7-CR2).  This module builds the run.

The schedule is the simple one — **at most one emitted digit per input digit**.  Maximal emission
would need an inner loop with a width-based termination measure; the one-digit schedule needs only
recursion on the input time, and S7-C3 already removed `StrictMono` from the clock, so stalling
steps are legal.

* `EmitStep t b u` — the emission relation written entrywise, so it carries no proof arguments and
  can be chosen from.  `emitStep_iff` identifies it with `readMap b ∘ u = t`.
* `runState Φ x n` / `runWord Φ x n` — the state after `n` input digits and the word emitted at
  step `n`; `runState_succ` is the transducer step, in exactly the shape `StatePin.step` wants.
* `runWord_length_le_one`, `runState_of_no_emit` — the two facts the clock analysis needs: a step
  emits at most one digit, and a stalling step composes a read on the right.
-/
import NormalNumbers.VandeheyS7CFRun

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

/-- The emission relation, entrywise: `t = readMap b ∘ u`. -/
def EmitStep (t : MapState) (b : ℕ) (u : MapState) : Prop :=
  1 ≤ b ∧ u.c = t.a ∧ u.d = t.b ∧ t.c = u.a + (b : ℝ) * u.c ∧ t.d = u.b + (b : ℝ) * u.d

theorem emitStep_iff {t : MapState} {b : ℕ} {u : MapState} (hb : 1 ≤ b) :
    EmitStep t b u ↔ (readMap (b : ℝ) (by exact_mod_cast hb)).comp u = t := by
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    refine ext_entries ?_ ?_ ?_ ?_
    · show (0:ℝ) * u.a + 1 * u.c = t.a; rw [← h1]; ring
    · show (0:ℝ) * u.b + 1 * u.d = t.b; rw [← h2]; ring
    · show (1:ℝ) * u.a + (b : ℝ) * u.c = t.c; rw [h3]; ring
    · show (1:ℝ) * u.b + (b : ℝ) * u.d = t.d; rw [h4]; ring
  · intro h
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · have := congrArg MapState.a h
      simp only [comp_a] at this
      show u.c = t.a
      rw [← this]; show u.c = 0 * u.a + 1 * u.c; ring
    · have := congrArg MapState.b h
      simp only [comp_b] at this
      show u.d = t.b
      rw [← this]; show u.d = 0 * u.b + 1 * u.d; ring
    · have := congrArg MapState.c h
      simp only [comp_c] at this
      show t.c = u.a + (b : ℝ) * u.c
      rw [← this]; show (1:ℝ) * u.a + (b:ℝ) * u.c = u.a + (b:ℝ) * u.c; ring
    · have := congrArg MapState.d h
      simp only [comp_d] at this
      show t.d = u.b + (b : ℝ) * u.d
      rw [← this]; show (1:ℝ) * u.b + (b:ℝ) * u.d = u.b + (b:ℝ) * u.d; ring

/-- Can this state emit a digit? -/
def Emittable (t : MapState) : Prop := ∃ b : ℕ, ∃ u : MapState, EmitStep t b u

open Classical in
/-- One transducer step: read, then emit one digit if possible. -/
noncomputable def step (t : MapState) : MapState × List ℕ :=
  if h : Emittable t then (h.choose_spec.choose, [h.choose]) else (t, [])

lemma step_of_not_emittable {t : MapState} (h : ¬ Emittable t) : step t = (t, []) := by
  rw [step, dif_neg h]

lemma step_emitStep {t : MapState} (h : Emittable t) :
    ∃ b : ℕ, EmitStep t b (step t).1 ∧ (step t).2 = [b] := by
  refine ⟨h.choose, ?_, ?_⟩
  · rw [step, dif_pos h]
    exact h.choose_spec.choose_spec
  · rw [step, dif_pos h]

lemma step_snd_length_le (t : MapState) : ((step t).2).length ≤ 1 := by
  by_cases h : Emittable t
  · obtain ⟨b, -, hb⟩ := step_emitStep h
    rw [hb]; simp
  · rw [step_of_not_emittable h]; simp

/-! ## The run -/

/-- The input digit, clamped to be genuine so the run is total. -/
noncomputable def inDigit (x : ℝ) (n : ℕ) : ℕ := max (cfDigit x n) 1

lemma one_le_inDigit (x : ℝ) (n : ℕ) : 1 ≤ inDigit x n := le_max_right _ _

lemma one_le_inDigit_real (x : ℝ) (n : ℕ) : (1:ℝ) ≤ ((inDigit x n : ℕ) : ℝ) := by
  exact_mod_cast one_le_inDigit x n

lemma inDigit_eq_cfDigit {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    inDigit x n = cfDigit x n := max_eq_left (one_le_cfDigit hx n)

/-- The read state at input time `n`. -/
noncomputable def readAt (x : ℝ) (n : ℕ) : MapState :=
  readMap ((inDigit x n : ℕ) : ℝ) (one_le_inDigit_real x n)

/-- The state of the machine after reading `n` input digits of `x`, starting from `Φ`. -/
noncomputable def runState (Φ : MapState) (x : ℝ) : ℕ → MapState
  | 0 => Φ
  | n + 1 =>
      step ((runState Φ x n).comp (readAt x n)) |>.1

/-- The word emitted while reading the `n`-th input digit. -/
noncomputable def runWord (Φ : MapState) (x : ℝ) (n : ℕ) : List ℕ :=
  step ((runState Φ x n).comp (readAt x n)) |>.2

lemma runWord_length_le_one (Φ : MapState) (x : ℝ) (n : ℕ) :
    (runWord Φ x n).length ≤ 1 := step_snd_length_le _


/-! ## S7-RN2: the step identity and the emission inverse -/

lemma idMap_comp (s : MapState) : idMap.comp s = s := by
  refine ext_entries ?_ ?_ ?_ ?_ <;> simp [comp_a, comp_b, comp_c, comp_d, idMap]

lemma comp_idMap (s : MapState) : s.comp idMap = s := by
  refine ext_entries ?_ ?_ ?_ ?_ <;> simp [comp_a, comp_b, comp_c, comp_d, idMap]

lemma cylMap_singleton {a : ℕ} (ha : 1 ≤ a) :
    cylMap [a] = readMap ((a : ℕ) : ℝ) (by exact_mod_cast ha) := by
  rw [cylMap_cons ha, cylMap_nil, comp_idMap]

/-- Reading a digit is inverted by one Gauss step. -/
lemma gaussMap_readMap_mob {a : ℕ} (ha : 1 ≤ a) {z : ℝ} (hz : z ∈ Set.Ioo (0:ℝ) 1) :
    gaussMap ((readMap ((a : ℕ) : ℝ) (by exact_mod_cast ha)).mob z) = z := by
  have ha1 : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
  have h1 : 0 < z + ((a : ℕ) : ℝ) := by linarith [hz.1]
  rw [readMap_mob]
  have hne : (1:ℝ) / (z + ((a : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [gaussMap, if_neg hne, one_div, inv_inv]
  have hcast : ((a : ℕ) : ℝ) = (((a : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hz.1.le, hz.2⟩]

lemma readMap_mapsTo_Ioo {a : ℕ} (ha : 1 ≤ a) :
    Set.MapsTo (readMap ((a : ℕ) : ℝ) (by exact_mod_cast ha)).mob
      (Set.Ioo (0:ℝ) 1) (Set.Ioo (0:ℝ) 1) := by
  have ha1 : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
  intro z hz
  rw [readMap_mob]
  have h1 : 0 < z + ((a : ℕ) : ℝ) := by linarith [hz.1]
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one h1]
  linarith [hz.1]

lemma cylMap_mapsTo_Ioo : ∀ (w : List ℕ), (∀ e ∈ w, 1 ≤ e) →
    Set.MapsTo (cylMap w).mob (Set.Ioo (0:ℝ) 1) (Set.Ioo (0:ℝ) 1)
  | [], _ => by intro z hz; simpa [cylMap_nil] using hz
  | a :: w, hpos => by
      have ha : 1 ≤ a := hpos a (by simp)
      have hw : ∀ e ∈ w, 1 ≤ e := fun e he => hpos e (by simp [he])
      intro z hz
      rw [cylMap_cons ha, mob_comp _ _ ⟨hz.1.le, hz.2.le⟩]
      exact readMap_mapsTo_Ioo ha (cylMap_mapsTo_Ioo w hw hz)

/-- **The tail identity for `MapState`.**  `|w|` Gauss steps strip `w` off `cylMap w`'s image. -/
theorem gaussMap_iterate_cylMap_mob : ∀ (w : List ℕ), (∀ e ∈ w, 1 ≤ e) → ∀ {z : ℝ},
    z ∈ Set.Ioo (0:ℝ) 1 → gaussMap^[w.length] ((cylMap w).mob z) = z
  | [], _, z, _ => by simp [cylMap_nil]
  | a :: w, hpos, z, hz => by
      have ha : 1 ≤ a := hpos a (by simp)
      have hw : ∀ e ∈ w, 1 ≤ e := fun e he => hpos e (by simp [he])
      have hmem : (cylMap w).mob z ∈ Set.Ioo (0:ℝ) 1 := cylMap_mapsTo_Ioo w hw hz
      rw [cylMap_cons ha, mob_comp _ _ ⟨hz.1.le, hz.2.le⟩, List.length_cons,
        Function.iterate_succ_apply, gaussMap_readMap_mob ha hmem]
      exact gaussMap_iterate_cylMap_mob w hw hz

/-! ## The step identity of the run -/

/-- **The transducer step.**  Exactly the shape `StatePin.step` asks for. -/
theorem runState_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    (cylMap (runWord Φ x n)).comp (runState Φ x (n + 1))
      = (runState Φ x n).comp (readAt x n) := by
  set t := (runState Φ x n).comp (readAt x n) with ht
  by_cases h : Emittable t
  · obtain ⟨b, hemit, hword⟩ := step_emitStep h
    have hb : 1 ≤ b := hemit.1
    have hrw : runWord Φ x n = [b] := hword
    have hst : runState Φ x (n + 1) = (step t).1 := rfl
    rw [hrw, hst, cylMap_singleton hb]
    exact (emitStep_iff hb).1 hemit
  · have hrw : runWord Φ x n = [] := by
      show (step t).2 = []
      rw [step_of_not_emittable h]
    have hst : runState Φ x (n + 1) = t := by
      show (step t).1 = t
      rw [step_of_not_emittable h]
    rw [hrw, hst, cylMap_nil, idMap_comp]

end MapState

section Audit2

#print axioms MapState.gaussMap_iterate_cylMap_mob
#print axioms MapState.runState_succ

end Audit2

section Audit

#print axioms MapState.emitStep_iff
#print axioms MapState.runWord_length_le_one

end Audit

end NormalNumbers.VandeheyS7
