/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RR: the reference run IS the Gauss shift

The architecture of S7-BF replaces every run state by the fixed `refState` (the identity Möbius
map).  This module computes what that replacement leaves: **nothing**.  The identity state reads a
digit and immediately emits the same digit, returning to the identity, so

    pairStep (refState, z) = (refState, gaussMap z)

and the reference slot observable is the plain block indicator of `w`:

    slotObs w (pairStep^[j] (refState, z)) = blockIndic (cfCylinder w) (gaussMap^[j] z).

Hence `blockAvg refState T w z` is exactly the empirical frequency of the block `w` among the
first `T` continued-fraction digits of `z`.

## Why this matters for the crux

`BlockForgetGen` (S7-BG) compares an arbitrary width-`≥η` state `s` with the reference state at the
same input.  By the computation above, its `s' = refState` instance says

> the `w`-count emitted per input digit by the machine started at `s` agrees, to within `ε`, with
> the `w`-count per digit of the INPUT ITSELF.

That is the absolute statement — not a comparison — and it is precisely the assertion that the
transducer preserves block frequencies, i.e. the headline.  `blockForgetGen_absolute` below is
that consequence, machine-checked.  So the repaired crux is a **restatement** of the target rather
than a reduction of it: the refutation of the uniform-`z` form (S7-QD) was what forced the
CF-normality hypothesis back into the crux, and with it the circularity.

## Guard rule

**Content locator.**  Everything rests on `step_readMap`: the unique emission of `readMap a` is the
digit `a`.  Uniqueness is not an accident of `Classical.choose` — it is forced by `MapState`'s
endpoint inequalities (`hb0` kills `b > a`, `hbd` kills `b < a - 1`, `habcd` kills `b = a - 1`).

**Degenerate cases.** `w = []`: `cfCylinder [] = (0,1)`, the observable is constantly `1` and
`blockAvg refState T [] z = 1` — the clock rate of the identity state, correctly `1`.
`T = 0`: `blockAvg` is `0/0 = 0` on both sides.
-/
import NormalNumbers.VandeheyS7BlockForget

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## The identity state is a left unit -/

lemma refState_comp (t : MapState) : refState.comp t = t := by
  refine ext_entries ?_ ?_ ?_ ?_
  · show (1:ℝ) * t.a + 0 * t.c = t.a; ring
  · show (1:ℝ) * t.b + 0 * t.d = t.b; ring
  · show (0:ℝ) * t.a + 1 * t.c = t.c; ring
  · show (0:ℝ) * t.b + 1 * t.d = t.d; ring

/-! ## The unique emission of a read map -/

/-- Reading the digit `a` emits the digit `a` and returns to the identity.  The emission is
UNIQUE: the `MapState` endpoint inequalities leave no other factorisation. -/
theorem step_readMap {a : ℕ} (ha : 1 ≤ a) (ha' : (1:ℝ) ≤ (a:ℝ)) :
    step (readMap (a:ℝ) ha') = (refState, [a]) := by
  have hemit : EmitStep (readMap (a:ℝ) ha') a refState := by
    refine ⟨ha, ?_, ?_, ?_, ?_⟩
    · show (0:ℝ) = 0; rfl
    · show (1:ℝ) = 1; rfl
    · show (1:ℝ) = 1 + (a:ℝ) * 0; ring
    · show (a:ℝ) = 0 + (a:ℝ) * 1; ring
  have hE : Emittable (readMap (a:ℝ) ha') := ⟨a, refState, hemit⟩
  obtain ⟨b, hb, hb2⟩ := step_emitStep hE
  set u := (step (readMap (a:ℝ) ha')).1 with hu
  obtain ⟨hb1, huc, hud, hc, hd⟩ := hb
  -- `u.c = 0`, `u.d = 1` are read off the read map
  have huc0 : u.c = 0 := by rw [huc]; rfl
  have hud1 : u.d = 1 := by rw [hud]; rfl
  -- hence `u.a = 1` and `u.b = a - b`
  have hua : u.a = 1 := by
    have : (1:ℝ) = u.a + (b:ℝ) * u.c := hc
    rw [huc0] at this; linarith
  have hub : u.b = (a:ℝ) - (b:ℝ) := by
    have : (a:ℝ) = u.b + (b:ℝ) * u.d := hd
    rw [hud1] at this; linarith
  -- `hb0` and `hbd` trap `b` in `{a-1, a}`; `habcd` kills `a-1`
  have hle : (b:ℝ) ≤ (a:ℝ) := by have := u.hb0; rw [hub] at this; linarith
  have hge : (a:ℝ) - 1 ≤ (b:ℝ) := by have := u.hbd; rw [hub, hud1] at this; linarith
  have hnot : (b:ℝ) ≠ (a:ℝ) - 1 := by
    intro hcon
    have := u.habcd
    rw [hua, hub, huc0, hud1, hcon] at this
    norm_num at this
  have hba : b = a := by
    have hlt : (a:ℝ) - 1 < (b:ℝ) := lt_of_le_of_ne hge (Ne.symm hnot)
    have h1 : (b:ℝ) ≤ (a:ℝ) := hle
    have : (a:ℝ) = (b:ℝ) := by
      rcases lt_or_eq_of_le h1 with h | h
      · exfalso
        have hbn : b + 1 ≤ a := by exact_mod_cast (by exact_mod_cast h : (b:ℝ) < (a:ℝ))
        have : ((b:ℝ) + 1) ≤ (a:ℝ) := by exact_mod_cast hbn
        linarith
      · exact h.symm
    exact_mod_cast this.symm
  subst hba
  have hueq : u = refState := by
    refine ext_entries ?_ ?_ ?_ ?_
    · rw [hua]; rfl
    · rw [hub]; show (b:ℝ) - (b:ℝ) = 0; ring
    · rw [huc0]; rfl
    · rw [hud1]; rfl
  exact Prod.ext hueq hb2

/-! ## The reference run -/

/-- **The reference run is the Gauss shift.**  No hypothesis on `z`: `inDigit` is clamped. -/
theorem pairStep_refState (z : ℝ) : pairStep (refState, z) = (refState, gaussMap z) := by
  have hread : readAt z 0 = readMap ((inDigit z 0 : ℕ) : ℝ) (one_le_inDigit_real z 0) := rfl
  have hstep := step_readMap (one_le_inDigit z 0) (one_le_inDigit_real z 0)
  refine Prod.ext ?_ rfl
  show (step ((refState : MapState).comp (readAt z 0))).1 = refState
  rw [refState_comp, hread, hstep]

theorem pairWord_refState (z : ℝ) : pairWord (refState, z) = [inDigit z 0] := by
  show (step ((refState : MapState).comp (readAt z 0))).2 = _
  rw [refState_comp]
  exact congrArg Prod.snd (step_readMap (one_le_inDigit z 0) (one_le_inDigit_real z 0))

@[simp] theorem emitObs_refState (z : ℝ) : emitObs (refState, z) = 1 := by
  rw [emitObs, pairWord_refState]; simp

theorem pairStep_iterate_refState (j : ℕ) (z : ℝ) :
    pairStep^[j] (refState, z) = (refState, gaussMap^[j] z) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, pairStep_refState, Function.iterate_succ_apply']

/-! ## The reference observable is the block indicator -/

theorem mapBlockSet_refState (w : List ℕ) : mapBlockSet refState w 0 = cfCylinder w := by
  rw [mapBlockSet]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, refState_mob, Function.iterate_zero, id_eq]
  constructor
  · rintro ⟨⟨hw, -⟩, -⟩; exact hw
  · intro hw; exact ⟨⟨hw, cfCylinder_subset_Ioo w hw⟩, cfCylinder_subset_Ioo w hw⟩

/-- **The reference slot observable is the plain `w`-block indicator of the input.** -/
theorem slotObs_refState (w : List ℕ) (j : ℕ) (z : ℝ) :
    slotObs w (pairStep^[j] (refState, z)) = blockIndic (cfCylinder w) (gaussMap^[j] z) := by
  rw [pairStep_iterate_refState, slotObs, emitObs_refState, mapBlockSet_refState, one_mul]

/-- **The reference block average is the input's own empirical block frequency.** -/
theorem blockAvg_refState (T : ℕ) (w : List ℕ) (z : ℝ) :
    blockAvg refState T w z = (∑ j ∈ range T, blockIndic (cfCylinder w) (gaussMap^[j] z)) / T := by
  rw [blockAvg, blockSum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => slotObs_refState w j z

/-! ## The consequence for the crux -/

/-- **`BlockForgetGen` is the ABSOLUTE statement, not a comparison.**  Instantiating the crux at
the reference state turns it into: every width-`≥η` state's block average agrees with the input's
own empirical `w`-frequency.  There is no longer any "forgetting" content — the crux asserts
outright that the machine reproduces the input's digit-block statistics. -/
theorem blockForgetGen_absolute {w : List ℕ} (h : BlockForgetGen w) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, 0 < T ∧ ∀ s : MapState, η ≤ s.width → ∀ z ∈ Set.Ioo (0:ℝ) 1, IsCFNormal z →
      |blockAvg s T w z
        - (∑ j ∈ range T, blockIndic (cfCylinder w) (gaussMap^[j] z)) / T| ≤ ε := by
  obtain ⟨T, hT, hfor⟩ := h ε hε η hη
  refine ⟨T, hT, fun s hs z hz hzn => ?_⟩
  rw [← blockAvg_refState]
  exact hfor s refState hs (by rw [refState_width]; exact hη1) z hz hzn

end MapState

section Audit

#print axioms MapState.step_readMap
#print axioms MapState.pairStep_refState
#print axioms MapState.slotObs_refState
#print axioms MapState.blockAvg_refState
#print axioms MapState.blockForgetGen_absolute

end Audit

end NormalNumbers.VandeheyS7
