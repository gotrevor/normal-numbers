/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-BX: `BlockForget` in the uniform-`z` form, refuted IN THE KERNEL

Lap 89 argued the refutation of route A's crux on paper and froze it in the Maze on the S7-QD
witnesses, because the last step — from digit frequencies to `blockAvg` — is transducer
correctness, which is not claimed.  This module removes that gap by never going through digit
frequencies at all: it **computes the skew-product orbit** of the pair `(shiftState, √2 − 1)` and
finds it is a `2`-cycle.

* `emitStep_unique` — the emitted digit and the residual state are unique.  `MapState`'s four
  endpoint inequalities trap `b` in `[M − 1, M]` for `M = 1/mob 0` and also in `[M' − 1, M']` for
  `M' = 1/mob 1`, and `M = M'` forces `det = 0`; so the closed interval containing every legal `b`
  has length `< 1`.  This is what makes `step` (a `Classical.choose`) computable.
* `pairStep_shiftState` / `pairStep_midState` — the `2`-cycle
  `(shiftState, √2−1) → (midState, √2−1) → (shiftState, √2−1)`, with `midState : t ↦ 1/(2t+4)`.
* `blockAvg_shiftState_ge` — at every `T ≥ 1` the block average of `w = [1]` from `shiftState` is
  `⌈T/2⌉/T ≥ 1/2`, because the even phase's image is `2√2 − 2` (first digit `1`) and the odd
  phase's is `(√2−1)/2` (first digit `4`).
* `blockAvg_refState_sqrtTwoSub` — from the reference state it is `0`, because `√2 − 1` is a Gauss
  fixed point all of whose digits are `2` (S7-RR turns the reference run into the Gauss shift).
* `not_blockForget` — hence no `T` can make the two agree to `1/4` at the width floor `1/3`.

`BlockForgetGen` (S7-BG) survives: `√2 − 1` is not CF-normal.

## Guard rule

**Content locator.**  The whole refutation is the pair of matrix identities
`shiftState ∘ read 2 = (2,4;2,5) = read 1 ∘ midState` and
`midState ∘ read 2 = (1,2;4,10) = read 4 ∘ shiftState`.  Everything else is bookkeeping.

**Degenerate cases.** `T = 0`: both averages are `0/0 = 0` and the statement is vacuous, which is
why `not_blockForget` uses the `0 < T` that `BlockForget` itself supplies.
-/
import NormalNumbers.VandeheyS7RefRun
import NormalNumbers.VandeheyS7Quadratic

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## Emission is unique, so `step` is computable -/

theorem emitStep_unique {t : MapState} {b b' : ℕ} {u u' : MapState}
    (h : EmitStep t b u) (h' : EmitStep t b' u') : b = b' ∧ u = u' := by
  obtain ⟨hb1, huc, hud, hc, hd⟩ := h
  obtain ⟨hb1', huc', hud', hc', hd'⟩ := h'
  -- the entries of `u` in terms of `t` and `b`
  have hua : u.a = t.c - (b:ℝ) * t.a := by rw [huc] at hc; linarith
  have hub : u.b = t.d - (b:ℝ) * t.b := by rw [hud] at hd; linarith
  have hua' : u'.a = t.c - (b':ℝ) * t.a := by rw [huc'] at hc'; linarith
  have hub' : u'.b = t.d - (b':ℝ) * t.b := by rw [hud'] at hd'; linarith
  -- the four inequalities, on each side
  have k0 : 0 ≤ t.d - (b:ℝ) * t.b := by have := u.hb0; linarith [hub ▸ this]
  have k1 : t.d - (b:ℝ) * t.b ≤ t.b := by
    have := u.hbd; rw [hub, hud] at this; exact this
  have k2 : 0 ≤ (t.c - (b:ℝ) * t.a) + (t.d - (b:ℝ) * t.b) := by
    have := u.hab0; rw [hua, hub] at this; exact this
  have k3 : (t.c - (b:ℝ) * t.a) + (t.d - (b:ℝ) * t.b) ≤ t.a + t.b := by
    have := u.habcd; rw [hua, hub, huc, hud] at this; exact this
  have m0 : 0 ≤ t.d - (b':ℝ) * t.b := by have := u'.hb0; linarith [hub' ▸ this]
  have m1 : t.d - (b':ℝ) * t.b ≤ t.b := by
    have := u'.hbd; rw [hub', hud'] at this; exact this
  have m2 : 0 ≤ (t.c - (b':ℝ) * t.a) + (t.d - (b':ℝ) * t.b) := by
    have := u'.hab0; rw [hua', hub'] at this; exact this
  have m3 : (t.c - (b':ℝ) * t.a) + (t.d - (b':ℝ) * t.b) ≤ t.a + t.b := by
    have := u'.habcd; rw [hua', hub', huc', hud'] at this; exact this
  -- `t.b > 0` and `t.a + t.b > 0`
  have htb : 0 < t.b := by
    rcases lt_or_eq_of_le t.hb0 with h | h
    · exact h
    · exfalso
      have hb : t.b = 0 := h.symm
      rw [hb, mul_zero] at k1
      linarith [t.hd]
  have htab : 0 < t.a + t.b := by
    rcases lt_or_eq_of_le t.hab0 with h | h
    · exact h
    · exfalso
      have hb : t.a + t.b = 0 := h.symm
      have hz : t.a = -t.b := by linarith
      have : t.c + t.d ≤ 0 := by nlinarith [k3]
      linarith [t.hcd]
  have hbb : b = b' := by
    by_contra hne
    -- wlog `b + 1 ≤ b'`
    rcases Nat.lt_or_ge b b' with hlt | hge
    · have hstep : (b:ℝ) + 1 ≤ (b':ℝ) := by exact_mod_cast hlt
      have e1 : t.d = ((b:ℝ) + 1) * t.b := by nlinarith
      have e2 : t.c + t.d = ((b:ℝ) + 1) * (t.a + t.b) := by nlinarith
      have e3 : t.c = ((b:ℝ) + 1) * t.a := by linarith [e1, e2]
      exact t.hdet (by rw [e1, e3]; ring)
    · have hlt' : b' < b := lt_of_le_of_ne hge (Ne.symm hne)
      have hstep : (b':ℝ) + 1 ≤ (b:ℝ) := by exact_mod_cast hlt'
      have e1 : t.d = ((b':ℝ) + 1) * t.b := by nlinarith
      have e2 : t.c + t.d = ((b':ℝ) + 1) * (t.a + t.b) := by nlinarith
      have e3 : t.c = ((b':ℝ) + 1) * t.a := by linarith [e1, e2]
      exact t.hdet (by rw [e1, e3]; ring)
  refine ⟨hbb, ?_⟩
  subst hbb
  exact ext_entries (by rw [hua, hua']) (by rw [hub, hub']) (by rw [huc, huc']) (by rw [hud, hud'])

/-- **`step` computed.**  Exhibit one emission and the transducer step is pinned. -/
theorem step_eq_of_emitStep {t : MapState} {b : ℕ} {u : MapState} (h : EmitStep t b u) :
    step t = (u, [b]) := by
  have hE : Emittable t := ⟨b, u, h⟩
  obtain ⟨b', hb', hb2⟩ := step_emitStep hE
  obtain ⟨hbb, huu⟩ := emitStep_unique hb' h
  subst hbb
  exact Prod.ext huu hb2

/-! ## The two states of the cycle -/

/-- The odd phase of the cycle: `t ↦ 1/(2t+4)`. -/
noncomputable def midState : MapState where
  a := 0
  b := 1
  c := 2
  d := 4
  hd := by norm_num
  hcd := by norm_num
  hb0 := by norm_num
  hbd := by norm_num
  hab0 := by norm_num
  habcd := by norm_num
  hdet := by norm_num

@[simp] lemma midState_mob (z : ℝ) : midState.mob z = 1 / (2 * z + 4) := by
  show ((0:ℝ) * z + 1) / (2 * z + 4) = 1 / (2 * z + 4)
  ring_nf

lemma midState_mob_sqrtTwoSub : midState.mob sqrtTwoSub = halfSqrtTwoSub := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [midState_mob, sqrtTwoSub, halfSqrtTwoSub, div_eq_iff (by linarith)]
  nlinarith [sqrtTwo_sq]

/-! ## The read map at `√2 − 1` -/

lemma inDigit_sqrtTwoSub (n : ℕ) : inDigit sqrtTwoSub n = 2 := by
  rw [inDigit, cfDigit_sqrtTwoSub]
  norm_num

lemma readAt_sqrtTwoSub (n : ℕ) :
    readAt sqrtTwoSub n = readMap (2:ℝ) (by norm_num) := by
  have h : readAt sqrtTwoSub n = readMap ((inDigit sqrtTwoSub n : ℕ) : ℝ)
      (one_le_inDigit_real sqrtTwoSub n) := rfl
  rw [h]
  congr 1
  rw [inDigit_sqrtTwoSub]
  norm_num

/-! ## The 2-cycle -/

lemma comp_shiftState_read2 :
    shiftState.comp (readMap (2:ℝ) (by norm_num)) = (readMap (1:ℝ) (by norm_num)).comp midState :=
  ext_entries (by show (0:ℝ)*0 + 2*1 = 0*0 + 1*2; ring)
    (by show (0:ℝ)*1 + 2*2 = 0*1 + 1*4; ring)
    (by show (1:ℝ)*0 + 2*1 = 1*0 + 1*2; ring)
    (by show (1:ℝ)*1 + 2*2 = 1*1 + 1*4; ring)

lemma comp_midState_read2 :
    midState.comp (readMap (2:ℝ) (by norm_num)) = (readMap (4:ℝ) (by norm_num)).comp shiftState :=
  ext_entries (by show (0:ℝ)*0 + 1*1 = 0*0 + 1*1; ring)
    (by show (0:ℝ)*1 + 1*2 = 0*2 + 1*2; ring)
    (by show (2:ℝ)*0 + 4*1 = 1*0 + 4*1; ring)
    (by show (2:ℝ)*1 + 4*2 = 1*2 + 4*2; ring)

lemma step_shiftState_read2 :
    step (shiftState.comp (readMap (2:ℝ) (by norm_num))) = (midState, [1]) := by
  refine step_eq_of_emitStep (b := 1) (u := midState) ?_
  rw [emitStep_iff (by norm_num)]
  rw [comp_shiftState_read2]
  norm_num

lemma step_midState_read2 :
    step (midState.comp (readMap (2:ℝ) (by norm_num))) = (shiftState, [4]) := by
  refine step_eq_of_emitStep (b := 4) (u := shiftState) ?_
  rw [emitStep_iff (by norm_num)]
  rw [comp_midState_read2]
  norm_num

theorem pairStep_shiftState : pairStep (shiftState, sqrtTwoSub) = (midState, sqrtTwoSub) := by
  refine Prod.ext ?_ ?_
  · show (step (shiftState.comp (readAt sqrtTwoSub 0))).1 = midState
    rw [readAt_sqrtTwoSub, step_shiftState_read2]
  · show gaussMap sqrtTwoSub = sqrtTwoSub
    exact gaussMap_sqrtTwoSub

theorem pairStep_midState : pairStep (midState, sqrtTwoSub) = (shiftState, sqrtTwoSub) := by
  refine Prod.ext ?_ ?_
  · show (step (midState.comp (readAt sqrtTwoSub 0))).1 = shiftState
    rw [readAt_sqrtTwoSub, step_midState_read2]
  · show gaussMap sqrtTwoSub = sqrtTwoSub
    exact gaussMap_sqrtTwoSub

theorem pairStep_iterate_shiftState (k : ℕ) :
    pairStep^[2 * k] (shiftState, sqrtTwoSub) = (shiftState, sqrtTwoSub) := by
  induction k with
  | zero => simp
  | succ n ih =>
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h2, Function.iterate_succ_apply, Function.iterate_succ_apply, pairStep_shiftState,
        pairStep_midState, ih]

theorem pairStep_iterate_shiftState_odd (k : ℕ) :
    pairStep^[2 * k + 1] (shiftState, sqrtTwoSub) = (midState, sqrtTwoSub) := by
  rw [Function.iterate_succ_apply', pairStep_iterate_shiftState, pairStep_shiftState]

/-! ## The slot observable along the cycle -/

lemma emitObs_shiftState : emitObs (shiftState, sqrtTwoSub) = 1 := by
  rw [emitObs]
  show (((step (shiftState.comp (readAt sqrtTwoSub 0))).2).length : ℝ) = 1
  rw [readAt_sqrtTwoSub, step_shiftState_read2]
  simp

lemma mem_mapBlockSet_shiftState :
    sqrtTwoSub ∈ mapBlockSet shiftState [1] 0 := by
  refine ⟨⟨?_, ?_⟩, sqrtTwoSub_mem⟩
  · rw [Set.mem_preimage, Function.iterate_zero, id_eq, shiftState_mob_sqrtTwoSub]
    exact ⟨twoSqrtTwoSub_mem, fun i hi => by
      have : i = 0 := by simpa using hi
      subst this
      simpa using cfDigit_twoSqrtTwoSub_zero⟩
  · rw [shiftState_mob_sqrtTwoSub]; exact twoSqrtTwoSub_mem

lemma notMem_mapBlockSet_midState :
    sqrtTwoSub ∉ mapBlockSet midState [1] 0 := by
  rintro ⟨⟨hcyl, -⟩, -⟩
  rw [Set.mem_preimage, Function.iterate_zero, id_eq, midState_mob_sqrtTwoSub] at hcyl
  have := hcyl.2 0 (by simp)
  rw [cfDigit_halfSqrtTwoSub_zero] at this
  simp at this

lemma slotObs_even (k : ℕ) :
    slotObs [1] (pairStep^[2 * k] (shiftState, sqrtTwoSub)) = 1 := by
  rw [pairStep_iterate_shiftState, slotObs, emitObs_shiftState,
    blockIndic_eq_one' mem_mapBlockSet_shiftState, mul_one]

lemma slotObs_odd (k : ℕ) :
    slotObs [1] (pairStep^[2 * k + 1] (shiftState, sqrtTwoSub)) = 0 := by
  rw [pairStep_iterate_shiftState_odd, slotObs,
    blockIndic_eq_zero' notMem_mapBlockSet_midState, mul_zero]

/-! ## The two block averages -/

lemma blockSum_shiftState (T : ℕ) :
    blockSum shiftState T [1] sqrtTwoSub
      = (((range T).filter fun j => j % 2 = 0).card : ℝ) := by
  rw [blockSum]
  rw [← Finset.sum_filter_add_sum_filter_not (range T) (fun j => j % 2 = 0)]
  have h1 : ∑ j ∈ (range T).filter (fun j => j % 2 = 0),
      slotObs [1] (pairStep^[j] (shiftState, sqrtTwoSub))
      = ∑ _j ∈ (range T).filter (fun j => j % 2 = 0), (1:ℝ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj2 : j % 2 = 0 := (Finset.mem_filter.1 hj).2
    obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    rw [hk]; exact slotObs_even k
  have h2 : ∑ j ∈ (range T).filter (fun j => ¬ j % 2 = 0),
      slotObs [1] (pairStep^[j] (shiftState, sqrtTwoSub)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj2 : ¬ j % 2 = 0 := (Finset.mem_filter.1 hj).2
    obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    rw [hk]; exact slotObs_odd k
  rw [h1, h2, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma card_even_ge (T : ℕ) : 2 * ((range T).filter fun j => j % 2 = 0).card ≥ T := by
  induction T with
  | zero => simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : n % 2 = 0
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        omega
      · rw [if_neg h]
        have hn : n % 2 = 1 := by omega
        -- when `n` is odd the count is already `(n+1)/2`
        have : 2 * ((range n).filter fun j => j % 2 = 0).card ≠ n := by
          intro hc; omega
        omega

theorem blockAvg_shiftState_ge {T : ℕ} (hT : 0 < T) :
    (1:ℝ) / 2 ≤ blockAvg shiftState T [1] sqrtTwoSub := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  rw [blockAvg, blockSum_shiftState, le_div_iff₀ hTR]
  have := card_even_ge T
  have hc : (T:ℝ) ≤ 2 * (((range T).filter fun j => j % 2 = 0).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- From the reference state the average is `0`: every digit of `√2 − 1` is `2`. -/
theorem blockAvg_refState_sqrtTwoSub (T : ℕ) : blockAvg refState T [1] sqrtTwoSub = 0 := by
  rw [blockAvg_refState]
  have : ∀ j ∈ range T, blockIndic (cfCylinder [1]) (gaussMap^[j] sqrtTwoSub) = 0 := by
    intro j _
    refine blockIndic_eq_zero' ?_
    rw [gaussMap_iterate_sqrtTwoSub]
    rintro ⟨-, hd⟩
    have := hd 0 (by simp)
    rw [cfDigit_sqrtTwoSub] at this
    simp at this
  rw [Finset.sum_eq_zero this, zero_div]

/-! ## The refutation -/

/-- **`BlockForget [1]` is FALSE**, in the kernel.  At the width floor `1/3` no block length `T`
makes the two states agree to `1/4` at the single input point `√2 − 1`. -/
theorem not_blockForget : ¬ BlockForget [1] := by
  intro h
  obtain ⟨T, hT, hfor⟩ := h (1/4) (by norm_num) (1/3) (by norm_num)
  have hs : (1:ℝ)/3 ≤ shiftState.width := by rw [shiftState_width]
  have hs' : (1:ℝ)/3 ≤ refState.width := by rw [refState_width]; norm_num
  have := hfor shiftState refState hs hs' sqrtTwoSub sqrtTwoSub_mem
  rw [blockAvg_refState_sqrtTwoSub, sub_zero, abs_of_nonneg (blockAvg_nonneg _ _ _ _)] at this
  have hge := blockAvg_shiftState_ge hT
  linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.emitStep_unique
#print axioms NormalNumbers.VandeheyS7.MapState.step_eq_of_emitStep
#print axioms NormalNumbers.VandeheyS7.MapState.pairStep_shiftState
#print axioms NormalNumbers.VandeheyS7.MapState.blockAvg_shiftState_ge
#print axioms NormalNumbers.VandeheyS7.MapState.not_blockForget

end Audit
