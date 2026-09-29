/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-BY: `BlockForgetGen` is FALSE too — the repair does not survive

S7-BX refuted the uniform-`z` crux with the Gauss fixed point `√2 − 1`.  Lap 89's repair
(`BlockForgetGen`, S7-BG) restricted the input quantifier to CF-normal `z`, on the ground that a
quadratic irrational is never CF-normal.  That repair fails, and for a structural reason:

**the crux's quantifier order is `∃ T, ∀ z`**, so the block length is fixed before the input, and
`blockAvg s T [1] z` is decided by the state cycle alone once the first `T` digits of `z` are
known.  CF-normality is a TAIL property, so a CF-normal `z` may open with any prescribed prefix.

Concretely, along the all-`2` prefix the state cycle is the S7-BX cycle
`shiftState → midState → shiftState`, and the two phases' targets are decided uniformly in the
point:

* `shiftState.mob y = 2/(y+2) ∈ (2/3, 1)` for EVERY `y ∈ (0,1)` — always first digit `1`;
* `midState.mob y = 1/(2y+4) ∈ (1/6, 1/4)` for EVERY `y ∈ (0,1)` — never first digit `1`.

So `blockAvg shiftState T [1] z ≥ 1/2` while `blockAvg refState T [1] z = 0` (S7-RR: the
reference run is the Gauss shift, and `z` has no digit `1` in its first `T` places).  The witness
`z` exists because a genuine cylinder has positive Gauss mass and CF-normality is `γ`-a.e.
(`exists_isCFNormal_mem_cfCylinder`).

**Consequence for the programme.**  Route A's crux is dead in both forms.  What the pair of
refutations isolates is that `blockAvg` at a FIXED block length `T` is a finite-prefix functional
of the input, so no statement of the form "`∃T, ∀ s, ∀ z`" can hold: any such `T` is defeated by
prescribing `T` digits.  A surviving crux must let `T` depend on the input, i.e. it must be an
asymptotic statement in `T` — which is where the transducer-correctness bridge, and with it the
headline itself, re-enters.  See `DIRECTION.md`.

## Guard rule

**Content locator.**  The two `Ioo` image computations (`shiftState_mob_mem`, `midState_mob_mem`)
are the whole content: they make the slot observable a function of the STATE, not of the point.

**Degenerate cases.**  `T = 0` is excluded by `BlockForgetGen`'s own `0 < T`.  The prefix word is
`List.replicate T 2`, nonempty exactly when `T > 0`.
-/
import NormalNumbers.VandeheyS7BlockRefute
import NormalNumbers.CFAeNormal
import NormalNumbers.CFScheduleA

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## A CF-normal point in every genuine cylinder -/

/-- **CF-normal points are dense in the digit topology.**  Every genuine cylinder contains one:
the cylinder has positive Gauss mass and the non-CF-normal set is `γ`-null. -/
theorem exists_isCFNormal_mem_cfCylinder (v : List ℕ) (hv : v ≠ [])
    (hpos : ∀ a ∈ v, 1 ≤ a) : ∃ z : ℝ, z ∈ cfCylinder v ∧ IsCFNormal z := by
  have hAnull : gaussMeasure {y | ¬ IsCFNormal y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact ae_isCFNormal
  obtain ⟨W, hWsub, hWmeas, hW0⟩ := MeasureTheory.exists_measurable_superset_of_null hAnull
  by_contra hcon
  push_neg at hcon
  have hsub : cfCylinder v ⊆ W := by
    intro z hz
    exact hWsub (hcon z hz)
  have : gaussMeasure (cfCylinder v) = 0 :=
    le_antisymm (le_trans (measure_mono hsub) (le_of_eq hW0)) bot_le
  have hposγ := gaussMeasure_cfCylinder_toReal_pos v hv hpos
  rw [this] at hposγ
  simp at hposγ

/-! ## The two phases' images are decided uniformly in the point -/

lemma shiftState_mob_mem {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    shiftState.mob y ∈ Set.Ioo (1/2 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hy
  rw [shiftState_mob]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith

lemma midState_mob_mem {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    midState.mob y ∈ Set.Ioo (1/6 : ℝ) (1/4 : ℝ) := by
  obtain ⟨h0, h1⟩ := hy
  rw [midState_mob]
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith

/-- First digit `1` is exactly the upper half interval. -/
lemma cfDigit_zero_eq_one {y : ℝ} (hy : y ∈ Set.Ioo (1/2 : ℝ) 1) : cfDigit y 0 = 1 := by
  obtain ⟨h0, h1⟩ := hy
  have hy0 : (0:ℝ) < y := by linarith
  rw [cfDigit, Function.iterate_zero, id_eq]
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [Nat.cast_one, le_inv_comm₀ (by norm_num) hy0]; linarith
  · rw [Nat.cast_one, inv_lt_iff_one_lt_mul₀ hy0]; linarith

/-- First digit `4` (in particular not `1`) on the lower quarter. -/
lemma cfDigit_zero_eq_four {y : ℝ} (hy : y ∈ Set.Ioo (1/6 : ℝ) (1/4 : ℝ)) :
    cfDigit y 0 ≠ 1 := by
  obtain ⟨h0, h1⟩ := hy
  have hy0 : (0:ℝ) < y := by linarith
  have hinv : (4:ℝ) < y⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hy0]; linarith
  intro hcon
  rw [cfDigit, Function.iterate_zero, id_eq] at hcon
  have : (y⁻¹ : ℝ) < 2 := by
    have h2 := Nat.lt_floor_add_one (y⁻¹)
    rw [hcon] at h2
    norm_num at h2
    linarith
  linarith

/-! ## One step of the cycle, at any point whose digit is `2` -/

lemma readAt_of_digit_two {y : ℝ} (h : cfDigit y 0 = 2) :
    readAt y 0 = readMap (2:ℝ) (by norm_num) := by
  have hi : inDigit y 0 = 2 := by rw [inDigit, h]; norm_num
  have hr : readAt y 0 = readMap ((inDigit y 0 : ℕ) : ℝ) (one_le_inDigit_real y 0) := rfl
  rw [hr]; congr 1; rw [hi]; norm_num

theorem pairStep_shiftState_of_digit {y : ℝ} (h : cfDigit y 0 = 2) :
    pairStep (shiftState, y) = (midState, gaussMap y) := by
  refine Prod.ext ?_ rfl
  show (step (shiftState.comp (readAt y 0))).1 = midState
  rw [readAt_of_digit_two h, step_shiftState_read2]

theorem pairStep_midState_of_digit {y : ℝ} (h : cfDigit y 0 = 2) :
    pairStep (midState, y) = (shiftState, gaussMap y) := by
  refine Prod.ext ?_ rfl
  show (step (midState.comp (readAt y 0))).1 = shiftState
  rw [readAt_of_digit_two h, step_midState_read2]

/-! ## The run along an all-`2` prefix -/

/-- Along a prefix of `2`s the skew orbit is the S7-BX cycle, at the shifted point. -/
theorem pairStep_iterate_of_prefix {z : ℝ} {N : ℕ} (hz : ∀ i < N, cfDigit z i = 2) :
    ∀ j ≤ N, pairStep^[j] (shiftState, z)
      = (if j % 2 = 0 then shiftState else midState, gaussMap^[j] z) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ N := by omega
      have hdig : cfDigit (gaussMap^[k] z) 0 = 2 := by
        rw [cfDigit_iter_shift, Nat.add_zero]
        exact hz k (by omega)
      rw [Function.iterate_succ_apply', ih hk']
      by_cases hpar : k % 2 = 0
      · rw [if_pos hpar, pairStep_shiftState_of_digit hdig,
          if_neg (by omega : ¬ (k + 1) % 2 = 0), Function.iterate_succ_apply']
      · rw [if_neg hpar, pairStep_midState_of_digit hdig,
          if_pos (by omega : (k + 1) % 2 = 0), Function.iterate_succ_apply']

lemma emitObs_shiftState_of_digit {y : ℝ} (h : cfDigit y 0 = 2) :
    emitObs (shiftState, y) = 1 := by
  rw [emitObs]
  show (((step (shiftState.comp (readAt y 0))).2).length : ℝ) = 1
  rw [readAt_of_digit_two h, step_shiftState_read2]
  simp

lemma slotObs_shiftState_of {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) (h : cfDigit y 0 = 2) :
    slotObs [1] (shiftState, y) = 1 := by
  have hmem : y ∈ mapBlockSet shiftState [1] 0 := by
    refine ⟨⟨?_, ?_⟩, hy⟩
    · rw [Set.mem_preimage, Function.iterate_zero, id_eq]
      refine ⟨⟨by linarith [(shiftState_mob_mem hy).1], (shiftState_mob_mem hy).2⟩, fun i hi => ?_⟩
      have : i = 0 := by simpa using hi
      subst this
      simpa using cfDigit_zero_eq_one (shiftState_mob_mem hy)
    · exact ⟨by linarith [(shiftState_mob_mem hy).1], (shiftState_mob_mem hy).2⟩
  rw [slotObs, emitObs_shiftState_of_digit h, blockIndic_eq_one' hmem, mul_one]

lemma slotObs_midState_of {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    slotObs [1] (midState, y) = 0 := by
  have hnot : y ∉ mapBlockSet midState [1] 0 := by
    rintro ⟨⟨hcyl, -⟩, -⟩
    rw [Set.mem_preimage, Function.iterate_zero, id_eq] at hcyl
    have := hcyl.2 0 (by simp)
    simp only [List.getD_cons_zero] at this
    exact cfDigit_zero_eq_four (midState_mob_mem hy) this
  rw [slotObs, blockIndic_eq_zero' hnot, mul_zero]

/-! ## The two block averages along the prefix -/

theorem blockAvg_shiftState_prefix_ge {z : ℝ} {T : ℕ} (hT : 0 < T)
    (horb : ∀ k, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1) (hz : ∀ i < T, cfDigit z i = 2) :
    (1:ℝ) / 2 ≤ blockAvg shiftState T [1] z := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hsum : blockSum shiftState T [1] z
      = (((range T).filter fun j => j % 2 = 0).card : ℝ) := by
    rw [blockSum, ← Finset.sum_filter_add_sum_filter_not (range T) (fun j => j % 2 = 0)]
    have h1 : ∑ j ∈ (range T).filter (fun j => j % 2 = 0),
        slotObs [1] (pairStep^[j] (shiftState, z))
        = ∑ _j ∈ (range T).filter (fun j => j % 2 = 0), (1:ℝ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hjr, hj2⟩ := Finset.mem_filter.1 hj
      have hjT : j ≤ T := le_of_lt (Finset.mem_range.1 hjr)
      rw [pairStep_iterate_of_prefix hz j hjT, if_pos hj2]
      refine slotObs_shiftState_of (horb j) ?_
      rw [cfDigit_iter_shift, Nat.add_zero]
      exact hz j (Finset.mem_range.1 hjr)
    have h2 : ∑ j ∈ (range T).filter (fun j => ¬ j % 2 = 0),
        slotObs [1] (pairStep^[j] (shiftState, z)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hjr, hj2⟩ := Finset.mem_filter.1 hj
      have hjT : j ≤ T := le_of_lt (Finset.mem_range.1 hjr)
      rw [pairStep_iterate_of_prefix hz j hjT, if_neg hj2]
      exact slotObs_midState_of (horb j)
    rw [h1, h2, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [blockAvg, hsum, le_div_iff₀ hTR]
  have hc : (T:ℝ) ≤ 2 * (((range T).filter fun j => j % 2 = 0).card : ℝ) := by
    exact_mod_cast card_even_ge T
  linarith

theorem blockAvg_refState_prefix {z : ℝ} {T : ℕ} (hz : ∀ i < T, cfDigit z i = 2) :
    blockAvg refState T [1] z = 0 := by
  rw [blockAvg_refState]
  have : ∀ j ∈ range T, blockIndic (cfCylinder [1]) (gaussMap^[j] z) = 0 := by
    intro j hj
    refine blockIndic_eq_zero' ?_
    rintro ⟨-, hd⟩
    have h1 := hd 0 (by simp)
    rw [cfDigit_iter_shift, Nat.add_zero, hz j (Finset.mem_range.1 hj)] at h1
    simp at h1
  rw [Finset.sum_eq_zero this, zero_div]

/-! ## The refutation -/

/-- **`BlockForgetGen [1]` is FALSE.**  The CF-normality repair of lap 89 does not save the crux:
the block length is chosen before the input, and a CF-normal input may open with `T` copies of the
digit `2`. -/
theorem not_blockForgetGen : ¬ BlockForgetGen [1] := by
  intro h
  obtain ⟨T, hT, hfor⟩ := h (1/4) (by norm_num) (1/3) (by norm_num)
  -- a CF-normal input whose first `T` digits are all `2`
  obtain ⟨z, hzc, hzn⟩ := exists_isCFNormal_mem_cfCylinder (List.replicate T 2)
    (by simp [List.replicate_eq_nil_iff]; omega) (by simp)
  have hz01 : z ∈ Set.Ioo (0:ℝ) 1 := hzc.1
  have hzirr : Irrational z := by
    by_contra hcon
    exact Literature.not_isCFNormal_of_not_irrational hcon hzn
  have horb : ∀ k, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1 := fun k =>
    (irrational_orbit z hzirr hz01 k).2
  have hdig : ∀ i < T, cfDigit z i = 2 := by
    intro i hi
    have := hzc.2 i (by simpa using hi)
    rw [List.getD_eq_getElem _ _ (by simpa using hi)] at this
    simpa using this
  have hs : (1:ℝ)/3 ≤ shiftState.width := by rw [shiftState_width]
  have hs' : (1:ℝ)/3 ≤ refState.width := by rw [refState_width]; norm_num
  have hgap := hfor shiftState refState hs hs' z hz01 hzn
  rw [blockAvg_refState_prefix hdig, sub_zero,
    abs_of_nonneg (blockAvg_nonneg _ _ _ _)] at hgap
  have hge := blockAvg_shiftState_prefix_ge hT horb hdig
  linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.exists_isCFNormal_mem_cfCylinder
#print axioms NormalNumbers.VandeheyS7.MapState.pairStep_iterate_of_prefix
#print axioms NormalNumbers.VandeheyS7.MapState.blockAvg_shiftState_prefix_ge
#print axioms NormalNumbers.VandeheyS7.MapState.not_blockForgetGen

end Audit
