/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyParity
import NormalNumbers.VandeheyRaneyReach
import NormalNumbers.VandeheyOutputFreq

set_option maxHeartbeats 1000000

/-!
# Transport: the joint law of the Raney transducer `lrDelta`

`VandeheyRaneyReach` proves a uniform common reach for the *phase-corrected* automaton
`rplusDelta`, and `VandeheyParity` proves `ClassEquidistribution` for the product of such an
automaton with a parity counter.  This file transports that back to the genuine Raney
transducer `lrDelta`, whose state set carries the deterministic period-2 phase
`det (M · B_j) = − det M`.

The bridge is the single identity

    `runState (lrDelta hD) M.toRState w = ι^{|w|} (runState (rplusDelta hD) M w).toRState`

(`runState_lrDelta_eq`, `ι = swapState`), together with the observation that the determinant
*pins the phase*: `ι` reverses the sign of the determinant, so a target `t : RState D` can only
be occupied at positions `i` of one parity, namely `(i : ZMod 2) = tPhase t`.  Hence

    `jointSet (lrDelta hD) s₀ t q x n = jointSet (prodStep (rplusDelta hD)) (s₀,0) (t⁺, p) q x n`

verbatim as finsets (`jointSet_lrDelta_eq`), and `JointStateFreq lrDelta s₀ ρ` follows.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyTwo

namespace VandeheyLR

variable {D : ℕ}

/-! ## The phase bookkeeping -/

lemma iterate_swapState (k : ℕ) (N : RState D) :
    (swapState)^[k] N = if (k : ZMod 2) = 0 then N else swapState N := by
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : ((k + 1 : ℕ) : ZMod 2) = (k : ZMod 2) + 1 := by push_cast; ring
    rcases h2 (k : ZMod 2) with h | h
    · rw [h, if_pos rfl, hc, h, if_neg (by decide : ¬((0 : ZMod 2) + 1 = 0))]
    · rw [h, if_neg (by decide : ¬((1 : ZMod 2) = 0)), swapState_swapState, hc, h,
        if_pos (by decide : ((1 : ZMod 2) + 1 = 0))]

/-- The phase-corrected run, transported by the involution. -/
lemma runState_lrDelta_swapState (hD : 0 < D) (N : RState D) (w : List ℕ) :
    runState (lrDelta hD) (swapState N) w = swapState (runState (lrDelta hD) N w) := by
  induction w generalizing N with
  | nil => simp
  | cons a w ih => rw [runState_cons, runState_cons, lrDelta_swapState, ih]

lemma lrDelta_eq_swapState_rplusDelta (hD : 0 < D) (M : RPlus D) (a : ℕ) :
    lrDelta hD M.toRState a = swapState (rplusDelta hD M a).toRState := by
  apply Subtype.ext
  show (lrDelta hD M.toRState a).val = Mat2.swapRows (Mat2.swapRows (lrDelta hD M.toRState a).val)
  rw [Mat2.swapRows_swapRows]

/-- **The bridge identity.**  Running the genuine Raney transducer is running the
phase-corrected one and then applying the involution once per digit. -/
theorem runState_lrDelta_eq (hD : 0 < D) (M : RPlus D) (w : List ℕ) :
    runState (lrDelta hD) M.toRState w
      = (swapState)^[w.length] (runState (rplusDelta hD) M w).toRState := by
  induction w generalizing M with
  | nil => simp
  | cons a w ih =>
    rw [runState_cons, lrDelta_eq_swapState_rplusDelta, runState_lrDelta_swapState,
      ih (rplusDelta hD M a)]
    rw [List.length_cons, runState_cons, Function.iterate_succ_apply']

/-- The phase of a Raney state: `0` if its determinant is `+D`, `1` if it is `−D`. -/
noncomputable def tPhase (t : RState D) : ZMod 2 := if t.val.det = (D : ℤ) then 0 else 1

/-- The phase-corrected representative of a Raney state: itself if its determinant is `+D`,
its row swap otherwise. -/
noncomputable def tPlus (t : RState D) : RPlus D :=
  ⟨if t.val.det = (D : ℤ) then t.val else Mat2.swapRows t.val, by
    split
    · next h => exact ⟨t.2, h⟩
    · next h =>
        refine ⟨Mat2.isRD_swapRows t.2, ?_⟩
        rw [Mat2.det_swapRows]
        rcases t.2.1 with h1 | h1
        · exact absurd h1 h
        · rw [h1]; ring⟩

lemma tPlus_val_of_pos {t : RState D} (h : t.val.det = (D : ℤ)) :
    (tPlus t).val = t.val := by
  show (if t.val.det = (D : ℤ) then t.val else Mat2.swapRows t.val) = t.val
  rw [if_pos h]

lemma tPlus_val_of_neg {t : RState D} (h : ¬ t.val.det = (D : ℤ)) :
    (tPlus t).val = Mat2.swapRows t.val := by
  show (if t.val.det = (D : ℤ) then t.val else Mat2.swapRows t.val) = Mat2.swapRows t.val
  rw [if_neg h]

/-- **The determinant pins the phase**: a state is occupied only at positions of one parity,
and there it determines its phase-corrected representative. -/
lemma runState_lrDelta_eq_iff (hD : 0 < D) (M : RPlus D) (w : List ℕ) (t : RState D) :
    runState (lrDelta hD) M.toRState w = t ↔
      (runState (rplusDelta hD) M w = tPlus t ∧ (w.length : ZMod 2) = tPhase t) := by
  have hD0 : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hne01 : (0 : ZMod 2) ≠ 1 := by decide
  rw [runState_lrDelta_eq, iterate_swapState]
  generalize hgen : runState (rplusDelta hD) M w = P
  have hPdet : P.val.det = (D : ℤ) := P.2.2
  by_cases hpar : ((w.length : ℕ) : ZMod 2) = 0
  · rw [if_pos hpar]
    constructor
    · rintro rfl
      have hdet : (P.toRState).val.det = (D : ℤ) := hPdet
      refine ⟨Subtype.ext ?_, ?_⟩
      · rw [tPlus_val_of_pos hdet]; rfl
      · rw [tPhase, if_pos hdet, hpar]
    · rintro ⟨h1, h2⟩
      have hdet : t.val.det = (D : ℤ) := by
        by_contra h
        rw [tPhase, if_neg h, hpar] at h2
        exact hne01 h2
      have hval : (tPlus t).val = P.val := by rw [← h1]
      rw [tPlus_val_of_pos hdet] at hval
      exact Subtype.ext hval.symm
  · rw [if_neg hpar]
    have hpar1 : ((w.length : ℕ) : ZMod 2) = 1 := by
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h2 ((w.length : ℕ) : ZMod 2) with h | h
      · exact absurd h hpar
      · exact h
    have hswapdet : ¬ (Mat2.swapRows P.val).det = (D : ℤ) := by
      rw [Mat2.det_swapRows, hPdet]
      omega
    have hsw : (swapState P.toRState).val = Mat2.swapRows P.val := rfl
    constructor
    · rintro rfl
      refine ⟨Subtype.ext ?_, ?_⟩
      · rw [tPlus_val_of_neg (by rw [hsw]; exact hswapdet), hsw, Mat2.swapRows_swapRows]
      · rw [tPhase, if_neg (by rw [hsw]; exact hswapdet), hpar1]
    · rintro ⟨h1, h2⟩
      have hdet : ¬ t.val.det = (D : ℤ) := by
        intro h
        rw [tPhase, if_pos h, hpar1] at h2
        exact hne01 h2.symm
      have hval : (tPlus t).val = P.val := by rw [← h1]
      rw [tPlus_val_of_neg hdet] at hval
      apply Subtype.ext
      rw [hsw, ← hval, Mat2.swapRows_swapRows]

/-! ## The joint count of `lrDelta` IS the joint count of the product automaton -/

lemma stateAt_lrDelta_eq_iff (hD : 0 < D) (s₀ : RPlus D) (x : ℝ) (i : ℕ) (t : RState D) :
    stateAt (lrDelta hD) s₀.toRState x i = t ↔
      stateAt (VandeheyPar.prodStep (rplusDelta hD)) (s₀, 0) x i = (tPlus t, tPhase t) := by
  rw [VandeheyPar.stateAt_prodStep, stateAt, Prod.ext_iff]
  simp only [zero_add]
  rw [stateAt, runState_lrDelta_eq_iff hD s₀ (cfWord x i) t, cfWord_length]

/-- **The transport identity.**  The positions at which the genuine Raney transducer is in
state `t` with window `q` are exactly the positions at which the phase-corrected automaton,
paired with a parity counter, is in state `(t⁺, p)`. -/
lemma jointSet_lrDelta_eq (hD : 0 < D) (s₀ : RPlus D) (t : RState D) (q : List ℕ) (x : ℝ)
    (n : ℕ) :
    jointSet (lrDelta hD) s₀.toRState t q x n
      = jointSet (VandeheyPar.prodStep (rplusDelta hD)) (s₀, 0) (tPlus t, tPhase t) q x n := by
  ext i
  simp only [mem_jointSet, stateAt_lrDelta_eq_iff hD]

lemma jointCount_lrDelta_eq (hD : 0 < D) (s₀ : RPlus D) (t : RState D) (q : List ℕ) (x : ℝ)
    (n : ℕ) :
    jointCount (lrDelta hD) s₀.toRState t q x n
      = jointCount (VandeheyPar.prodStep (rplusDelta hD)) (s₀, 0) (tPlus t, tPhase t) q x n :=
  congrArg Finset.card (jointSet_lrDelta_eq hD s₀ t q x n)

/-! ## The payoff: the joint law of the genuine Raney transducer -/

/-- **`ClassEquidistribution` for the genuine Raney transducer, through the product.** -/
theorem classEquidistribution_prodStep_rplusDelta (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (t : RState D) {q : List ℕ} (hq : q ≠ []) :
    VandeheyCocycle.ClassEquidistribution (VandeheyPar.prodStep (rplusDelta hD))
      (tPlus t, tPhase t) q :=
  VandeheyPar.classEquidistribution_prodStep_of_common_reach (rplusDelta hD) (tPlus t)
    (tPhase t) q (List.length_pos_iff.mpr hq) 2 le_rfl (rplus_common_reach D hD)

/-- **The joint (window, state) frequency of the Raney transducer of `x ↦ D·x` converges to an
`x`-independent limit**, from every phase-corrected initial state.  This is the crux input
`hjs` of `VandeheyOut.mobiusUniformFreq_of_transducer`. -/
theorem tendsto_jointCount_lrDelta (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (t : RState D) {q : List ℕ} (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : RPlus D) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (jointCount (lrDelta hD) s₀.toRState t q x n : ℝ) / n) atTop
        (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) := by
  obtain ⟨L, hL⟩ := VandeheyCocycle.tendsto_jointCount_of_classEquidistribution
    (classEquidistribution_prodStep_rplusDelta D hD t hq) hq hqpos
  refine ⟨L, fun s₀ x hx => ?_⟩
  have := hL (s₀, 0) x hx
  simpa only [jointCount_lrDelta_eq hD s₀ t q x] using this

open Classical in
/-- The joint law itself, extracted by choice. -/
noncomputable def rhoLR (hD : 0 < D) (s₀ : RPlus D) (q : List ℕ) (t : RState D) : ℝ :=
  if q = [] ∨ ¬ (∀ a ∈ q, 1 ≤ a) then 0
  else if h : ∃ r : ℝ, ∀ x : ℝ, IsCFNormal x →
      Tendsto (fun n => (jointCount (lrDelta hD) s₀.toRState t q x n : ℝ) / n) atTop (nhds r)
    then h.choose else 0

/-- **`JointStateFreq` for the Raney transducer** — the crux hypothesis of the capstone. -/
theorem jointStateFreq_lrDelta (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s₀ : RPlus D) :
    VandeheyOut.JointStateFreq (lrDelta hD) s₀.toRState (rhoLR hD s₀) := by
  classical
  intro t q hq hqpos x hx
  have hex : ∃ r : ℝ, ∀ y : ℝ, IsCFNormal y →
      Tendsto (fun n => (jointCount (lrDelta hD) s₀.toRState t q y n : ℝ) / n) atTop (nhds r) := by
    obtain ⟨L, hL⟩ := tendsto_jointCount_lrDelta D hD t hq hqpos
    exact ⟨L * (gaussMeasure (cfCylinder q)).toReal, fun y hy => hL s₀ y hy⟩
  have hval : rhoLR hD s₀ q t = hex.choose := by
    rw [rhoLR, if_neg (by push_neg; exact ⟨hq, hqpos⟩), dif_pos hex]
  rw [hval]
  exact hex.choose_spec x hx

/-- `SubWindow` is free for the transported law. -/
theorem subWindow_rhoLR (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s₀ : RPlus D) :
    VandeheyOut.SubWindow (rhoLR hD s₀) := by
  classical
  intro w t
  by_cases hgen : w = [] ∨ ¬ (∀ a ∈ w, 1 ≤ a)
  · have : rhoLR hD s₀ w t = 0 := by rw [rhoLR, if_pos hgen]
    rw [this]
    exact ⟨le_rfl, ENNReal.toReal_nonneg⟩
  · push_neg at hgen
    exact VandeheyOut.jointStateFreq_le_gauss (jointStateFreq_lrDelta D hD s₀) t w hgen.1 hgen.2

end VandeheyLR

end NormalNumbers

section
open NormalNumbers.VandeheyLR
#print axioms NormalNumbers.VandeheyLR.runState_lrDelta_eq
#print axioms NormalNumbers.VandeheyLR.runState_lrDelta_eq_iff
#print axioms NormalNumbers.VandeheyLR.jointSet_lrDelta_eq
#print axioms NormalNumbers.VandeheyLR.tendsto_jointCount_lrDelta
#print axioms NormalNumbers.VandeheyLR.jointStateFreq_lrDelta
#print axioms NormalNumbers.VandeheyLR.subWindow_rhoLR
end
