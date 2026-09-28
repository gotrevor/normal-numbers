/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyTransport
import NormalNumbers.VandeheyRunBirkhoff
import NormalNumbers.VandeheyOutLen

set_option maxHeartbeats 1000000

/-!
# The augmented automaton: `JointStateFreq` for the RUN clock

`VandeheyRunBirkhoff` shows the emitted run count — Vandehey's true `ℓ(n)` — is a Birkhoff sum
of `altOut` over the automaton `lrB` obtained from `lrDelta` by remembering the last emitted
letter.  This file repeats `VandeheyTransport` for `lrB`.

Two facts make the repeat cheap:

* the involution acts on the augmented state by `ι'(M, b) = (ι M, !b)`, because
  `lrOut (ι M) j = (lrOut M j).map not` (`lrOut_swapState`) — so the phase argument is verbatim;
* the Bool coordinate is a *function of the previous state and digit* whenever the emitted block
  is nonempty, and `lrOut ⟨diag(1,D)⟩ j = Lᴰʲ` is nonempty for `j ≥ 1`.  So the length-2 common
  reach of `VandeheyRaneyReach` becomes a length-3 common reach on `RPlus D × Bool`: two digits
  to `diag(1,D)`, then one more to pin the letter as well.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyTwo

namespace VandeheyLR

variable {D : ℕ}

/-- The emitted word of the common target: `D·j` copies of `L`. -/
theorem lrOut_zPlus (hD : 0 < D) (j : ℕ) :
    lrOut hD ⟨zPlus D, isRD_zPlus hD⟩ j = List.replicate (D * j) true := by
  have hfac : (zPlus D) * Mat2.B j
      = Mat2.lrProd (List.replicate (D * j) true) * zSpin D := by
    rw [Mat2.lrProd_replicate_true]
    refine Mat2.mat2_ext ?_ ?_ ?_ ?_ <;>
      simp only [Mat2.mul_def, Mat2.mul, Mat2.B, zPlus_a, zPlus_b, zPlus_c, zPlus_d,
        zSpin_a, zSpin_b, zSpin_c, zSpin_d] <;> push_cast <;> ring
  exact (lrStep_pin hD ⟨zPlus D, isRD_zPlus hD⟩ j (isRD_zSpin hD) hfac).1

/-! ## The augmented involution and the augmented phase-corrected automaton -/

/-- The involution on the augmented state set: swap the rows, flip the letter. -/
def swapStateB (s : RState D × Bool) : RState D × Bool := (swapState s.1, !s.2)

@[simp] lemma swapStateB_swapStateB (s : RState D × Bool) :
    swapStateB (swapStateB s) = s := by
  simp [swapStateB]

lemma getLast?_map_not (l : List Bool) (b : Bool) :
    ((l.map not).getLast?).getD (!b) = !((l.getLast?).getD b) := by
  rw [List.getLast?_map]
  cases l.getLast? <;> simp

/-- **The involution commutes with the augmented transducer.** -/
lemma lrB_swapStateB (hD : 0 < D) (s : RState D × Bool) (j : ℕ) :
    lrB hD (swapStateB s) j = swapStateB (lrB hD s j) := by
  rw [lrB, lrB, swapStateB, swapStateB]
  refine Prod.ext ?_ ?_
  · exact lrDelta_swapState hD s.1 j
  · show ((lrOut hD (swapState s.1) j).getLast?).getD (!s.2)
      = !(((lrOut hD s.1 j).getLast?).getD s.2)
    rw [lrOut_swapState hD s.1 j]
    exact getLast?_map_not _ _

/-- The augmented phase-corrected automaton. -/
noncomputable def rplusB (hD : 0 < D) (s : RPlus D × Bool) (j : ℕ) : RPlus D × Bool :=
  (rplusDelta hD s.1 j, !(((lrOut hD s.1.toRState j).getLast?).getD s.2))

/-- The augmented state underlying a phase-corrected one. -/
def toRStateB (s : RPlus D × Bool) : RState D × Bool := (s.1.toRState, s.2)

lemma lrB_eq_swapStateB_rplusB (hD : 0 < D) (s : RPlus D × Bool) (j : ℕ) :
    lrB hD (toRStateB s) j = swapStateB (toRStateB (rplusB hD s j)) := by
  refine Prod.ext ?_ ?_
  · exact lrDelta_eq_swapState_rplusDelta hD s.1 j
  · show ((lrOut hD s.1.toRState j).getLast?).getD s.2
      = !(!(((lrOut hD s.1.toRState j).getLast?).getD s.2))
    rw [Bool.not_not]

lemma runState_lrB_swapStateB (hD : 0 < D) (s : RState D × Bool) (w : List ℕ) :
    runState (lrB hD) (swapStateB s) w = swapStateB (runState (lrB hD) s w) := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih => rw [runState_cons, runState_cons, lrB_swapStateB, ih]

lemma iterate_swapStateB (k : ℕ) (s : RState D × Bool) :
    (swapStateB)^[k] s = if (k : ZMod 2) = 0 then s else swapStateB s := by
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : ((k + 1 : ℕ) : ZMod 2) = (k : ZMod 2) + 1 := by push_cast; ring
    rcases h2 (k : ZMod 2) with h | h
    · rw [h, if_pos rfl, hc, h, if_neg (by decide : ¬((0 : ZMod 2) + 1 = 0))]
    · rw [h, if_neg (by decide : ¬((1 : ZMod 2) = 0)), swapStateB_swapStateB, hc, h,
        if_pos (by decide : ((1 : ZMod 2) + 1 = 0))]

/-- **The augmented bridge identity.** -/
theorem runState_lrB_eq (hD : 0 < D) (s : RPlus D × Bool) (w : List ℕ) :
    runState (lrB hD) (toRStateB s) w
      = (swapStateB)^[w.length] (toRStateB (runState (rplusB hD) s w)) := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih =>
    rw [runState_cons, lrB_eq_swapStateB_rplusB, runState_lrB_swapStateB,
      ih (rplusB hD s a), List.length_cons, runState_cons, Function.iterate_succ_apply']

/-! ## The phase bookkeeping on the augmented state set -/

/-- The phase of an augmented state: that of its matrix part. -/
noncomputable def tPhaseB (t : RState D × Bool) : ZMod 2 := tPhase t.1

/-- The phase-corrected representative of an augmented state. -/
noncomputable def tPlusB (t : RState D × Bool) : RPlus D × Bool :=
  (tPlus t.1, if t.1.val.det = (D : ℤ) then t.2 else !t.2)

lemma runState_lrB_eq_iff (hD : 0 < D) (s : RPlus D × Bool) (w : List ℕ)
    (t : RState D × Bool) :
    runState (lrB hD) (toRStateB s) w = t ↔
      (runState (rplusB hD) s w = tPlusB t ∧ (w.length : ZMod 2) = tPhaseB t) := by
  have hne01 : (0 : ZMod 2) ≠ 1 := by decide
  rw [runState_lrB_eq, iterate_swapStateB]
  generalize hgen : runState (rplusB hD) s w = P
  have hPdet : P.1.val.det = (D : ℤ) := P.1.2.2
  by_cases hpar : ((w.length : ℕ) : ZMod 2) = 0
  · rw [if_pos hpar]
    constructor
    · rintro rfl
      have hdet : (P.1.toRState).val.det = (D : ℤ) := hPdet
      refine ⟨Prod.ext ?_ ?_, ?_⟩
      · show P.1 = tPlus (P.1.toRState)
        exact Subtype.ext (by rw [tPlus_val_of_pos hdet]; rfl)
      · show P.2 = if (P.1.toRState).val.det = (D : ℤ) then P.2 else !P.2
        rw [if_pos hdet]
      · show ((w.length : ℕ) : ZMod 2) = tPhase (P.1.toRState)
        rw [tPhase, if_pos hdet, hpar]
    · rintro ⟨h1, h2⟩
      have hdet : t.1.val.det = (D : ℤ) := by
        by_contra h
        rw [tPhaseB, tPhase, if_neg h, hpar] at h2
        exact hne01 h2
      have h1' : P.1 = tPlus t.1 := congrArg Prod.fst h1
      have h2' : P.2 = (if t.1.val.det = (D : ℤ) then t.2 else !t.2) := congrArg Prod.snd h1
      rw [if_pos hdet] at h2'
      have hval : (tPlus t.1).val = t.1.val := tPlus_val_of_pos hdet
      refine Prod.ext (Subtype.ext ?_) h2'
      show P.1.val = t.1.val
      rw [show P.1.val = (tPlus t.1).val from congrArg Subtype.val h1', hval]
  · rw [if_neg hpar]
    have hpar1 : ((w.length : ℕ) : ZMod 2) = 1 := by
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h2 ((w.length : ℕ) : ZMod 2) with h | h
      · exact absurd h hpar
      · exact h
    have hswapdet : ¬ (Mat2.swapRows P.1.val).det = (D : ℤ) := by
      rw [Mat2.det_swapRows, hPdet]
      have hD0 : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
      omega
    have hsw : (swapState (P.1.toRState)).val = Mat2.swapRows P.1.val := rfl
    constructor
    · rintro rfl
      refine ⟨Prod.ext ?_ ?_, ?_⟩
      · show P.1 = tPlus (swapState (P.1.toRState))
        refine Subtype.ext ?_
        rw [tPlus_val_of_neg (by rw [hsw]; exact hswapdet), hsw, Mat2.swapRows_swapRows]
      · show P.2 = if (swapState (P.1.toRState)).val.det = (D : ℤ) then !P.2 else !(!P.2)
        rw [if_neg (by rw [hsw]; exact hswapdet), Bool.not_not]
      · show ((w.length : ℕ) : ZMod 2) = tPhase (swapState (P.1.toRState))
        rw [tPhase, if_neg (by rw [hsw]; exact hswapdet), hpar1]
    · rintro ⟨h1, h2⟩
      have hdet : ¬ t.1.val.det = (D : ℤ) := by
        intro h
        rw [tPhaseB, tPhase, if_pos h, hpar1] at h2
        exact hne01 h2.symm
      have h1' : P.1 = tPlus t.1 := congrArg Prod.fst h1
      have h2' : P.2 = (if t.1.val.det = (D : ℤ) then t.2 else !t.2) := congrArg Prod.snd h1
      rw [if_neg hdet] at h2'
      refine Prod.ext ?_ ?_
      · show swapState (P.1.toRState) = t.1
        refine Subtype.ext ?_
        have hval : (tPlus t.1).val = Mat2.swapRows t.1.val := tPlus_val_of_neg hdet
        rw [hsw, show P.1.val = (tPlus t.1).val from congrArg Subtype.val h1', hval,
          Mat2.swapRows_swapRows]
      · show (!P.2) = t.2
        rw [h2', Bool.not_not]

end VandeheyLR

end NormalNumbers

section
open NormalNumbers.VandeheyLR
#print axioms NormalNumbers.VandeheyLR.lrOut_zPlus
#print axioms NormalNumbers.VandeheyLR.lrB_swapStateB
#print axioms NormalNumbers.VandeheyLR.runState_lrB_eq
#print axioms NormalNumbers.VandeheyLR.runState_lrB_eq_iff
end
