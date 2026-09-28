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

open MeasureTheory Filter VandeheyAut VandeheyTwo VandeheyOut

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

/-! ## The length-3 common reach -/

lemma runState_rplusB_fst (hD : 0 < D) (s : RPlus D × Bool) (w : List ℕ) :
    (runState (rplusB hD) s w).1 = runState (rplusDelta hD) s.1 w := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih => rw [runState_cons, runState_cons, ih]; rfl

lemma getLast?_replicate_true (m : ℕ) :
    (List.replicate (m + 1) true).getLast? = some true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.getLast?_cons_of_ne_nil (by simp [List.replicate_succ])]
    exact ih

lemma rplusB_zPlusState (hD : 0 < D) (b : Bool) :
    rplusB hD (zPlusState D hD, b) 1 = (zDiagState D hD, false) := by
  refine Prod.ext (rplusDelta_zPlusState hD 1) ?_
  show (!(((lrOut hD (zPlusState D hD).toRState 1).getLast?).getD b)) = false
  have h : (zPlusState D hD).toRState = ⟨zPlus D, isRD_zPlus hD⟩ := rfl
  rw [h, lrOut_zPlus hD 1]
  obtain ⟨m, hm⟩ : ∃ m, D * 1 = m + 1 := ⟨D - 1, by omega⟩
  rw [hm, getLast?_replicate_true m]
  rfl

/-- **The uniform common reach of the augmented automaton, at length exactly 3.**  Two digits
drive the matrix to `diag(1,D)` (`rplus_common_reach`); the third emits a nonempty block
(`lrOut_zPlus`), which overwrites the remembered letter — so the whole augmented state is
common. -/
theorem rplusB_common_reach (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s : RPlus D × Bool) :
    ∃ w : List ℕ, w.length = 3 ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState (rplusB hD) s w = (zDiagState D hD, false) := by
  obtain ⟨u, hulen, hupos, hureach⟩ := rplus_common_reach D hD s.1
  refine ⟨u ++ [1], by simp [hulen], ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hupos a h
    · simp only [List.mem_singleton] at h; omega
  · rw [runState_append]
    have hfst : (runState (rplusB hD) s u).1 = zPlusState D hD := by
      rw [runState_rplusB_fst, hureach]
    have : runState (rplusB hD) s u = (zPlusState D hD, (runState (rplusB hD) s u).2) := by
      rw [← hfst]
    rw [this]
    show rplusB hD (zPlusState D hD, _) 1 = _
    exact rplusB_zPlusState hD _

/-! ## The payoff: `JointStateFreq` for the run-clock automaton -/

lemma stateAt_lrB_eq_iff (hD : 0 < D) (s₀ : RPlus D × Bool) (x : ℝ) (i : ℕ)
    (t : RState D × Bool) :
    stateAt (lrB hD) (toRStateB s₀) x i = t ↔
      stateAt (VandeheyPar.prodStep (rplusB hD)) (s₀, 0) x i = (tPlusB t, tPhaseB t) := by
  rw [stateAt, runState_lrB_eq_iff hD s₀ (cfWord x i) t, cfWord_length,
    VandeheyPar.stateAt_prodStep, stateAt, Prod.mk.injEq]
  simp only [zero_add]
  rw [Prod.mk.injEq, ← Prod.ext_iff]

lemma jointCount_lrB_eq (hD : 0 < D) (s₀ : RPlus D × Bool) (t : RState D × Bool)
    (q : List ℕ) (x : ℝ) (n : ℕ) :
    jointCount (lrB hD) (toRStateB s₀) t q x n
      = jointCount (VandeheyPar.prodStep (rplusB hD)) (s₀, 0) (tPlusB t, tPhaseB t) q x n := by
  refine congrArg Finset.card ?_
  ext i
  simp only [mem_jointSet, stateAt_lrB_eq_iff hD]

/-- **The joint law of the run-clock automaton.** -/
theorem tendsto_jointCount_lrB (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (t : RState D × Bool) {q : List ℕ} (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : RPlus D × Bool) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (jointCount (lrB hD) (toRStateB s₀) t q x n : ℝ) / n) atTop
        (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) := by
  have hce : VandeheyCocycle.ClassEquidistribution (VandeheyPar.prodStep (rplusB hD))
      (tPlusB t, tPhaseB t) q :=
    VandeheyPar.classEquidistribution_prodStep_of_common_reach (rplusB hD) (tPlusB t)
      (tPhaseB t) q (List.length_pos_iff.mpr hq) 3 (by norm_num)
      (rplusB_common_reach D hD)
  obtain ⟨L, hL⟩ := VandeheyCocycle.tendsto_jointCount_of_classEquidistribution hce hq hqpos
  refine ⟨L, fun s₀ x hx => ?_⟩
  have := hL (s₀, 0) x hx
  simpa only [jointCount_lrB_eq hD s₀ t q x] using this

open Classical in
/-- The run-clock joint law, extracted by choice. -/
noncomputable def rhoLRB (hD : 0 < D) (s₀ : RPlus D × Bool) (q : List ℕ)
    (t : RState D × Bool) : ℝ :=
  if q = [] ∨ ¬ (∀ a ∈ q, 1 ≤ a) then 0
  else if h : ∃ r : ℝ, ∀ x : ℝ, IsCFNormal x →
      Tendsto (fun n => (jointCount (lrB hD) (toRStateB s₀) t q x n : ℝ) / n) atTop (nhds r)
    then h.choose else 0

/-- **`hjs` for the run clock.** -/
theorem jointStateFreq_lrB (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s₀ : RPlus D × Bool) :
    VandeheyOut.JointStateFreq (lrB hD) (toRStateB s₀) (rhoLRB hD s₀) := by
  classical
  intro t q hq hqpos x hx
  have hex : ∃ r : ℝ, ∀ y : ℝ, IsCFNormal y →
      Tendsto (fun n => (jointCount (lrB hD) (toRStateB s₀) t q y n : ℝ) / n) atTop (nhds r) := by
    obtain ⟨L, hL⟩ := tendsto_jointCount_lrB D hD t hq hqpos
    exact ⟨L * (gaussMeasure (cfCylinder q)).toReal, fun y hy => hL s₀ y hy⟩
  have hval : rhoLRB hD s₀ q t = hex.choose := by
    rw [rhoLRB, if_neg (by push_neg; exact ⟨hq, hqpos⟩), dif_pos hex]
  rw [hval]
  exact hex.choose_spec x hx

/-- `SubWindow` for the run-clock law. -/
theorem subWindow_rhoLRB (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s₀ : RPlus D × Bool) :
    VandeheyOut.SubWindow (rhoLRB hD s₀) := by
  classical
  intro w t
  by_cases hgen : w = [] ∨ ¬ (∀ a ∈ w, 1 ≤ a)
  · have h0 : rhoLRB hD s₀ w t = 0 := by rw [rhoLRB, if_pos hgen]
    rw [h0]
    exact ⟨le_rfl, ENNReal.toReal_nonneg⟩
  · push_neg at hgen
    exact VandeheyOut.jointStateFreq_le_gauss (jointStateFreq_lrB D hD s₀) t w hgen.1 hgen.2

/-! ## The run clock has an `x`-independent rate -/

/-- The alternation weight as a length-1 window function. -/
noncomputable def altWeight (hD : 0 < D) (t : RState D × Bool) (w : List ℕ) : ℝ :=
  (altOut hD t w.headI : ℝ)

lemma altWeight_nonneg (hD : 0 < D) (t : RState D × Bool) (w : List ℕ) :
    0 ≤ altWeight hD t w := by unfold altWeight; positivity

lemma altWeight_le (hD : 0 < D) (t : RState D × Bool) (w : List ℕ) :
    altWeight hD t w ≤ ((2 * D + 1 : ℕ) : ℝ) := by
  unfold altWeight
  exact_mod_cast altOut_le hD t w.headI

/-- **Vandehey's Lemma 6.1 for the TRUE clock.**  The number of runs emitted by the Raney
transducer — i.e. the number of CF digits of the image — has an `x`-independent Cesàro limit
along every CF-normal orbit.  The letter clock cannot have one (infinite digit mean); this one
does, and it is a corollary of `JointStateFreq` for `lrB` and nothing else. -/
theorem tendsto_numAlt_lrWord_div (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (s₀ : RPlus D × Bool) {x : ℝ} (hx : IsCFNormal x) :
    Tendsto (fun n => (numAlt (s₀.2 :: lrWord hD s₀.1.toRState x n) : ℝ) / n) atTop
      (nhds (∑ t : RState D × Bool,
        VandeheyOut.wLimit (rhoLRB hD s₀) t (altWeight hD t) 1)) := by
  have hsum : ∀ n : ℕ, (numAlt (s₀.2 :: lrWord hD s₀.1.toRState x n) : ℝ) / n
      = ∑ t : RState D × Bool,
          VandeheyOut.wCount (lrB hD) (toRStateB s₀) t (altWeight hD t) 1 x n / n := by
    intro n
    rw [← Finset.sum_div]
    congr 1
    have h := numAlt_lrWord_eq_sum hD s₀.1.toRState s₀.2 x n
    have h' : ((numAlt (s₀.2 :: lrWord hD s₀.1.toRState x n) : ℕ) : ℝ)
        = ∑ i ∈ Finset.range n,
            altWeight hD (stateAt (lrB hD) (toRStateB s₀) x i) [cfDigit x i] := by
      rw [h]
      push_cast
      rfl
    rw [h']
    exact VandeheyOut.sum_birkhoff_eq_sum_wCount (lrB hD) (toRStateB s₀)
      (fun t j => (altOut hD t j : ℝ)) x n
  refine Tendsto.congr (fun (n : ℕ) => (hsum n).symm) ?_
  refine tendsto_finsetSum _ fun t _ => ?_
  exact VandeheyOut.tendsto_wCount_div (lrB hD) (toRStateB s₀) (jointStateFreq_lrB D hD s₀) t
    (subWindow_rhoLRB D hD s₀) (C := ((2 * D + 1 : ℕ) : ℝ)) one_pos
    (altWeight_nonneg hD t) (altWeight_le hD t) hx

end VandeheyLR

end NormalNumbers

section
open NormalNumbers.VandeheyLR
#print axioms NormalNumbers.VandeheyLR.lrOut_zPlus
#print axioms NormalNumbers.VandeheyLR.lrB_swapStateB
#print axioms NormalNumbers.VandeheyLR.runState_lrB_eq
#print axioms NormalNumbers.VandeheyLR.runState_lrB_eq_iff
#print axioms NormalNumbers.VandeheyLR.rplusB_common_reach
#print axioms NormalNumbers.VandeheyLR.jointStateFreq_lrB
#print axioms NormalNumbers.VandeheyLR.subWindow_rhoLRB
#print axioms NormalNumbers.VandeheyLR.tendsto_numAlt_lrWord_div
end
