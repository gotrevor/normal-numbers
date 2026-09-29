/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WS: the state after a word, as a function OF the word

S7-WC says the state after `L` steps depends on the input point only through its first `L` digits
(`pairIter_fst_congr`).  For the reference-state Cesàro input (`RefCesaro`, S7-BF) that is not
quite enough: the decomposition of `blockAvg refState T w` into events needs the state as an
explicit FUNCTION of the digit word, so that the coefficient of each cylinder is a closed term and
not "the state at some point of the cylinder" (which would need the cylinder to be nonempty).

    wordState s v = v.foldl digitStep s        the state after reading the word `v` from `s`
    digitEmit t a = #(the word emitted when `t` reads the digit `a`)

and the two determinacy facts

    (pairStep^[|v|] (s, z)).1 = wordState s v          when `z`'s first `|v|` digits spell `v`
    emitObs (t, z) = digitEmit t (cfDigit z 0)         always.

Both are exact and unconditional.  Together with S7-RT (the target is order-connected) and S7-RQ
(relative equidistribution) they turn the reference observable into a finite combination of events
whose frequencies CF-normality computes.

## Guard rule

**Content locator.**  `digitEmit` and `digitStep` both factor through `readDigit a = readMap (max a
1)`; the `max … 1` is not decoration — the run reads `inDigit`, i.e. a `0` digit (the junk value at
a rational) is read as a `1`, and the determinacy lemma would be false for a definition that read
the raw digit.  At `v = []` the statement is `s = s`.

**Degenerate cases.**  `v = []`: `wordState s [] = s`.  A word containing a `0`: allowed, and the
`max` makes it behave as a `1` — matching the run exactly.  A stalling state: `digitEmit t a = 0`
and the emitted word is empty, so the slot observable vanishes, as in S7-SK.
-/
import NormalNumbers.VandeheyS7RefTarget

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

/-- The reading state of a digit, with the run's `max … 1` convention (`inDigit`). -/
noncomputable def readDigit (a : ℕ) : MapState :=
  readMap ((max a 1 : ℕ) : ℝ) (by
    have : (1:ℕ) ≤ max a 1 := le_max_right _ _
    exact_mod_cast this)

lemma readAt_eq_readDigit (z : ℝ) : readAt z 0 = readDigit (cfDigit z 0) := by
  show readMap ((inDigit z 0 : ℕ) : ℝ) _ = readMap ((max (cfDigit z 0) 1 : ℕ) : ℝ) _
  rfl

/-- One step of the state machine on a digit. -/
noncomputable def digitStep (t : MapState) (a : ℕ) : MapState :=
  (step (t.comp (readDigit a))).1

/-- The number of digits emitted when the state `t` reads the digit `a` (`0` or `1`). -/
noncomputable def digitEmit (t : MapState) (a : ℕ) : ℝ :=
  (((step (t.comp (readDigit a))).2).length : ℝ)

/-- The state after reading the word `v`, as a function of the word. -/
noncomputable def wordState (s : MapState) (v : List ℕ) : MapState := v.foldl digitStep s

@[simp] lemma wordState_nil (s : MapState) : wordState s [] = s := rfl

lemma wordState_cons (s : MapState) (a : ℕ) (m : List ℕ) :
    wordState s (a :: m) = wordState (digitStep s a) m := rfl

/-- **The emission observable is a function of the state and the current digit.** -/
theorem emitObs_eq_digitEmit (t : MapState) (z : ℝ) :
    emitObs (t, z) = digitEmit t (cfDigit z 0) := by
  rw [emitObs, pairWord, digitEmit, readAt_eq_readDigit]

/-- **The state after `|v|` steps IS `wordState s v`**, for every point whose first `|v|` digits
spell `v`. -/
theorem pairIter_fst_eq_wordState : ∀ (v : List ℕ) (s : MapState) (z : ℝ),
    (∀ i < v.length, cfDigit z i = v.getD i 0) →
    (pairStep^[v.length] (s, z)).1 = wordState s v
  | [], s, z, _ => rfl
  | a :: m, s, z, h => by
      have h0 : cfDigit z 0 = a := by
        have := h 0 (by simp)
        simpa using this
      have hstep : (pairStep (s, z)).1 = digitStep s a := by
        show (step (s.comp (readAt z 0))).1 = digitStep s a
        rw [readAt_eq_readDigit, h0]
        rfl
      have htail : ∀ i < m.length, cfDigit (gaussMap z) i = m.getD i 0 := by
        intro i hi
        rw [cfDigit_gaussMap]
        have := h (i + 1) (by simp; omega)
        simpa using this
      have hlen : (a :: m).length = m.length + 1 := by simp
      rw [hlen, Function.iterate_succ_apply]
      show (pairStep^[m.length] ((pairStep (s, z)).1, gaussMap z)).1 = wordState s (a :: m)
      rw [hstep, wordState_cons]
      exact pairIter_fst_eq_wordState m (digitStep s a) (gaussMap z) htail

/-- The run's state, in the same terms. -/
theorem runState_eq_pairIter_fst (s : MapState) (z : ℝ) (j : ℕ) :
    runState s z j = (pairStep^[j] (s, z)).1 :=
  congrArg Prod.fst (runPair_eq_iterate s z j)

/-- **The slot observable, in closed form.**  For a point whose first `j` digits spell `v`, the
`j`-th slot observable of the run started at `s` is a constant times the indicator of an
order-connected target, pulled back `j` steps. -/
theorem slotObs_pairIter_eq (s : MapState) (w v : List ℕ) (z : ℝ)
    (h : ∀ i < v.length, cfDigit z i = v.getD i 0) :
    slotObs w (pairStep^[v.length] (s, z))
      = digitEmit (wordState s v) (cfDigit (gaussMap^[v.length] z) 0)
        * blockIndic (mapBlockSet (wordState s v) w 0) (gaussMap^[v.length] z) := by
  have hpair : pairStep^[v.length] (s, z) = (wordState s v, gaussMap^[v.length] z) := by
    have h2 : pairStep^[v.length] (s, z) = runPair s z v.length := (runPair_eq_iterate s z _).symm
    have hfst : (pairStep^[v.length] (s, z)).1 = wordState s v :=
      pairIter_fst_eq_wordState v s z h
    have hsnd : (pairStep^[v.length] (s, z)).2 = gaussMap^[v.length] z := by
      rw [h2]; rfl
    exact Prod.ext hfst hsnd
  rw [hpair, slotObs, emitObs_eq_digitEmit]

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.emitObs_eq_digitEmit
#print axioms NormalNumbers.VandeheyS7.MapState.pairIter_fst_eq_wordState
#print axioms NormalNumbers.VandeheyS7.MapState.slotObs_pairIter_eq

end Audit
