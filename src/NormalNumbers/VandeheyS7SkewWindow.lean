/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WC: the window cocycle — state(n+L) = (state(n), the L digits in between), exactly

S7-SK exhibited the run as the orbit of one autonomous map `pairStep` on `MapState × ℝ`.  This
module extracts the consequence that reshapes the crux:

    runPair Φ x (n + L) = pairStep^[L] (runPair Φ x n)                  (`runPair_add`)
    (pairStep^[L] (s, t)).1 depends on `t` only through `cfDigit t 0 … cfDigit t (L−1)`
                                                                       (`pairIter_fst_congr`)

So the state at time `n + L` is an exact function of **two** arguments: the state at time `n`
(the far past) and the `L`-digit window read in between.  Nothing else enters.

## Why this is the right split for the crux

The crux (S7-SO/S7-SB) is a bound on the joint empirical frequency of

    "the state emits"  ∧  "Gⁿx lies in s_n⁻¹(I_w)" .

Directive fact (α) says CF-normality of `x` — a statement about finite-word frequencies — cannot
control a correlation between an arbitrary predictable object and the tail.  Write the state as
`s_n = F^L(s_{n−L}, window)`.  Then the correlation splits in two:

* the dependence on the **window**, a block of `L` consecutive digits sitting immediately before
  the tested time.  A joint statement about the window and the next few digits is a statement
  about the frequency of one finite word of length `L + |w|` — and that is **exactly** what
  CF-normality of `x` supplies.  This is the first point in the chain where normality bears on the
  joint quantity rather than on the marginal.
* the dependence on the **far-past state** `s_{n−L}`, which must be shown to wash out as `L`
  grows.  Pathwise it never does (S7-CN: reading is inert, the discrepancy is carried unchanged),
  so the washing-out has to be distributional — the Birkhoff–Hopf instrument of
  `VandeheyS7Birkhoff`, on the compact state box of directive fact (δ).

That is a genuinely different wall from "empirical versus expected for a predictable family", and
it is the wall lap 80 asked for: it names what must be proved about the far past, and it hands the
rest to normality.  The split itself, proved here, is unconditional and exact.

## Guard rule

Content locator: `pairIter_fst_congr`'s induction step consumes `cfDigit t 0 = cfDigit t' 0` at
the read and then shifts the window by `cfDigit_gaussMap`; if digits did not shift this way the
`L`-digit window would not be the right object and the split would be false.  Degenerate case:
`L = 0` makes the congruence vacuous and `runPair_add` the identity — the far-past state is the
state, and the window is empty.
-/
import NormalNumbers.VandeheyS7Skew

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- Digits shift under the Gauss map. -/
lemma cfDigit_gaussMap (t : ℝ) (i : ℕ) : cfDigit (gaussMap t) i = cfDigit t (i + 1) := by
  show cfDigit (gaussMap^[i] (gaussMap t)) 0 = cfDigit (gaussMap^[i + 1] t) 0
  rw [← Function.iterate_succ_apply]

/-- **The window cocycle.**  The run after `n + L` steps is `L` skew steps from the run at `n`. -/
theorem runPair_add (Φ : MapState) (x : ℝ) (n L : ℕ) :
    runPair Φ x (n + L) = pairStep^[L] (runPair Φ x n) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [← Nat.add_assoc, runPair_succ, ih, Function.iterate_succ_apply']

/-- **The state after `L` steps sees only the `L`-digit window.**  Two points with the same first
`L` continued-fraction digits drive the state to the same place. -/
theorem pairIter_fst_congr : ∀ (L : ℕ) (s : MapState) (t t' : ℝ),
    (∀ i < L, cfDigit t i = cfDigit t' i) →
    (pairStep^[L] (s, t)).1 = (pairStep^[L] (s, t')).1
  | 0, s, t, t', _ => rfl
  | L + 1, s, t, t', h => by
      have h0 : cfDigit t 0 = cfDigit t' 0 := h 0 (Nat.succ_pos L)
      have hread : readAt t 0 = readAt t' 0 := by
        show readMap ((inDigit t 0 : ℕ) : ℝ) _ = readMap ((inDigit t' 0 : ℕ) : ℝ) _
        have : inDigit t 0 = inDigit t' 0 := by
          show max (cfDigit t 0) 1 = max (cfDigit t' 0) 1
          rw [h0]
        simp only [this]
      have hstep : (pairStep (s, t)).1 = (pairStep (s, t')).1 := by
        show (step (s.comp (readAt t 0))).1 = (step (s.comp (readAt t' 0))).1
        rw [hread]
      have htail : ∀ i < L, cfDigit (gaussMap t) i = cfDigit (gaussMap t') i := by
        intro i hi
        rw [cfDigit_gaussMap, cfDigit_gaussMap]
        exact h (i + 1) (by omega)
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      show (pairStep^[L] ((pairStep (s, t)).1, gaussMap t)).1
          = (pairStep^[L] ((pairStep (s, t')).1, gaussMap t')).1
      rw [hstep]
      exact pairIter_fst_congr L _ (gaussMap t) (gaussMap t') htail

/-- **The split, in run coordinates.**  The state at time `n + L` is an exact function of the
state at time `n` and the `L` input digits read in between. -/
theorem runState_add_eq (Φ : MapState) (x : ℝ) (n L : ℕ) :
    runState Φ x (n + L) = (pairStep^[L] (runState Φ x n, gaussMap^[n] x)).1 := by
  have h := runPair_add Φ x n L
  exact congrArg Prod.fst h

/-- Two run times whose states agree and whose next `L` input digits agree have equal states `L`
steps later: the far past enters ONLY through the state. -/
theorem runState_add_congr {Φ Ψ : MapState} {x y : ℝ} {n m L : ℕ}
    (hs : runState Φ x n = runState Ψ y m)
    (hd : ∀ i < L, cfDigit x (n + i) = cfDigit y (m + i)) :
    runState Φ x (n + L) = runState Ψ y (m + L) := by
  rw [runState_add_eq, runState_add_eq, hs]
  refine pairIter_fst_congr L _ _ _ ?_
  intro i hi
  have hx : cfDigit (gaussMap^[n] x) i = cfDigit x (n + i) := by
    show cfDigit (gaussMap^[i] (gaussMap^[n] x)) 0 = cfDigit (gaussMap^[n + i] x) 0
    rw [← Function.iterate_add_apply, Nat.add_comm i n]
  have hy : cfDigit (gaussMap^[m] y) i = cfDigit y (m + i) := by
    show cfDigit (gaussMap^[i] (gaussMap^[m] y)) 0 = cfDigit (gaussMap^[m + i] y) 0
    rw [← Function.iterate_add_apply, Nat.add_comm i m]
  rw [hx, hy]
  exact hd i hi

end MapState

section Audit

#print axioms MapState.runPair_add
#print axioms MapState.pairIter_fst_congr
#print axioms MapState.runState_add_eq
#print axioms MapState.runState_add_congr

end Audit

end NormalNumbers.VandeheyS7
