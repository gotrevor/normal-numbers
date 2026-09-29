/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SK: the run is a SKEW PRODUCT, and the crux is a Birkhoff sum of a FIXED observable

Directive fact (α) says: "predictable + bounded distortion" can never beat the crux, because
`exists_predictor_all_hit` builds a family `n ↦ A_n`, each `A_n` determined by `x₁…x_n`, that is
hit at every time while each `A_n` has tiny measure.  Lap 80 showed the front is one statement and
warned that any future route must produce real information about the output.  This module supplies
the one piece of structure the counterexample families provably lack, and it is unconditional.

## The structure

The run's state is not an arbitrary predictable object: it is driven by an autonomous map.  Put

    pairStep (s, t)  =  ( (step (s.comp (readAt t 0))).1 , gaussMap t )

on `MapState × ℝ`, and `runPair Φ x n = (runState Φ x n, gaussMap^[n] x)`.  Then

    runPair Φ x (n+1) = pairStep (runPair Φ x n)        (`runPair_succ`)
    runPair Φ x n     = pairStep^[n] (Φ, x)             (`runPair_eq_iterate`)

i.e. the pair (state, current point) is the **orbit of a single fixed map** — a skew product over
the Gauss map, with the state as the fibre coordinate.  The only input is that the digit read at
time `n` is a function of `Gⁿx` alone (`readAt_iterate`), which is `rfl` for `cfDigit`.

## Why that is the escape from fact (α)

The crux's counting function is then a Birkhoff sum of a **time-independent** observable:

    slotCount Φ x w p = ∑_{n<p} slotObs w (runPair Φ x n)     (`slotCount_eq_sum_slotObs`)
    runClock Φ x p    = ∑_{n<p} emitObs (runPair Φ x n)       (`runClock_eq_sum_emitObs`)

with `slotObs w`, `emitObs` fixed functions on `MapState × ℝ`, depending on neither `n` nor `x`
nor `Φ`.  A predictable family in the sense of `exists_predictor_all_hit` has no such
representation: its sets are chosen freely at each time, so its counting function is not a
Birkhoff sum of anything.  This is exactly the gap fact (α) left open, and it is what makes the
ergodic instruments (invariant limits of the empirical measures, disintegration over the Gauss
base) applicable at all.

## The invariance, exactly

For **any** `f : MapState × ℝ → ℝ` the empirical measures' defect of invariance telescopes:

    ∑_{n<N} ( f (pairStep (runPair Φ x n)) − f (runPair Φ x n) )
      = f (runPair Φ x N) − f (runPair Φ x 0)                (`sum_pairStep_sub`)

an exact identity, so for bounded `f` the averaged defect is `≤ 2M/N` (`abs_avg_defect_le`).
Hence every weak-∗ limit of `(1/N) ∑_{n<N} δ_{runPair Φ x n}` is `pairStep`-invariant, and — since
`x` is CF-normal — its base marginal is the Gauss measure.  That is the precise sense in which the
crux is now: *for every `pairStep`-invariant measure `ν` with Gauss base marginal,*
`ν(slotObs w) ≤ C γ(I_w) · ν(emitObs)`.

## Guard rule

Content locator: `runPair_succ`'s first component is `runState`'s defining equation with
`readAt x n` rewritten as `readAt (Gⁿx) 0`; if that rewrite were false the whole skew-product
reading collapses (the state would depend on the absolute time, not the current point).
Degenerate case: a stalling step has `emitObs = 0` and `slotObs = 0`, so stalls contribute to
neither sum — consistent with `slotCount`/`runClock` at `p = 0`.
-/
import NormalNumbers.VandeheyS7Slot

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-! ## The digit read is a function of the current point -/

/-- The digit read at time `n` depends only on `Gⁿx`. -/
theorem inDigit_iterate (x : ℝ) (n : ℕ) : inDigit x n = inDigit (gaussMap^[n] x) 0 := rfl

/-- The read map at time `n` depends only on `Gⁿx`. -/
theorem readAt_iterate (x : ℝ) (n : ℕ) : readAt x n = readAt (gaussMap^[n] x) 0 := rfl

/-! ## The skew product -/

/-- One step of the autonomous map driving the run: read the current point's digit, feed it to
the state, emit if possible, and advance the point by the Gauss map. -/
noncomputable def pairStep (p : MapState × ℝ) : MapState × ℝ :=
  ((step (p.1.comp (readAt p.2 0))).1, gaussMap p.2)

/-- The word emitted by one skew step. -/
noncomputable def pairWord (p : MapState × ℝ) : List ℕ :=
  (step (p.1.comp (readAt p.2 0))).2

/-- The pair (state, current point) at input time `n`. -/
noncomputable def runPair (Φ : MapState) (x : ℝ) (n : ℕ) : MapState × ℝ :=
  (runState Φ x n, gaussMap^[n] x)

@[simp] lemma runPair_zero (Φ : MapState) (x : ℝ) : runPair Φ x 0 = (Φ, x) := rfl

/-- **S7-SK.**  The run is the orbit of a single fixed map. -/
theorem runPair_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    runPair Φ x (n + 1) = pairStep (runPair Φ x n) := by
  refine Prod.ext ?_ ?_
  · show runState Φ x (n + 1) = (step ((runState Φ x n).comp (readAt (gaussMap^[n] x) 0))).1
    rw [← readAt_iterate]
    rfl
  · show gaussMap^[n + 1] x = gaussMap (gaussMap^[n] x)
    rw [Function.iterate_succ_apply']

theorem runPair_eq_iterate (Φ : MapState) (x : ℝ) (n : ℕ) :
    runPair Φ x n = pairStep^[n] (Φ, x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [runPair_succ, ih, Function.iterate_succ_apply']

/-- The emitted word is a function of the pair. -/
theorem runWord_eq_pairWord (Φ : MapState) (x : ℝ) (n : ℕ) :
    runWord Φ x n = pairWord (runPair Φ x n) := by
  show (step ((runState Φ x n).comp (readAt x n))).2
      = (step ((runState Φ x n).comp (readAt (gaussMap^[n] x) 0))).2
  rw [← readAt_iterate]

/-! ## The crux's counting functions are Birkhoff sums -/

/-- The emission observable: `1` if the step emits, `0` if it stalls. -/
noncomputable def emitObs (p : MapState × ℝ) : ℝ := ((pairWord p).length : ℝ)

/-- The slot observable: `1` exactly when the step emits and the emitted digit block is `w`. -/
noncomputable def slotObs (w : List ℕ) (p : MapState × ℝ) : ℝ :=
  emitObs p * blockIndic (mapBlockSet p.1 w 0) p.2

theorem emitIndic_eq_emitObs (Φ : MapState) (x : ℝ) (n : ℕ) :
    emitIndic Φ x n = emitObs (runPair Φ x n) := by
  rw [emitIndic, emitObs, runWord_eq_pairWord]

/-- **The crux is a Birkhoff sum of a fixed observable.** -/
theorem slotCount_eq_sum_slotObs (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) :
    slotCount Φ x w p = ∑ n ∈ range p, slotObs w (runPair Φ x n) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [slotObs, ← emitIndic_eq_emitObs]
  rfl

theorem runClock_eq_sum_emitObs (Φ : MapState) (x : ℝ) (p : ℕ) :
    (runClock Φ x p : ℝ) = ∑ n ∈ range p, emitObs (runPair Φ x n) := by
  rw [runClock_eq_sum_emitIndic]
  exact Finset.sum_congr rfl fun n _ => emitIndic_eq_emitObs Φ x n

/-- Both counting functions are Birkhoff sums of fixed observables along one orbit of
`pairStep`. -/
theorem slotCount_eq_birkhoffSum (Φ : MapState) (x : ℝ) (w : List ℕ) (p : ℕ) :
    slotCount Φ x w p = ∑ n ∈ range p, slotObs w (pairStep^[n] (Φ, x)) := by
  rw [slotCount_eq_sum_slotObs]
  exact Finset.sum_congr rfl fun n _ => by rw [runPair_eq_iterate]

/-! ## Near-invariance of the empirical measures -/

/-- **The defect of invariance telescopes, exactly.** -/
theorem sum_pairStep_sub (Φ : MapState) (x : ℝ) (f : MapState × ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, (f (pairStep (runPair Φ x n)) - f (runPair Φ x n)))
      = f (runPair Φ x N) - f (runPair Φ x 0) := by
  have h : ∀ n, f (pairStep (runPair Φ x n)) = f (runPair Φ x (n + 1)) := by
    intro n; rw [runPair_succ]
  simp only [h]
  exact Finset.sum_range_sub (fun n => f (runPair Φ x n)) N

/-- For a bounded observable the averaged defect of invariance is `O(1/N)`: every weak-∗ limit
of the empirical measures of the run is `pairStep`-invariant. -/
theorem abs_avg_defect_le (Φ : MapState) (x : ℝ) {f : MapState × ℝ → ℝ} {M : ℝ}
    (hf : ∀ p, |f p| ≤ M) (N : ℕ) :
    |(∑ n ∈ range N, (f (pairStep (runPair Φ x n)) - f (runPair Φ x n))) / (N : ℝ)|
      ≤ 2 * M / (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 := hf (runPair Φ x N)
  have h2 := hf (runPair Φ x 0)
  have hnum : |f (runPair Φ x N) - f (runPair Φ x 0)| ≤ 2 * M := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  rw [sum_pairStep_sub, abs_div, abs_of_pos hNpos]
  gcongr

end MapState

section Audit

#print axioms MapState.runPair_succ
#print axioms MapState.runPair_eq_iterate
#print axioms MapState.slotCount_eq_birkhoffSum
#print axioms MapState.sum_pairStep_sub
#print axioms MapState.abs_avg_defect_le

end Audit

end NormalNumbers.VandeheyS7
