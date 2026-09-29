/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RO: the run realizes the image orbit

The run of S7-RN carries a value, `zₙ = (runState Φ x n).mob (Gⁿx)`, and the whole point of the
machine is that this value **is** the image orbit: `zₙ = G^{N n} y` for `y = Φ.mob x` and the clock
`N n = Σ_{k<n} |runWord k|`.

The induction is short once the two cases are separated.  Write `t = runState n ∘ readAt n`; the
read identity gives `t.mob (Gⁿ⁺¹x) = zₙ` in both cases.

* **Stalling step**: `runState (n+1) = t`, so `zₙ₊₁ = zₙ` and the clock does not move.
* **Emitting step**: `readMap b ∘ u = t` with `runState (n+1) = u`, so `zₙ = 1/(zₙ₊₁ + b)`, i.e.
  `zₙ₊₁ = 1/zₙ − b`.  Then `zₙ₊₁ ∈ [0,1]` because `u` is a `MapState`, `zₙ₊₁` is irrational because
  `zₙ` is, and therefore `gaussMap zₙ = fract (1/zₙ) = fract (zₙ₊₁ + b) = zₙ₊₁`.  The clock moves by
  one and the identity persists.

Note what the emitting case did *not* need: that `b` is the CF digit of `zₙ`.  It follows (the
digit is determined by `zₙ₊₁ ∈ [0,1)`), but the induction never uses it, which is why irrationality
alone carries the whole argument.
-/
import NormalNumbers.VandeheyS7Run

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

/-- The clock: output digits produced by the first `n` input digits. -/
noncomputable def runClock (Φ : MapState) (x : ℝ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (runWord Φ x k).length

@[simp] lemma runClock_zero (Φ : MapState) (x : ℝ) : runClock Φ x 0 = 0 := by simp [runClock]

lemma runClock_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    runClock Φ x (n + 1) = runClock Φ x n + (runWord Φ x n).length := by
  simp [runClock, Finset.sum_range_succ]

lemma runClock_mono (Φ : MapState) (x : ℝ) : Monotone (runClock Φ x) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [runClock_succ]; omega

/-- The run's value at input time `n`. -/
noncomputable def runValue (Φ : MapState) (x : ℝ) (n : ℕ) : ℝ :=
  (runState Φ x n).mob (gaussMap^[n] x)

/-- **S7-RO.**  The run realizes the image orbit: the value at input time `n` is the image orbit
point at clock time `N n`, and stays an irrational of `(0,1)`. -/
theorem runValue_spec (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (n : ℕ) :
    runValue Φ x n ∈ Set.Ioo (0:ℝ) 1 ∧ Irrational (runValue Φ x n) ∧
      gaussMap^[runClock Φ x n] (Φ.mob x) = runValue Φ x n := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp [runValue, runState, hy, hyirr]
  | succ n ih =>
      obtain ⟨hmem, hirr, hclock⟩ := ih
      set z := runValue Φ x n with hz
      set t := (runState Φ x n).comp (readAt x n) with ht
      -- the read identity: `t` evaluated at the next orbit point gives back `z`
      have hread : (readAt x n).mob (gaussMap^[n + 1] x) = gaussMap^[n] x := by
        have h := readMap_cfDigit_mob hx n
        rw [readMap_mob] at h
        rw [readAt, readMap_mob, inDigit_eq_cfDigit hx n]
        exact h
      have hteval : t.mob (gaussMap^[n + 1] x) = z := by
        rw [ht, mob_comp _ _ ⟨(hx (n + 1)).1.le, (hx (n + 1)).2.le⟩, hread, hz, runValue]
      by_cases hem : Emittable t
      · obtain ⟨b, hemit, hword⟩ := step_emitStep hem
        have hb : 1 ≤ b := hemit.1
        have hb1 : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        have hst : runState Φ x (n + 1) = (step t).1 := rfl
        have hcomp : (readMap (b : ℝ) hb1).comp ((step t).1) = t := (emitStep_iff hb).1 hemit
        set z' := runValue Φ x (n + 1) with hz'
        have hz'eq : z' = ((step t).1).mob (gaussMap^[n + 1] x) := by rw [hz', runValue, hst]
        have hz'mem01 : z' ∈ Set.Icc (0:ℝ) 1 := by
          rw [hz'eq]
          exact ((step t).1).mapsTo ⟨(hx (n + 1)).1.le, (hx (n + 1)).2.le⟩
        have hlink0 : (readMap (b : ℝ) hb1).mob z' = z := by
          rw [hz'eq, ← mob_comp _ _ ⟨(hx (n + 1)).1.le, (hx (n + 1)).2.le⟩, hcomp, hteval]
        have hlink : (1:ℝ) / (z' + (b : ℝ)) = z := by
          rw [← hlink0, readMap_mob]
        have hden : 0 < z' + (b : ℝ) := by linarith [hz'mem01.1]
        have h2 : z * (z' + (b : ℝ)) = 1 := by
          rw [← hlink]; field_simp
        have hsum : z' + (b : ℝ) = 1 / z := by
          rw [eq_div_iff hmem.1.ne']; linarith [h2]
        have hzval : z' = 1 / z - (b : ℝ) := by linarith [hsum]
        have hirr' : Irrational z' := by
          rw [hzval, one_div]
          exact (hirr.inv).sub_natCast b
        have hmem' : z' ∈ Set.Ioo (0:ℝ) 1 := by
          refine ⟨lt_of_le_of_ne hz'mem01.1 ?_, lt_of_le_of_ne hz'mem01.2 ?_⟩
          · intro h; exact hirr' ⟨0, by push_cast; exact h⟩
          · intro h; exact hirr' ⟨1, by push_cast; exact h.symm⟩
        have hgauss : gaussMap z = z' := by
          have h1 : (1:ℝ) / z = z' + (b : ℝ) := hsum.symm
          rw [gaussMap, if_neg hmem.1.ne']
          rw [show z⁻¹ = 1 / z from (one_div z).symm, h1]
          have hcast : (b : ℝ) = ((b : ℤ) : ℝ) := by push_cast; ring
          rw [hcast, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hmem'.1.le, hmem'.2⟩]
        refine ⟨hmem', hirr', ?_⟩
        have hlen : (runWord Φ x n).length = 1 := by
          show ((step t).2).length = 1
          rw [hword]; rfl
        rw [runClock_succ, hlen, Nat.add_comm, Function.iterate_add_apply, hclock]
        simpa using hgauss
      · have hst : runState Φ x (n + 1) = t := by
          show (step t).1 = t
          rw [step_of_not_emittable hem]
        have hlen : (runWord Φ x n).length = 0 := by
          show ((step t).2).length = 0
          rw [step_of_not_emittable hem]; simp
        have hval : runValue Φ x (n + 1) = z := by
          rw [runValue, hst, hteval]
        rw [hval]
        exact ⟨hmem, hirr, by rw [runClock_succ, hlen]; simpa using hclock⟩

end MapState

section Audit

#print axioms MapState.runValue_spec

end Audit

end NormalNumbers.VandeheyS7
