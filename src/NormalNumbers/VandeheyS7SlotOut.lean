/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SO: the crux's counting function IS the output's block count

S7-CX decoded one membership; this module cashes it in for the whole counting function.  With
`y = Φ.mob x` and `N = runClock`,

    slotCount Φ x w p  =  #{ i < N p : Gⁱy ∈ I_w }                      (`slotCount_eq_outCount`)

exactly — no error term, no hypothesis beyond the run being genuine.  The proof is an induction:
at an emitting step the clock advances by one and S7-CX says the new slot is the output's digit at
the new clock time; at a stalling step both sides are unchanged.

So the §7 front's content, stated without the state at all, is

    limsup_p  #{ i < N p : Gⁱy ∈ I_w } / N p  ≤  C · γ(I_w) ,

and since `N` is monotone and tends to infinity (`runClock_tendsto`), that limsup along the
subsequence `N p` is the honest upper digit-frequency of `y`.  `OrbitWordBound` therefore *is*
the upper-frequency half of `IsCFNormal (Φ.mob x)`, which is the theorem being sought.

Recording this settles the "is the reduction faithful?" question for the whole §7 chain: it is,
and there is no remaining slack in it to exploit.

## Guard rule

Content locator: at `p = 0` both sides are `0`; at a stalling step the identity is the statement
that a stall contributes nothing, which is where `emitIndic = 0` does all the work.  Degenerate
case: `w = []` makes both sides count every output slot, `= N p`, since `cfCylinder [] = (0,1)`
and the output orbit stays in `(0,1)`.
-/
import NormalNumbers.VandeheyS7CruxMeaning
import NormalNumbers.VandeheyS7Slot

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

open Classical in
/-- The output's block count: how many of the first `k` output orbit points lie in `I_w`. -/
noncomputable def outCount (Φ : MapState) (x : ℝ) (w : List ℕ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, if gaussMap^[i] (Φ.mob x) ∈ cfCylinder w then (1:ℝ) else 0

/-- **S7-SO.**  The crux's counting function is the output's block count, exactly. -/
theorem slotCount_eq_outCount (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (w : List ℕ) (p : ℕ) :
    slotCount Φ x w p = outCount Φ x w (runClock Φ x p) := by
  classical
  induction p with
  | zero => simp [slotCount, outCount]
  | succ p ih =>
      have hstep : slotCount Φ x w (p + 1)
          = slotCount Φ x w p
            + emitIndic Φ x p * blockIndic (mapBlockSet (runState Φ x p) w 0) (gaussMap^[p] x) := by
        simp [slotCount, Finset.sum_range_succ]
      have hlen := runWord_length_le_one Φ x p
      have hclock : runClock Φ x (p + 1) = runClock Φ x p + (runWord Φ x p).length :=
        runClock_succ Φ x p
      rcases Nat.lt_or_ge (runWord Φ x p).length 1 with hz | ho
      · -- a stall: nothing moves
        have hz0 : (runWord Φ x p).length = 0 := by omega
        have hE : emitIndic Φ x p = 0 := by rw [emitIndic, hz0]; norm_num
        rw [hstep, hE, zero_mul, add_zero, ih, hclock, hz0, Nat.add_zero]
      · -- an emission: the new slot is the output's digit at the new clock time
        have ho1 : (runWord Φ x p).length = 1 := by omega
        have hE : emitIndic Φ x p = 1 := by rw [emitIndic, ho1]; norm_num
        have hiff := mem_mapBlockSet_iff Φ hx hy hyirr p 0 w
        rw [Nat.add_zero] at hiff
        have hind : blockIndic (mapBlockSet (runState Φ x p) w 0) (gaussMap^[p] x)
            = if gaussMap^[runClock Φ x p] (Φ.mob x) ∈ cfCylinder w then (1:ℝ) else 0 := by
          by_cases hmem : gaussMap^[p] x ∈ mapBlockSet (runState Φ x p) w 0
          · rw [blockIndic, Set.indicator_of_mem hmem, if_pos (hiff.mp hmem)]; rfl
          · rw [blockIndic, Set.indicator_of_notMem hmem,
              if_neg (fun h => hmem (hiff.mpr h))]
        rw [hstep, hE, one_mul, ih, hind, hclock, ho1, outCount, outCount,
          Finset.sum_range_succ]

end MapState

section Audit

#print axioms MapState.slotCount_eq_outCount

end Audit

end NormalNumbers.VandeheyS7
