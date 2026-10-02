/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CK: the circularity check — is the crux a reduction, a restatement, or neither?

The operator's wrap-up question (DIRECTION, 2026-09-29): does the GOAL `IsCFNormal (Φ.mob x)` imply
the crux?  The answer is exact, and it is neither "yes" nor "no":

* **The signed crux IS the goal.**  S7-NR proves both directions: `SignedForget Φ x w` — the crux's
  Cesàro sum with the absolute value REMOVED — holds exactly when `slotCount Φ x w p / p → γ(I_w)`,
  which with the clock is the goal (`signedForget_iff_slotCountFreq`).  So everything in the crux
  beyond its absolute values is a restatement of the theorem being sought.

* **The absolute values are not free.**  `abs_gap_witness` below: two `[0,1]`-valued sequences whose
  Cesàro means agree (both `1/2`) while the Cesàro mean of `|difference|` is `1`.  So no argument
  that sees only the two counting functions can produce the crux; the step from signed to absolute
  needs LOCAL information.

* **What the goal would still owe.**  Reconstructing `BlockForgetAll` from the goal needs two local
  statements, and neither follows from a statement about global frequencies:
  1. *window concentration* — for a CF-normal point the window frequency at scale `T` is within `ε`
     of `γ(I_w)` in Cesàro average (a property of the Gauss system alone; the inputs for its proof
     are S7-PC's pair-correlation decay and the repo's `variance_blockCount_le`), and
  2. *local clock regularity* — the number of emissions during a window of `T` reads must be `≈ T`
     in Cesàro average, a LOCAL strengthening of the clock rate (S7-CO) which the global rate does
     not give.

**Verdict.**  `BlockForgetRun`/`BlockForgetAll` is strictly stronger than the headline: it is the
headline plus local clock regularity plus window concentration.  It is therefore not a reduction —
proving it proves the theorem — and route A's architecture (S7-AW) is best read as a *factorisation*
of the headline into a local statement, not as a path to it.

## Guard rule

**Content locator.**  `abs_gap_witness` is the only theorem; the rest of the verdict is carried by
S7-NR (both directions) and by S7-AW (the crux implies the goal).

**Degenerate cases.**  The witness uses period-2 sequences, so the Cesàro means are exact at even
`p`; the statement is at even `p` for that reason.
-/
import NormalNumbers.VandeheyS7NoReduction

namespace NormalNumbers.VandeheyS7

open Finset

/-- **The absolute value is not free.**  Two `[0,1]`-valued sequences with the same Cesàro mean
whose difference has Cesàro `L¹` norm `1`: at every even length, the signed average of the
difference is `0` while the average of its absolute value is `1`.  So an argument that controls only
the two counting functions cannot control the crux's summand. -/
theorem abs_gap_witness (p : ℕ) :
    (∑ m ∈ range (2 * p), ((if m % 2 = 0 then (1:ℝ) else 0) - (if m % 2 = 0 then 0 else 1))) = 0 ∧
      (∑ m ∈ range (2 * p),
        |(if m % 2 = 0 then (1:ℝ) else 0) - (if m % 2 = 0 then 0 else 1)|) = 2 * p := by
  classical
  induction p with
  | zero => simp
  | succ k ih =>
      have hsplit : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have h0 : (2 * k) % 2 = 0 := by omega
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      constructor
      · rw [if_pos h0, if_pos h0, if_neg (by omega : ¬ (2 * k + 1) % 2 = 0),
          if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
        have := ih.1
        push_cast
        linarith [this]
      · rw [if_pos h0, if_pos h0, if_neg (by omega : ¬ (2 * k + 1) % 2 = 0),
          if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
        have := ih.2
        push_cast at this ⊢
        rw [show |(1:ℝ) - 0| = 1 from by norm_num, show |(0:ℝ) - 1| = 1 from by norm_num]
        linarith [this]

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.abs_gap_witness

end Audit
