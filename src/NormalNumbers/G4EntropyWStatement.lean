/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWSqueeze
import NormalNumbers.DisjunctiveCorollaries

/-!
# The audit surface for `IsNormal 2 fullRealW`

This module states the expedition's endpoint in the form an auditor should read, with the
abbreviations unwound, and records the immediate corollaries.

What is proved, in words:

> There is a **strictly increasing** map `p : ℕ → ℕ` whose definition mentions only the
> base-four schedule — never `G₄` — such that the real number whose `j`-th **binary digit** is
> `G₄`'s `p j`-th binary digit is **normal in base two**.

The three parts are separate theorems so that each can be checked on its own:

* `fullPosW_strictMono` (`G4EntropyFullSeqW`) — `p = fullPosW` is strictly increasing.  Its
  definition takes no real argument at all, which is the machine-checkable form of "schedule
  only": `fullPosW j = fnthW (fgrpW j) ((j − fTW (fgrpW j)) / kk (fgrpW j)) + …`, built from the
  band thresholds and the distinct window starts.
* `digitOf_fullRealW` — the constructed real's **own** binary expansion is exactly that read.
  This is the faithfulness step: without it, `fullRealW` would merely be *a* number built from
  those digits, not the number whose digits they are.
* `isNormal_fullRealW` (`G4EntropyWSqueeze`) — it is normal in base two.

`isNormal_two_of_schedule_read` bundles the three into a single statement.

**What `fullRealW` is, and what is NOT claimed.**  `fullRealW := realOfDigits 2 (fullDigW G₄)`
with `fullDigW G₄ j := digitOf 2 (Int.fract G₄) (fullPosW j)`: the real whose `j`-th binary
digit is `G₄`'s binary digit at the schedule position `fullPosW j`.  The positions read are a
sparse sample of `G₄`'s digit string: at each scale `i` the windows sit on the grid of the
tensor construction, and `Sched.density_coeff_le` (`G4ResidualConfinement`) bounds the upper
density of the positions read at scale `i` by a coefficient below `10^(−10^1665000)` already at
`i = 0`, so the read set has density zero in the digit string.  The positions themselves are
astronomically large: every window start of band `i` lies above
`wLo i = 4 · Xlo (KK i)` (`wLo_le_fnthW`), with `KK 0 = 160000`.  Consequently normality of
`fullRealW` says nothing about normality of `G₄` itself: a mask that changes every unread
digit changes `G₄` without changing `fullRealW`.  The theorem is exactly the normality of one
explicitly specified extracted real, not of the source.
-/

open Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- `fullRealW` is a genuine binary expansion: it lies in `[0,1)`. -/
theorem fullRealW_mem_Ico : fullRealW ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico 2 (le_refl 2) _ (fullDigW_lt _) properDigits_fullDigW

/-- **The faithfulness identity.**  `fullRealW`'s own base-two digit sequence is `G₄`'s base-two
digit sequence read at the schedule-defined positions `fullPosW`. -/
theorem digitOf_fullRealW :
    digitOf 2 fullRealW = fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (fullPosW j) :=
  digitOf_realOfDigits 2 (le_refl 2) _ (fullDigW_lt _) properDigits_fullDigW

/-- 🎯 **THE HEADLINE, unwound.**  There is a strictly increasing, `G₄`-free position map `p`
such that the real whose binary digits are `G₄`'s binary digits at the positions `p` is normal
in base two. -/
theorem isNormal_two_of_schedule_read :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      (∀ j, digitOf 2 fullRealW j
        = digitOf 2 (Int.fract (primeLambertAtBase 4)) (p j)) ∧
      IsNormal 2 fullRealW :=
  ⟨fullPosW, fullPosW_strictMono, fun j => congrFun digitOf_fullRealW j, isNormal_fullRealW⟩

/-- Every finite binary word occurs in `fullRealW`. -/
theorem isDisjunctive_fullRealW : IsDisjunctive 2 fullRealW :=
  isNormal_fullRealW.isDisjunctive (le_refl 2)

/-- `fullRealW` is irrational. -/
theorem irrational_fullRealW : Irrational fullRealW :=
  isDisjunctive_fullRealW.irrational

end NormalNumbers.G4.Sched
