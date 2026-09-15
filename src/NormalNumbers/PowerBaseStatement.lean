/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseReal
import NormalNumbers.DisjunctiveCorollaries
import NormalNumbers.G4EntropyWStatement

/-!
# The audit surface for the base-`2^k` upgrade

`G4EntropyWStatement` is the audit surface for `IsNormal 2 fullRealW`.  This module is the audit
surface for its base-`2^k` strengthening, and for the general theorem behind it.

What is proved, in words:

> A real number normal to base `b` is normal to base `b^K`, for every `K ≥ 1` — with an
> elementary proof (no Weyl/Wall, no Fourier, no measure theory).  In particular the schedule-only
> read `fullRealW` off `G₄`'s binary digits is normal to base `4`, and to every base `2^k`.

The definitions the statement rests on are pinned by kernel-evaluated anchors below, so a reader
can check that `wordOf`, `valOf`, `flat` and `blockOf` mean what their names claim:

* `wordOf b m k` is the base-`b` word of length `m` and value `k`, most significant digit first;
* `valOf b w` is its inverse, the numeric value;
* `flat b K w` replaces each base-`b^K` letter of `w` by its `K` base-`b` digits;
* `blockOf b K s j` is the value of the `K`-block of `s` starting at `K·j`, i.e. the claimed
  base-`b^K` digit — `blockOf_digitOf` is the theorem that it really is one.
-/

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### Non-vacuity anchors (kernel-evaluated) -/

/-- `5 = 1·4 + 0·2 + 1` in base two, most significant digit first. -/
theorem wordOf_anchor : wordOf 2 3 5 = [1, 0, 1] := by decide +kernel

/-- `valOf` inverts `wordOf`. -/
theorem valOf_anchor : valOf 2 [1, 0, 1] = 5 := by decide +kernel

/-- Leading zeros are kept: a length-4 word of value 5. -/
theorem wordOf_leading_zero_anchor : wordOf 2 4 5 = [0, 1, 0, 1] := by decide +kernel

/-- Flattening the base-four word `[3, 1]` into binary gives `[1,1,0,1]`. -/
theorem flat_anchor : flat 2 2 [3, 1] = [1, 1, 0, 1] := by decide +kernel

/-- Blocking the alternating sequence `0,1,0,1,…` in base `4` gives the constant digit `1`. -/
theorem blockOf_anchor : blockOf 2 2 (fun i => i % 2) 1 = 1 := by decide +kernel

/-- The block really is read from position `K·j` onwards: `blockOf` at `j = 2` with `K = 3`
reads positions `6, 7, 8`. -/
theorem blockOf_offset_anchor : blockOf 2 3 (fun i => if i = 7 then 1 else 0) 2 = 2 := by
  decide +kernel

end NormalNumbers.PowerBase

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.PowerBase NormalNumbers.PrimeLambert

/-- 🎯 **THE UPGRADE, unwound.**  The same strictly increasing, `G₄`-free read of `G₄`'s binary
digits is normal in **every** base `2^k`, `k ≥ 1` — in particular in base four. -/
theorem isNormal_two_pow_of_schedule_read :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      (∀ j, digitOf 2 fullRealW j
        = digitOf 2 (Int.fract (primeLambertAtBase 4)) (p j)) ∧
      ∀ k : ℕ, 0 < k → IsNormal (2 ^ k) fullRealW :=
  ⟨fullPosW, fullPosW_strictMono, fun j => congrFun digitOf_fullRealW j,
    isNormal_two_pow_fullRealW⟩

/-- Every finite base-four word occurs in `fullRealW`. -/
theorem isDisjunctive_four_fullRealW : IsDisjunctive 4 fullRealW :=
  isNormal_four_fullRealW.isDisjunctive (by norm_num)

end NormalNumbers.G4.Sched
