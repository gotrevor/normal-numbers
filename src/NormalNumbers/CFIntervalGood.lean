/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw

/-!
# B6 / L1+L2 — interval covering and good-block density on arbitrary intervals

Expedition **B6** (`KHINCHIN.md` §B6): the affine-image extension of the B5′
witness.  The Vandehey (Compositio 2017) §7 problem asks whether `qx + r`
CF-normal follows from `x` CF-normal (`q ≠ 0`).  The witness route needs the
brick machinery to work on IMAGE intervals `ψ(I) = qI + r`, which are not
themselves CF-cylinders.  This module supplies the two purely metric bridges,
**strictly additively** over the frozen B5′ modules (no edits to
`TBrick`/`CFSchedule`/`CFLogTail`/…):

* **L1** (`volume_interval_sdiff_covered_le`): the rank-`n` CF-cylinders that
  are FULLY CONTAINED in an interval `J = (a,b) ⊆ (0,1)` cover all of `J`
  except at most the two boundary cylinders straddling `a` and `b`; hence the
  uncovered measure is `≤ 2 · maxₙ`, where `maxₙ = 1/fib(n+1)²` bounds a single
  rank-`n` cylinder length (`fib_le_cfK`).  Beyond a rank this is `< δ` for any
  `δ > 0`.
* **L2** (`volume_interval_good_ge`, provisional): composing L1 with the
  cylinder-conditioned good-mass bound (`goodC_half` culture) gives a lower
  bound on the good-block mass inside an arbitrary interval — the input the
  affine schedule (L4) consumes.

Lemma table and lap plan: `B6-BRIEF-DRAFT.md`.  **Statement-alignment note**:
the L1 shape below is final (self-contained metric fact); the L2 shape is
PROVISIONAL — it will be pinned against the real `goodExtSet`/`goodC_half`
exports once L1 is discharged.  See `PENDING_WORK.md`.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Single rank-`n` cylinder length bound -/

/-- A single genuine rank-`n` cylinder has Lebesgue length `≤ 1/fib(n+1)²`.
Immediate from `volume_cfCylinder = 1/(qₙ(qₙ+qₙ₋₁))`, `qₙ₋₁ ≥ 0`, and the
Fibonacci lower bound `qₙ ≥ fib(n+1)` (`fib_le_cfK`).  This is the
deterministic "cylinders shrink" fact — the `maxₙ → 0` driver behind L1. -/
theorem volume_cfCylinder_le_fib (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder w) ≤ ENNReal.ofReal (1 / (Nat.fib (w.length + 1) : ℝ) ^ 2) := by
  rw [volume_cfCylinder w hw hpos]
  apply ENNReal.ofReal_le_ofReal
  set F : ℝ := (Nat.fib (w.length + 1) : ℝ) with hF
  set q : ℝ := (cfK w : ℝ) with hq
  set d : ℝ := (cfK w.dropLast : ℝ) with hd
  have hFpos : 0 < F := by
    rw [hF]; exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos _)
  have hFq : F ≤ q := by
    rw [hF, hq]; exact_mod_cast fib_le_cfK w hpos
  have hqpos : 0 < q := lt_of_lt_of_le hFpos hFq
  have hdnn : 0 ≤ d := by rw [hd]; positivity
  have hden : F ^ 2 ≤ q * (q + d) := by
    have h1 : F ^ 2 ≤ q ^ 2 := by
      rw [sq, sq]; exact mul_le_mul hFq hFq hFpos.le hqpos.le
    have h2 : q ^ 2 ≤ q * (q + d) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hqpos.le
    linarith
  exact one_div_le_one_div_of_le (by positivity) hden

/-! ## L1 — interval covered by contained rank-`n` cylinders -/

/-- The union of the rank-`n` CF-cylinders fully contained in the interval
`(a,b)`.  (Genuine `n`-words with the non-contained ones sent to `∅`, so the
biUnion is over the countable index `genWords n`, matching the partition
calculus of `CFDigitLaw`.) -/
noncomputable def coveredByCyl (a b : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ w ∈ {w ∈ genWords n | cfCylinder w ⊆ Set.Ioo a b}, cfCylinder w

/-- **L1 — interval→cylinder covering.**  For `0 ≤ a ≤ b ≤ 1`, the rank-`n`
CF-cylinders contained in `(a,b)` cover all of `(a,b)` except at most the two
boundary cylinders straddling `a` and `b`; each has length `≤ 1/fib(n+1)²`, so
the uncovered mass is `≤ 2/fib(n+1)²`.  Beyond a rank this is `< δ`.

TODO(L1): the straddler count.  Rank-`n` cylinders are pairwise-disjoint
intervals (`cfCylinder_disjoint` + `cfCylinder_subset_uIcc`/
`uIoo_subset_cfCylinder`); one that meets `(a,b)` but is not `⊆ (a,b)` must
contain `a` or `b`; disjointness caps that at two, each bounded by
`volume_cfCylinder_le_fib`. -/
theorem volume_interval_sdiff_covered_le (a b : ℝ)
    (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) (n : ℕ) :
    volume (Set.Ioo a b \ coveredByCyl a b n)
      ≤ ENNReal.ofReal (2 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
  sorry

/-! ## L2 — good-block density on arbitrary intervals (provisional) -/

/-- **L2 — good-block density on an arbitrary interval** (PROVISIONAL shape).
Composing L1 with the cylinder-conditioned good-mass bound (`goodC_half`),
the "good" rank-`n` extensions inside an interval `(a,b) ⊆ (0,1)` occupy at
least a fixed fraction of `|b − a|` beyond a rank.  The exact statement will
be pinned to the real `goodExtSet`/`goodC` exports once L1 lands. -/
theorem volume_interval_good_ge (a b : ℝ)
    (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) :
    True := by
  trivial

end NormalNumbers
