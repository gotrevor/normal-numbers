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
CF-cylinders contained in `(a,b)` cover all of `(a,b)` except a neighborhood of
the two endpoints: every rank-`n` cylinder that *straddles* the boundary has
length `≤ M := 1/fib(n+1)²` and meets the boundary, hence lies within `M` of `a`
or `b`.  So the uncovered mass is `≤ 4M = 4/fib(n+1)²`, which `→ 0`; beyond a
rank it is `< δ` for any `δ > 0`.

Proof: an irrational point of `(a,b)` not covered lies in a rank-`n` cylinder
`cfCylinder u` (its own digits, `u ∈ genWords n`) that is NOT `⊆ (a,b)` — so
`u` has a companion point outside `(a,b)`.  Packaging `cfCylinder u ⊆ Icc lo hi`
with `hi − lo ≤ M` (`cfCylinder_subset_Icc_length` + `volume_cfCylinder_le_fib`),
the two points pin `a` (or `b`) into `[lo,hi]`, so the whole cylinder — and in
particular the point — sits in `[a−M,a+M] ∪ [b−M,b+M]`.  Rationals are null. -/
theorem volume_interval_sdiff_covered_le (a b : ℝ)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ 1) (n : ℕ) :
    volume (Set.Ioo a b \ coveredByCyl a b n)
      ≤ ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
  set M : ℝ := 1 / (Nat.fib (n + 1) : ℝ) ^ 2 with hM
  have hFpos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos _)
  have hMpos : 0 < M := by rw [hM]; positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- rank 0: RHS = 4, and the whole interval has mass ≤ 1
    subst hn0
    calc volume (Set.Ioo a b \ coveredByCyl a b 0)
        ≤ volume (Set.Ioo a b) := measure_mono Set.diff_subset
      _ ≤ ENNReal.ofReal 1 := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (4 / (Nat.fib (0 + 1) : ℝ) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal; rw [Nat.fib_one]; norm_num
  -- The straddler neighborhood of the two endpoints.
  set S : Set ℝ := Set.Icc (a - M) (a + M) ∪ Set.Icc (b - M) (b + M) with hS
  -- Key containment: uncovered ⊆ S ∪ ℚ.
  have hsub : Set.Ioo a b \ coveredByCyl a b n ⊆ S ∪ Set.range ((↑) : ℚ → ℝ) := by
    rintro x ⟨⟨hax, hxb⟩, hxnc⟩
    by_cases hirr : Irrational x
    · -- x is in its own rank-n cylinder u
      left
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt ha hax, lt_of_lt_of_le hxb hb⟩
      set u : List ℕ := (List.range n).map fun i => cfDigit x i with hu_def
      have hulen : u.length = n := by simp [hu_def]
      have hugen : u ∈ genWords n := by
        refine ⟨hulen, fun c hc => ?_⟩
        simp only [hu_def, List.mem_map, List.mem_range] at hc
        obtain ⟨i, _, rfl⟩ := hc
        exact one_le_cfDigit x hirr hx01 _
      have hxu : x ∈ cfCylinder u := by
        refine ⟨hx01, fun i hi => ?_⟩
        rw [hulen] at hi
        simp [hu_def, hi, List.getD_eq_getElem?_getD]
      -- u's cylinder is NOT ⊆ (a,b), else x would be covered
      have hunotsub : ¬ (cfCylinder u ⊆ Set.Ioo a b) := by
        intro hcon
        exact hxnc (Set.mem_biUnion ⟨hugen, hcon⟩ hxu)
      obtain ⟨y, hyu, hyab⟩ := Set.not_subset.mp hunotsub
      -- package u into an Icc of length ≤ M
      have hune : u ≠ [] := by
        rw [← List.length_pos_iff]; omega
      obtain ⟨lo, hi, hIcc, hlen⟩ :=
        cfCylinder_subset_Icc_length u hune hugen.2
      have hlenM : hi - lo ≤ M := by
        rw [hlen]
        have := volume_cfCylinder_le_fib u hune hugen.2
        rw [hulen] at this
        calc (volume (cfCylinder u)).toReal
            ≤ (ENNReal.ofReal M).toReal :=
              ENNReal.toReal_mono (by simp) (by rw [hM]; simpa using this)
          _ = M := ENNReal.toReal_ofReal hMpos.le
      have hxlo : lo ≤ x := (hIcc hxu).1
      have hxhi : x ≤ hi := (hIcc hxu).2
      have hylo : lo ≤ y := (hIcc hyu).1
      have hyhi : y ≤ hi := (hIcc hyu).2
      -- y ∉ (a,b): y ≤ a or b ≤ y
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hyab
      rcases hyab with hya | hby
      · -- y ≤ a < x: a ∈ [lo,hi], so x ∈ [a-M, a+M]
        left
        constructor
        · linarith [hxhi, hlenM, hxlo]
        · linarith [hxhi, hlenM, hylo, hya, hax]
      · -- x < b ≤ y: b ∈ [lo,hi], so x ∈ [b-M, b+M]
        right
        constructor
        · linarith [hxlo, hlenM, hyhi, hby, hxb]
        · linarith [hxlo, hlenM, hxhi]
    · right
      rw [Irrational] at hirr
      push_neg at hirr
      exact hirr
  -- measure the neighborhood
  calc volume (Set.Ioo a b \ coveredByCyl a b n)
      ≤ volume (S ∪ Set.range ((↑) : ℚ → ℝ)) := measure_mono hsub
    _ ≤ volume S + volume (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
    _ = volume S := by rw [(Set.countable_range _).measure_zero, add_zero]
    _ ≤ volume (Set.Icc (a - M) (a + M)) + volume (Set.Icc (b - M) (b + M)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        rw [hM]; ring

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
