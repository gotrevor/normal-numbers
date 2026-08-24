/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw
import NormalNumbers.CFSchedule

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
  except a neighborhood of the two endpoints; the uncovered measure is
  `≤ 4·maxₙ = 4/fib(n+1)²`, where `maxₙ` bounds a single rank-`n` cylinder
  length (`fib_le_cfK`).  Beyond a rank this is `< δ` for any `δ > 0`.
* **L2** (`length_le_two_mul_good_add_err`): composing L1 with the
  cylinder-conditioned good-mass bound (`goodC_half`: `|I_w| ≤ 2·|good ext of
  w|`) gives `|b−a| ≤ 2·|good mass inside (a,b)| + 4/fib(n+1)²` — so beyond a
  rank the good mass inside any interval is `≥ (|b−a| − δ)/2`, the affine
  schedule (L4) input.

Lemma table and lap plan: `B6-BRIEF-DRAFT.md`.  Both statements are now final
and axiom-clean; `goodInInterval` is the good-mass-inside-`(a,b)` set.
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

/-! ## L2 — good-block density on arbitrary intervals -/

/-- The good order-`m` extensions live inside their base cylinder. -/
lemma goodExtSet_subset_cfCylinder (w : List ℕ) (C : ℝ) (m : ℕ) :
    goodExtSet w C m ⊆ cfCylinder w := by
  refine Set.iUnion₂_subset fun u _ => ?_
  split
  · exact cfCylinder_append_subset w u
  · exact Set.empty_subset _

/-- The good-length extension set is measurable (countable union of cylinders). -/
lemma measurableSet_goodExtSet (w : List ℕ) (C : ℝ) (m : ℕ) :
    MeasurableSet (goodExtSet w C m) := by
  refine MeasurableSet.biUnion
    (Set.Countable.mono (Set.subset_univ _) Set.countable_univ) fun u _ => ?_
  split
  · exact measurableSet_cfCylinder _
  · exact MeasurableSet.empty

/-- The union of the good order-`m` extensions of every rank-`n` cylinder that
is contained in `(a,b)` — the "good mass inside the interval `(a,b)`". -/
noncomputable def goodInInterval (a b : ℝ) (n m : ℕ) : Set ℝ :=
  ⋃ w ∈ {w ∈ genWords n | cfCylinder w ⊆ Set.Ioo a b}, goodExtSet w goodC m

/-- **L2 — good-block density on an arbitrary interval.**  Composing L1
(`volume_interval_sdiff_covered_le`) with the cylinder-conditioned good-mass
bound (`goodC_half`: `|I_w| ≤ 2·|good extensions of w|`): the length of any
interval `(a,b) ⊆ (0,1)` is at most twice the good mass inside it plus the L1
covering error `4/fib(n+1)²`, which `→ 0`.  So beyond a rank the good mass
inside `(a,b)` is at least `(|b−a| − δ)/2` — the affine schedule (L4) input.

`n ≥ 1` (rank 0 is the whole space; the density statement is for genuine
cylinders).  `m` is the free extension order carried through from `goodC_half`. -/
theorem length_le_two_mul_good_add_err (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ENNReal.ofReal (b - a)
      ≤ 2 * volume (goodInInterval a b n m)
        + ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
  set idx : Set (List ℕ) := {w ∈ genWords n | cfCylinder w ⊆ Set.Ioo a b} with hidx
  have hidxcount : idx.Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  have hdisj_cyl : idx.PairwiseDisjoint (fun w => cfCylinder w) := by
    intro u hu u' hu' hne
    exact cfCylinder_disjoint (by rw [hu.1.1, hu'.1.1]) hne
  have hdisj_good : idx.PairwiseDisjoint (fun w => goodExtSet w goodC m) := by
    intro u hu u' hu' hne
    exact (cfCylinder_disjoint (by rw [hu.1.1, hu'.1.1]) hne).mono
      (goodExtSet_subset_cfCylinder u goodC m) (goodExtSet_subset_cfCylinder u' goodC m)
  have hcov : volume (coveredByCyl a b n) = ∑' w : idx, volume (cfCylinder (w : List ℕ)) := by
    rw [coveredByCyl]
    exact measure_biUnion hidxcount hdisj_cyl (fun w _ => measurableSet_cfCylinder w)
  have hgood : volume (goodInInterval a b n m)
      = ∑' w : idx, volume (goodExtSet (w : List ℕ) goodC m) := by
    rw [goodInInterval]
    exact measure_biUnion hidxcount hdisj_good
      (fun w _ => measurableSet_goodExtSet w goodC m)
  have hterm : ∀ w : idx,
      volume (cfCylinder (w : List ℕ)) ≤ 2 * volume (goodExtSet (w : List ℕ) goodC m) := by
    rintro ⟨w, hw⟩
    have hne : w ≠ [] := by
      have hlen : w.length = n := hw.1.1
      rw [← List.length_pos_iff]; omega
    exact goodC_half w hne hw.1.2 m
  have hcov_le : volume (coveredByCyl a b n) ≤ 2 * volume (goodInInterval a b n m) := by
    rw [hcov, hgood, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hterm
  have hcovsub : coveredByCyl a b n ⊆ Set.Ioo a b := by
    rw [coveredByCyl]; exact Set.iUnion₂_subset fun w hw => hw.2
  have hmeascov : MeasurableSet (coveredByCyl a b n) := by
    rw [coveredByCyl]
    exact MeasurableSet.biUnion hidxcount (fun w _ => measurableSet_cfCylinder w)
  have hsplit : volume (coveredByCyl a b n)
      + volume (Set.Ioo a b \ coveredByCyl a b n) = volume (Set.Ioo a b) := by
    have h := measure_inter_add_sdiff (μ := volume) (Set.Ioo a b) hmeascov
    rwa [Set.inter_eq_right.mpr hcovsub] at h
  calc ENNReal.ofReal (b - a)
      = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
    _ = volume (coveredByCyl a b n) + volume (Set.Ioo a b \ coveredByCyl a b n) := hsplit.symm
    _ ≤ 2 * volume (goodInInterval a b n m)
          + ENNReal.ofReal (4 / (Nat.fib (n + 1) : ℝ) ^ 2) := by
        gcongr
        exact volume_interval_sdiff_covered_le a b ha hab hb n

/-- **Feasibility core.**  Beyond a rank (once the L1 error `4/fib(n+1)²` drops
below `|b−a|`), the good mass inside a nondegenerate interval `(a,b) ⊆ (0,1)` is
STRICTLY positive — so `goodInInterval` is nonempty and a good CF-cylinder can
be selected inside `(a,b)`.  This is the per-stage feasibility the interleaved
affine schedule (B6 crux) needs: every refinement step has a good block to pick.
Immediate from L2 (`length_le_two_mul_good_add_err`). -/
theorem goodInInterval_pos_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hfib : 4 / (Nat.fib (n + 1) : ℝ) ^ 2 < b - a) (m : ℕ) :
    0 < volume (goodInInterval a b n m) := by
  rw [pos_iff_ne_zero]
  intro hV
  have hL2 := length_le_two_mul_good_add_err a b ha hab.le hb hn m
  rw [hV, mul_zero, zero_add, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hL2
  linarith

end NormalNumbers
