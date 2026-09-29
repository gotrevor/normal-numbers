/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyScaleCount
import NormalNumbers.VandeheyFirstLetter

/-!
# The run clock, and the dictionary between letter positions and image CF indices

`VandeheyScaleCount` produces the letter-level Cesàro limits; `VandeheyRunClock` wants the
image's CF-occurrence count sampled along a clock.  This file builds the clock and the
dictionary that converts between them.

## The clock

The transducer's letter word after `n` input digits is the length-`P n` prefix of the `L/R`
expansion of `z = D·y` (`lrWord_eq_lrExpandWord`).  Since `z` may exceed `1`, that expansion
opens with `R^{k₀}`, `k₀ = ⌊z⌋ ≤ D − 1`, and only then reads the expansion of the image
`img = fract z` (`lrExpand_shift`).  So the number of CF digits of the image that the first `n`
input digits have COMPLETED is

  `runClock n = runIdx img (P n − k₀)`,

the index of the run of `img` in which the letter word stops.  Two facts about it:

* `numAlt_lrExpandWord` — alternations of a prefix count run boundaries, so
  `runIdx img L = numAlt (prefix of length L+1)`.  Together with the `k₀ ≤ D − 1` shift this
  pins `runClock n` to `numAlt (lrWord n)` up to a constant, hence
  `VandeheyTransportB.tendsto_numAlt_lrWord_div` gives its RATE, and
  `VandeheyFirstLetter.zero_lt_runRate` its positivity.
* `runClock` is monotone (`runIdx_mono`), which is the other hypothesis of the run-clock
  capstone.
-/

namespace NormalNumbers.VandeheyLR

open Filter Mat2 VandeheyAut VandeheyOut

/-! ## Alternations count run boundaries -/

section RunDict

variable {w : ℝ} (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1)

/-- The last letter of a prefix. -/
lemma getLast?_map_range (f : ℕ → Bool) (L : ℕ) :
    ((List.range (L + 1)).map f).getLast? = some (f L) := by
  rw [List.range_succ, List.map_append]
  simp

include hirr hw in
/-- **Alternations sit at run boundaries, counted.**  `numAlt` of the length-`L+1` prefix of the
`L/R` expansion is the index of the run containing position `L`. -/
theorem numAlt_lrExpandWord : ∀ L : ℕ,
    numAlt ((List.range (L + 1)).map (lrExpand w)) = runIdx w L
  | 0 => by
      have h : runIdx w 0 = 0 := by
        refine runIdx_eq hirr hw 0 0 (by simp [lrPos]) ?_
        have := lrPos_lt_succ hirr hw 0
        simpa [lrPos] using this
      simp [h]
  | (L + 1) => by
      have ih := numAlt_lrExpandWord L
      have hlast := getLast?_map_range (lrExpand w) L
      have hsplit : (List.range (L + 2)).map (lrExpand w)
          = ((List.range (L + 1)).map (lrExpand w)) ++ [lrExpand w (L + 1)] := by
        rw [show L + 2 = (L + 1) + 1 from rfl, List.range_succ, List.map_append]
        simp
      rw [hsplit, numAlt_append_eq _ _ _ hlast, ih]
      rw [runIdx_succ_eq hirr hw L]
      have hiff := lrExpand_ne_succ_iff hirr hw L
      by_cases hb : L + 1 = lrPos w (runIdx w L + 1)
      · rw [if_pos hb]
        have hne : lrExpand w L ≠ lrExpand w (L + 1) := hiff.mpr hb
        rw [numAlt, if_neg hne]
        simp
      · rw [if_neg hb]
        have heq : lrExpand w L = lrExpand w (L + 1) := by
          by_contra hcon
          exact hb (hiff.mp hcon)
        rw [numAlt, if_pos heq]
        simp

include hirr hw in
/-- The run index is monotone in the position. -/
lemma runIdx_mono : Monotone (runIdx w) := by
  intro P P' hPP'
  by_contra hcon
  have h1 : runIdx w P' + 1 ≤ runIdx w P := by omega
  have h2 := (lrPos_strictMono hirr hw).monotone h1
  have h3 := runIdx_le (w := w) P
  have h4 := lt_runIdx_succ hirr hw P'
  omega

end RunDict

/-! ## The leading `R`-run of the image -/

/-- **The shift.**  Above `1` the `L/R` expansion opens with `R^{⌊z⌋}` and then reads the
expansion of the fractional part. -/
lemma lrExpand_shift {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    lrExpand z (⌊z⌋.toNat + j) = lrExpand (Int.fract z) j := by
  have hz' : ((⌊z⌋.toNat : ℤ)) = ⌊z⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hz)
  have hfl : ((⌊z⌋.toNat : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by
    exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) hz'
  have hle : ((⌊z⌋.toNat : ℕ) : ℝ) ≤ z := by
    rw [hfl]; exact Int.floor_le z
  have hiter : lrTail^[⌊z⌋.toNat] z = Int.fract z := by
    rw [lrTail_iter_R _ hle, Int.fract, hfl]
  rw [lrExpand, lrExpand, Nat.add_comm, Function.iterate_add_apply, hiter]

/-! ## The clock -/

variable {D : ℕ}

/-- The image point, as the capstone names it. -/
noncomputable def imgOf (D : ℕ) (x : ℝ) : ℝ := Int.fract ((D : ℝ) * x)

/-- The number of LETTERS emitted after `n` input digits. -/
noncomputable def letterLen (hD : 0 < D) (x : ℝ) (n : ℕ) : ℕ :=
  (lrWord hD (startState hD) (Int.fract x) n).length

/-- The length of the image's leading `R`-run: `⌊D · fract x⌋ ≤ D − 1`. -/
noncomputable def headRun (D : ℕ) (x : ℝ) : ℕ := ⌊(D : ℝ) * Int.fract x⌋.toNat

/-- **The run clock**: the index of the run of the image's `L/R` expansion in which the emitted
letter word stops — i.e. the number of the image's CF digits that the first `n` input digits have
completed. -/
noncomputable def runClock (hD : 0 < D) (x : ℝ) (n : ℕ) : ℕ :=
  runIdx (imgOf D x) (letterLen hD x n - headRun D x)

/-- The image of the fractional part is the image. -/
lemma fract_mul_fract (D : ℕ) (x : ℝ) :
    Int.fract ((D : ℝ) * Int.fract x) = imgOf D x := by
  have hsub : (D : ℝ) * Int.fract x = (D : ℝ) * x - ((D * ⌊x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [imgOf, hsub, Int.fract_sub_intCast]

/-- The start state acts as `x ↦ D·x`. -/
lemma act_startState (hD : 0 < D) (u : ℝ) : (startState hD).val.act u = (D : ℝ) * u := by
  simp [startState, Mat2.act, Mat2.den]

lemma letterLen_mono (hD : 0 < D) (x : ℝ) : Monotone (letterLen hD x) := by
  intro n n' h
  simp only [letterLen]
  refine List.IsPrefix.length_le ?_
  simp only [lrWord]
  exact (VandeheyOut.range_prefix h).flatMap _

/-! ## The clock is monotone, and it counts the image's runs -/

section Clock

variable (hD : 0 < D) {x : ℝ} (hirr : Irrational x) (hD1 : 1 ≤ D)

include hirr hD1 in
lemma irrational_imgOf : Irrational (imgOf D x) ∧ imgOf D x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hDx : Irrational ((D : ℝ) * x) := hirr.natCast_mul (by omega)
  obtain ⟨h0, h1, hi⟩ := Literature.fract_mem_Ioo_of_irrational hDx
  exact ⟨hi, ⟨h0, h1⟩⟩

include hirr hD1 in
lemma runClock_mono : Monotone (runClock hD x) := by
  obtain ⟨hi, h01⟩ := irrational_imgOf (D := D) (x := x) hirr hD1
  intro n n' h
  refine runIdx_mono hi h01 ?_
  have := letterLen_mono hD x h
  omega

end Clock

/-! ## The clock is `numAlt` up to a constant -/

section Bridge

variable (hD : 0 < D) {x : ℝ} (hirr : Irrational x) (hD1 : 1 ≤ D)

include hirr in
lemma fract_irr : Irrational (Int.fract x) ∧ Int.fract x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1, hi⟩ := Literature.fract_mem_Ioo_of_irrational hirr
  exact ⟨hi, ⟨h0, h1⟩⟩

include hirr in
/-- The emitted letter word is the image expansion's prefix, as a mapped range. -/
lemma lrWord_eq_map (n : ℕ) :
    lrWord hD (startState hD) (Int.fract x) n
      = (List.range (letterLen hD x n)).map (lrExpand ((D : ℝ) * Int.fract x)) := by
  obtain ⟨hi, h01⟩ := fract_irr hirr
  have h := lrWord_eq_lrExpandWord hD hi h01 n
  rw [act_startState hD] at h
  rw [← h, lrExpandWord, letterLen]

/-- `⌊z⌋` really is the length of the leading `R`-run. -/
lemma lrExpand_lt_headRun {i : ℕ} (hi : i < headRun D x) :
    lrExpand ((D : ℝ) * Int.fract x) i = false := by
  set z : ℝ := (D : ℝ) * Int.fract x with hz
  have hz0 : 0 ≤ z := by
    have := Int.fract_nonneg x
    positivity
  have hz' : ((⌊z⌋.toNat : ℤ)) = ⌊z⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hz0)
  have hfl : ((⌊z⌋.toNat : ℕ) : ℝ) ≤ z := by
    have : ((⌊z⌋.toNat : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by
      exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) hz'
    rw [this]; exact Int.floor_le z
  exact lrExpand_R_run hfl hi

include hirr hD1 in
/-- **The split at the leading run.**  Past the leading `R`-run the letters are the image's. -/
lemma map_range_split {L : ℕ} (hL : headRun D x ≤ L) :
    (List.range L).map (lrExpand ((D : ℝ) * Int.fract x))
      = List.replicate (headRun D x) false
        ++ (List.range (L - headRun D x)).map (lrExpand (imgOf D x)) := by
  set k₀ : ℕ := headRun D x with hk
  have hz0 : 0 ≤ (D : ℝ) * Int.fract x := by
    have := Int.fract_nonneg x
    positivity
  refine List.ext_getElem (by simp; omega) ?_
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range]
  rcases lt_or_ge i k₀ with hik | hik
  · rw [List.getElem_append_left (by simpa using hik)]
    rw [lrExpand_lt_headRun hik, List.getElem_replicate]
  · rw [List.getElem_append_right (by simpa using hik)]
    simp only [List.length_replicate, List.getElem_map, List.getElem_range]
    have hshift := lrExpand_shift hz0 (i - k₀)
    rw [fract_mul_fract] at hshift
    have hkk : (⌊(D : ℝ) * Int.fract x⌋.toNat) = k₀ := rfl
    rw [hkk] at hshift
    rw [← hshift]
    congr 1
    omega

/-- The last letter of a nonempty constant list. -/
lemma getLast?_replicate {α : Type*} (c : α) {k : ℕ} (hk : 1 ≤ k) :
    (List.replicate k c).getLast? = some c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ']
  simp

/-- `numAlt` changes by at most one under a cons. -/
lemma numAlt_cons_diff {α : Type*} [DecidableEq α] (b : α) (w : List α) :
    numAlt w ≤ numAlt (b :: w) ∧ numAlt (b :: w) ≤ numAlt w + 1 :=
  ⟨numAlt_le_cons b w, numAlt_cons_le b w⟩

include hirr hD1 in
/-- **The clock IS the alternation count, up to `3`.**  Hence its Cesàro rate is the run rate of
`VandeheyTransportB.tendsto_numAlt_lrWord_div`. -/
theorem runClock_sub_numAlt_le (n : ℕ) :
    runClock hD x n ≤ numAlt (false :: lrWord hD (startState hD) (Int.fract x) n) + 3 ∧
      numAlt (false :: lrWord hD (startState hD) (Int.fract x) n) ≤ runClock hD x n + 3 := by
  classical
  obtain ⟨hiimg, h01img⟩ := irrational_imgOf (D := D) (x := x) hirr hD1
  set k₀ : ℕ := headRun D x with hk
  set L : ℕ := letterLen hD x n with hLdef
  set W : List Bool := lrWord hD (startState hD) (Int.fract x) n with hW
  have hWmap : W = (List.range L).map (lrExpand ((D : ℝ) * Int.fract x)) :=
    lrWord_eq_map hD hirr n
  -- the two easy `cons` slacks
  obtain ⟨hc1, hc2⟩ := numAlt_cons_diff false W
  rcases lt_or_ge L k₀ with hLk | hLk
  · -- the letter word is still inside the leading `R`-run
    have hconst : ∀ c ∈ W, c = false := by
      intro c hc
      rw [hWmap] at hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact lrExpand_lt_headRun (by simp only [List.mem_range] at hi; omega)
    have h0 : numAlt W = 0 := numAlt_eq_zero_of_const W false hconst
    have hrc : runClock hD x n = 0 := by
      have hzero : L - k₀ = 0 := by omega
      simp only [runClock, ← hLdef, ← hk, hzero]
      refine runIdx_eq hiimg h01img 0 0 (by simp [lrPos]) ?_
      have := lrPos_lt_succ hiimg h01img 0
      simpa [lrPos] using this
    omega
  · -- past the leading run: the letters are the image's
    have hsplit : W = List.replicate k₀ false
        ++ (List.range (L - k₀)).map (lrExpand (imgOf D x)) := by
      rw [hWmap]; exact map_range_split hirr hD1 hLk
    set V : List Bool := (List.range (L - k₀)).map (lrExpand (imgOf D x)) with hV
    -- the alternation count of `V`
    have hVnum : ∀ M : ℕ, L - k₀ = M + 1 → numAlt V = runIdx (imgOf D x) M := by
      intro M hM
      rw [hV, hM]
      exact numAlt_lrExpandWord hiimg h01img M
    rcases Nat.eq_zero_or_pos (L - k₀) with hz | hpos
    · -- the letter word ends exactly at the end of the leading run
      have hrc : runClock hD x n = 0 := by
        simp only [runClock, ← hLdef, ← hk, hz]
        refine runIdx_eq hiimg h01img 0 0 (by simp [lrPos]) ?_
        have := lrPos_lt_succ hiimg h01img 0
        simpa [lrPos] using this
      have hV0 : V = [] := by rw [hV, hz]; simp
      have hWr : W = List.replicate k₀ false := by rw [hsplit, hV0]; simp
      have h0 : numAlt W = 0 := by
        refine numAlt_eq_zero_of_const W false ?_
        intro c hc
        rw [hWr] at hc
        exact List.eq_of_mem_replicate hc
      omega
    · obtain ⟨M, hM⟩ : ∃ M, L - k₀ = M + 1 := ⟨L - k₀ - 1, by omega⟩
      have hVnum' := hVnum M hM
      -- `runClock = runIdx (M+1)`, and `runIdx` steps by at most one
      have hstep := runIdx_succ_eq hiimg h01img M
      have hrc : runClock hD x n = runIdx (imgOf D x) (M + 1) := by
        simp only [runClock, ← hLdef, ← hk, hM]
      have hstep' : runIdx (imgOf D x) (M + 1) ≤ runIdx (imgOf D x) M + 1 ∧
          runIdx (imgOf D x) M ≤ runIdx (imgOf D x) (M + 1) := by
        rw [hstep]; split_ifs <;> omega
      -- and `numAlt W = numAlt V` up to the seam with the leading run
      have hWV : numAlt W ≤ numAlt V + 1 ∧ numAlt V ≤ numAlt W + 1 := by
        rcases Nat.eq_zero_or_pos k₀ with hk0 | hk0
        · have hWV0 : W = V := by rw [hsplit, hk0]; simp
          rw [hWV0]
          omega
        · have hlast : (List.replicate k₀ false).getLast? = some false :=
            getLast?_replicate false hk0
          have hsum := numAlt_append_eq (List.replicate k₀ false) V false hlast
          have hrep : numAlt (List.replicate k₀ false) = 0 :=
            numAlt_eq_zero_of_const _ false fun c hc => List.eq_of_mem_replicate hc
          obtain ⟨hd1, hd2⟩ := numAlt_cons_diff false V
          rw [hsplit, hsum, hrep]
          omega
      omega

end Bridge

/-! ## The clock's rate -/

/-- **The run rate**: the asymptotic number of image CF digits per input digit. -/
noncomputable def runRate (D : ℕ) (hD : 0 < D) : ℝ :=
  ∑ t : RState D × Bool,
    VandeheyOut.wLimit (rhoLRB hD (startPlus hD, false)) t (altWeight hD t) 1

/-- The run rate is strictly positive (`VandeheyFirstLetter.zero_lt_runRate`). -/
theorem zero_lt_runRate' (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) : 0 < runRate D hD :=
  zero_lt_runRate D hD (startPlus hD, false)

/-- **The clock grows linearly, at an `x`-independent rate.**  This is Vandehey's Lemma 6.1 for
the clock the capstone actually runs on. -/
theorem tendsto_runClock_div (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) {x : ℝ}
    (hirr : Irrational x) (hx : IsCFNormal (Int.fract x)) :
    Tendsto (fun n => (runClock hD x n : ℝ) / n) atTop (nhds (runRate D hD)) := by
  have hD1 : 1 ≤ D := hD
  have hnum := tendsto_numAlt_lrWord_div D hD (startPlus hD, false) hx
  refine cesaro_of_bounded_diff (C := 3) (fun n => ?_) hnum
  obtain ⟨h1, h2⟩ := runClock_sub_numAlt_le hD hirr hD1 n
  rw [abs_le]
  constructor
  · have : ((numAlt (false :: lrWord hD (startState hD) (Int.fract x) n) : ℕ) : ℝ)
        ≤ ((runClock hD x n : ℕ) : ℝ) + 3 := by exact_mod_cast h2
    simpa using by linarith [this]
  · have : ((runClock hD x n : ℕ) : ℝ)
        ≤ ((numAlt (false :: lrWord hD (startState hD) (Int.fract x) n) : ℕ) : ℝ) + 3 := by
      exact_mod_cast h1
    simpa using by linarith [this]

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms numAlt_lrExpandWord
#print axioms runIdx_mono
#print axioms lrExpand_shift
#print axioms fract_mul_fract
#print axioms act_startState
#print axioms runClock_mono
#print axioms map_range_split
#print axioms runClock_sub_numAlt_le
#print axioms zero_lt_runRate'
#print axioms tendsto_runClock_div
end
