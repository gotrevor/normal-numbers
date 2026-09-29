/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyRunDict

/-!
# The run dictionary, as a count: `hcount` for the Raney machine

`VandeheyRunClock.mobiusUniformFreq_of_runClock` has one remaining hypothesis, `hcount`: an
`x`-independent Cesàro limit for the image's CF-occurrence count sampled along the run clock.
`VandeheyScaleCount.exists_tendsto_countOccurrences_patN` supplies the *letter-level* limit.
This file is the `O(1)` bookkeeping between them.
-/

namespace NormalNumbers.VandeheyLR

open Filter Mat2 VandeheyAut VandeheyOut

variable {D : ℕ}

/-! ## The emitted word in the two alphabets -/

lemma outWord_lrOutN (hD : 0 < D) (s₀ : RState D) (x : ℝ) (n : ℕ) :
    outWord (lrDelta hD) (lrOutN hD) s₀ x n = (lrWord hD s₀ x n).map encLetter := by
  simp only [outWord, lrWord, outBlock, lrOutN, List.map_flatMap]
  rfl

/-! ## Block matching, as a pointwise statement -/

lemma match_iff {α : Type*} [Inhabited α] (s : ℕ → α) (v : List α) (n : ℕ) :
    v = (List.range' n v.length).map s ↔ ∀ i, i < v.length → s (n + i) = v[i]! := by
  constructor
  · intro h i hi
    have h2 : v[i]! = ((List.range' n v.length).map s)[i]! := by rw [← h]
    rw [h2, List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range' (by omega)]
    simp
  · intro h
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range', one_mul, h i h1,
      List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rfl

/-! ## Pattern-occurrence counts on a window of letter positions -/

open scoped Classical in
/-- The number of positions in `[A, B)` at which the letter stream `f` reads the pattern `p`. -/
noncomputable def patCard (f : ℕ → Bool) (p : List Bool) (A B : ℕ) : ℕ :=
  ((Finset.Ico A B).filter (fun P => (List.range' P p.length).map f = p)).card

open scoped Classical in
/-- Enlarging the window on the left costs at most the enlargement. -/
lemma patCard_zero_le (f : ℕ → Bool) (p : List Bool) (A B : ℕ) :
    patCard f p 0 B ≤ patCard f p A B + A ∧ patCard f p A B ≤ patCard f p 0 B := by
  constructor
  · have hsub : (Finset.Ico 0 B).filter (fun P => (List.range' P p.length).map f = p)
        ⊆ ((Finset.Ico A B).filter (fun P => (List.range' P p.length).map f = p))
          ∪ Finset.range A := by
      intro P hP
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union, Finset.mem_range] at hP ⊢
      rcases lt_or_ge P A with h | h
      · exact Or.inr h
      · exact Or.inl ⟨⟨h, hP.1.2⟩, hP.2⟩
    have := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      (((Finset.Ico A B).filter (fun P => (List.range' P p.length).map f = p)))
      (Finset.range A)
    simp only [Finset.card_range] at h2
    exact le_trans this h2
  · exact Finset.card_le_card (Finset.filter_subset_filter _ (by
      intro P hP
      simp only [Finset.mem_Ico] at hP ⊢
      exact ⟨Nat.zero_le _, hP.2⟩))

/-! ## The letter-count side: `countOccurrences` is a pattern card -/

lemma map_range'_map (f : ℕ → Bool) (P m : ℕ) :
    (List.range' P m).map (fun j => encLetter (f j))
      = ((List.range' P m).map f).map encLetter := by
  rw [List.map_map]
  rfl

open scoped Classical in
lemma occStart_patN_eq (f : ℕ → Bool) (b : Bool) (u : List ℕ) (N : ℕ) :
    occStart (patN b u) (fun j => encLetter (f j)) N = patCard f (patWord b u) 0 N := by
  rw [occStart, patCard, ← Finset.range_eq_Ico]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro P _
  have hlen : (patN b u).length = (patWord b u).length := by
    rw [patN, List.length_map]
  rw [hlen, map_range'_map, patN]
  exact ⟨fun h => (List.map_injective_iff.mpr encLetter_injective h).symm,
    fun h => congrArg (List.map encLetter) h.symm⟩

/-! ## The shift past the leading `R`-run -/

lemma map_range'_lrExpand_shift {z : ℝ} (hz : 0 ≤ z) (Q m : ℕ) :
    (List.range' (⌊z⌋.toNat + Q) m).map (lrExpand z)
      = (List.range' Q m).map (lrExpand (Int.fract z)) := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range']
  rw [show ⌊z⌋.toNat + Q + 1 * i = ⌊z⌋.toNat + (Q + 1 * i) from by omega]
  exact lrExpand_shift hz (Q + 1 * i)

open scoped Classical in
/-- **Reindexing past the leading run.**  Pattern occurrences of the stream of `z` at positions
`≥ ⌊z⌋` are exactly the pattern occurrences of the stream of `fract z`, shifted. -/
lemma patCard_shift {z : ℝ} (hz : 0 ≤ z) (p : List Bool) (N : ℕ) :
    patCard (lrExpand z) p (⌊z⌋.toNat) N
      = patCard (lrExpand (Int.fract z)) p 0 (N - ⌊z⌋.toNat) := by
  set k₀ : ℕ := ⌊z⌋.toNat with hk
  refine Finset.card_bij (fun P _ => P - k₀) ?_ ?_ ?_
  · intro P hP
    simp only [Finset.mem_filter, Finset.mem_Ico] at hP ⊢
    obtain ⟨⟨h1, h2⟩, hocc⟩ := hP
    refine ⟨⟨Nat.zero_le _, by omega⟩, ?_⟩
    rw [← map_range'_lrExpand_shift hz (P - k₀) p.length,
      show k₀ + (P - k₀) = P from by omega]
    exact hocc
  · intro P hP Q hQ hEq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hP hQ
    omega
  · intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_Ico] at hQ ⊢
    obtain ⟨⟨_, h2⟩, hocc⟩ := hQ
    refine ⟨k₀ + Q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [map_range'_lrExpand_shift hz Q p.length]
    exact hocc

/-! ## The window: from `[0, N)` to the run window `[lrPos 1 − 1, lrPos M − 1)` -/

section Window

variable {w : ℝ} (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1)

open scoped Classical in
include hirr hw in
/-- **The two ends of the window cost at most one occurrence.**  Below `lrPos w 1 − 1` there is
no occurrence at all, and above `lrPos w M − 1` (with `M` the run index of the right endpoint)
there is at most the single position `lrPos w M − 1`. -/
lemma patCard_window (b : Bool) (a : ℕ) (v : List ℕ) (hv : ∀ x ∈ a :: v, 1 ≤ x) (Nl : ℕ) :
    patCard (lrExpand w) (patWord b (a :: v)) 0 Nl
        ≤ patCard (lrExpand w) (patWord b (a :: v))
            (lrPos w 1 - 1) (lrPos w (runIdx w Nl) - 1) + 1 ∧
      patCard (lrExpand w) (patWord b (a :: v))
          (lrPos w 1 - 1) (lrPos w (runIdx w Nl) - 1)
        ≤ patCard (lrExpand w) (patWord b (a :: v)) 0 Nl := by
  set M : ℕ := runIdx w Nl with hM
  set p : List Bool := patWord b (a :: v) with hp
  have hplen : p.length = (a :: v).sum + 2 := patWord_length b (a :: v)
  have hmono := lrPos_strictMono hirr hw
  have hMle : lrPos w M ≤ Nl := runIdx_le (w := w) Nl
  have hNlt : Nl < lrPos w (M + 1) := lt_runIdx_succ hirr hw Nl
  constructor
  · have hsub : (Finset.Ico 0 Nl).filter (fun P => (List.range' P p.length).map (lrExpand w) = p)
        ⊆ ((Finset.Ico (lrPos w 1 - 1) (lrPos w M - 1)).filter
            (fun P => (List.range' P p.length).map (lrExpand w) = p))
          ∪ {lrPos w M - 1} := by
      intro P hP
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union,
        Finset.mem_singleton] at hP ⊢
      obtain ⟨⟨-, hPN⟩, hocc⟩ := hP
      rw [hplen] at hocc
      obtain ⟨hstart, -, -⟩ := cf_of_patWord_occ hirr hw P b a v hv hocc
      have hn1 : 1 ≤ runIdx w P + 1 := by omega
      have hlow : lrPos w 1 ≤ lrPos w (runIdx w P + 1) := hmono.monotone hn1
      have hnM : runIdx w P + 1 ≤ M := by
        by_contra hcon
        have : M + 1 ≤ runIdx w P + 1 := by omega
        have := hmono.monotone this
        omega
      have hup : lrPos w (runIdx w P + 1) ≤ lrPos w M := hmono.monotone hnM
      rcases lt_or_ge P (lrPos w M - 1) with hlt | hge
      · exact Or.inl ⟨⟨by omega, hlt⟩, by rw [hplen]; exact hocc⟩
      · exact Or.inr (by omega)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((Finset.Ico (lrPos w 1 - 1) (lrPos w M - 1)).filter
        (fun P => (List.range' P p.length).map (lrExpand w) = p))
      ({lrPos w M - 1} : Finset ℕ)
    simp only [Finset.card_singleton] at h2
    exact le_trans h1 h2
  · refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro P hP
    simp only [Finset.mem_Ico] at hP ⊢
    exact ⟨Nat.zero_le _, by omega⟩

end Window

/-! ## The CF side: dropping index `0` and splitting by parity -/

open scoped Classical in
lemma card_range_split (M : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Ico 1 M).filter Q).card ≤ ((Finset.range M).filter Q).card ∧
      ((Finset.range M).filter Q).card ≤ ((Finset.Ico 1 M).filter Q).card + 1 := by
  constructor
  · refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro n hn
    simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
    omega
  · have hsub : (Finset.range M).filter Q
        ⊆ ((Finset.Ico 1 M).filter Q) ∪ ({0} : Finset ℕ) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
        Finset.mem_singleton] at hn ⊢
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Or.inr rfl
      · exact Or.inl ⟨⟨hpos, hn.1⟩, hn.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.Ico 1 M).filter Q) ({0} : Finset ℕ)
    simp only [Finset.card_singleton] at h2
    exact le_trans h1 h2

open scoped Classical in
lemma card_parity_split (S : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ b : Bool, (S.filter (fun n => decide (n % 2 = 0) = b ∧ Q n)).card = (S.filter Q).card := by
  rw [Fintype.sum_bool]
  have hT : S.filter (fun n => decide (n % 2 = 0) = true ∧ Q n)
      = (S.filter Q).filter (fun n => n % 2 = 0) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro n _
    simp [and_comm]
  have hF : S.filter (fun n => decide (n % 2 = 0) = false ∧ Q n)
      = (S.filter Q).filter (fun n => ¬ (n % 2 = 0)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro n _
    simp [and_comm]
  rw [hT, hF]
  exact Finset.card_filter_add_card_filter_not _

/-! ## The leading run is shorter than `D` -/

lemma headRun_le (hD : 0 < D) (x : ℝ) : headRun D x ≤ D := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hlt : (D : ℝ) * Int.fract x < D := by
    have h1 := Int.fract_lt_one x
    nlinarith
  have hfl : ⌊(D : ℝ) * Int.fract x⌋ < (D : ℤ) := by
    refine Int.floor_lt.mpr ?_
    simpa using hlt
  have := Int.toNat_le_toNat hfl.le
  simpa [headRun] using Int.toNat_le_toNat (show ⌊(D:ℝ) * Int.fract x⌋ ≤ (D : ℤ) from hfl.le)

/-! ## One parity: the letter word's occurrence count is the run window's pattern card -/

section Bridge

variable (hD : 0 < D) {x : ℝ} (hirr : Irrational x) (hD1 : 1 ≤ D)

open scoped Classical in
include hirr hD1 in
/-- **The letter-level bridge.**  For one parity, the pattern card over the run window of the
image differs from the emitted word's occurrence count by at most `1 + D + |patWord|`. -/
lemma letter_bridge (b : Bool) (a : ℕ) (v : List ℕ) (hv : ∀ e ∈ a :: v, 1 ≤ e) (n : ℕ) :
    patCard (lrExpand (imgOf D x)) (patWord b (a :: v))
        (lrPos (imgOf D x) 1 - 1) (lrPos (imgOf D x) (runClock hD x n) - 1)
      ≤ countOccurrences (patN b (a :: v))
          (outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n)
        + (1 + D + ((a :: v).sum + 2)) ∧
    countOccurrences (patN b (a :: v))
        (outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n)
      ≤ patCard (lrExpand (imgOf D x)) (patWord b (a :: v))
          (lrPos (imgOf D x) 1 - 1) (lrPos (imgOf D x) (runClock hD x n) - 1)
        + (1 + D + ((a :: v).sum + 2)) := by
  obtain ⟨hiimg, h01img⟩ := irrational_imgOf (D := D) (x := x) hirr hD1
  set u : List ℕ := a :: v with hu
  set z : ℝ := (D : ℝ) * Int.fract x with hz
  have hz0 : 0 ≤ z := by
    have := Int.fract_nonneg x
    positivity
  have hfz : Int.fract z = imgOf D x := fract_mul_fract D x
  set k₀ : ℕ := headRun D x with hk
  have hkz : ⌊z⌋.toNat = k₀ := rfl
  set N : ℕ := letterLen hD x n with hN
  set p : List Bool := patWord b u with hp
  have hplen : p.length = u.sum + 2 := patWord_length b u
  -- the emitted word, as a mapped range
  have hword : outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n
      = (List.range N).map (fun j => encLetter (lrExpand z j)) := by
    rw [outWord_lrOutN, lrWord_eq_map hD hirr n, List.map_map]
    rfl
  -- link 1: `countOccurrences` vs `occStart`
  have hL1 := countOccurrences_le_occStart (patN b u) (by
      intro hcon
      have : (patN b u).length = 0 := by rw [hcon]; simp
      rw [patN_length] at this
      simp [hu] at this) (fun j => encLetter (lrExpand z j)) N
  have hL2 := occStart_le_countOccurrences_add (patN b u) (by
      intro hcon
      have : (patN b u).length = 0 := by rw [hcon]; simp
      rw [patN_length] at this
      simp [hu] at this) (fun j => encLetter (lrExpand z j)) N
  rw [patN_length] at hL2
  -- link 2: `occStart` IS the pattern card on `[0, N)`
  have hL3 : occStart (patN b u) (fun j => encLetter (lrExpand z j)) N
      = patCard (lrExpand z) p 0 N := occStart_patN_eq (lrExpand z) b u N
  -- link 3: trimming the leading run
  obtain ⟨hL4, hL5⟩ := patCard_zero_le (lrExpand z) p k₀ N
  -- link 4: the shift
  have hL6 : patCard (lrExpand z) p k₀ N = patCard (lrExpand (imgOf D x)) p 0 (N - k₀) := by
    rw [← hfz, ← hkz]
    exact patCard_shift hz0 p N
  -- link 5: the run window
  have hrc : runClock hD x n = runIdx (imgOf D x) (N - k₀) := rfl
  obtain ⟨hL7, hL8⟩ := patCard_window hiimg h01img b a v hv (N - k₀)
  rw [← hp] at hL7 hL8
  rw [← hrc] at hL7 hL8
  have hkD : k₀ ≤ D := headRun_le hD x
  rw [hword]
  omega

end Bridge

/-! ## The CF side, assembled -/

section CFSide

variable {w : ℝ} (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1)

open scoped Classical in
include hirr hw in
/-- **The CF side.**  The image's start-position occurrence count over `[0, M)` is the sum over
the two parities of the pattern card on the run window, up to the single index `0`. -/
lemma cf_side (a : ℕ) (v : List ℕ) (hv : ∀ e ∈ a :: v, 1 ≤ e) (M : ℕ) :
    occStart (a :: v) (cfDigit w) M
        ≤ (patCard (lrExpand w) (patWord true (a :: v)) (lrPos w 1 - 1) (lrPos w M - 1)
          + patCard (lrExpand w) (patWord false (a :: v)) (lrPos w 1 - 1) (lrPos w M - 1)) + 1 ∧
      (patCard (lrExpand w) (patWord true (a :: v)) (lrPos w 1 - 1) (lrPos w M - 1)
        + patCard (lrExpand w) (patWord false (a :: v)) (lrPos w 1 - 1) (lrPos w M - 1))
        ≤ occStart (a :: v) (cfDigit w) M := by
  set u : List ℕ := a :: v with hu
  set Q : ℕ → Prop := fun n => ∀ i, i < u.length → cfDigit w (n + i) = u[i]! with hQ
  have hocc : occStart u (cfDigit w) M = ((Finset.range M).filter Q).card := by
    rw [occStart]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro n _
    exact match_iff (cfDigit w) u n
  obtain ⟨hs1, hs2⟩ := card_range_split M Q
  have hpar := card_parity_split (Finset.Ico 1 M) Q
  rw [Fintype.sum_bool] at hpar
  have hb : ∀ b : Bool,
      ((Finset.Ico 1 M).filter (fun n => decide (n % 2 = 0) = b ∧ Q n)).card
        = patCard (lrExpand w) (patWord b u) (lrPos w 1 - 1) (lrPos w M - 1) := by
    intro b
    rw [patCard, patWord_length]
    exact card_cf_eq_card_patWord hirr hw b a v hv M
  rw [hb true, hb false] at hpar
  omega

end CFSide

/-! ## The run clock is monotone unconditionally -/

/-- `runIdx` is `Nat.findGreatest` of a predicate that only weakens as the position grows, with
a bound that only grows — so it is monotone for **every** `w`, irrational or not.  This is what
lets the run clock be handed to `mobiusUniformFreq_of_runClock`, whose `hmono` is unconditional. -/
lemma runIdx_mono' (w : ℝ) : Monotone (runIdx w) := by
  classical
  intro P P' h
  exact Nat.findGreatest_mono (P := fun n => lrPos w n ≤ P) (Q := fun n => lrPos w n ≤ P')
    (fun n hn => le_trans hn h) h

lemma runClock_mono' (hD : 0 < D) (x : ℝ) : Monotone (runClock hD x) := by
  intro n n' h
  refine runIdx_mono' _ ?_
  have := letterLen_mono hD x h
  omega

/-! ## `hcount` -/

section Count

variable (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)

open scoped Classical in
/-- **The whole bookkeeping, in one bounded difference.**  The image's CF-occurrence count
sampled at the run clock differs from the two parities' letter-level occurrence counts by an
`x`- and `n`-independent constant. -/
theorem cfCount_sub_letters_bound {x : ℝ} (hirr : Irrational x)
    (a : ℕ) (v : List ℕ) (hv : ∀ e ∈ a :: v, 1 ≤ e) (n : ℕ) :
    |cfCount (a :: v) (imgOf D x) (runClock hD x n)
        - (((countOccurrences (patN true (a :: v))
              (outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n) : ℕ) : ℝ)
          + ((countOccurrences (patN false (a :: v))
              (outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n) : ℕ) : ℝ))|
      ≤ (((a :: v).length + 1 + 2 * (1 + D + ((a :: v).sum + 2)) : ℕ) : ℝ) := by
  have hD1 : 1 ≤ D := hD
  obtain ⟨hiimg, h01img⟩ := irrational_imgOf (D := D) (x := x) hirr hD1
  have hune : (a :: v) ≠ [] := by simp
  -- A-side
  have hA1 := countOccurrences_le_occStart (a :: v) hune (cfDigit (imgOf D x))
    (runClock hD x n)
  have hA2 := occStart_le_countOccurrences_add (a :: v) hune (cfDigit (imgOf D x))
    (runClock hD x n)
  obtain ⟨hA3, hA4⟩ := cf_side hiimg h01img a v hv (runClock hD x n)
  -- B-side, one parity at a time
  obtain ⟨hB1, hB2⟩ := letter_bridge hD hirr hD1 true a v hv n
  obtain ⟨hB3, hB4⟩ := letter_bridge hD hirr hD1 false a v hv n
  set u : List ℕ := a :: v with hu
  set M : ℕ := runClock hD x n with hM
  set img : ℝ := imgOf D x with himg
  set W : List ℕ := outWord (lrDelta hD) (lrOutN hD) (startState hD) (Int.fract x) n with hW
  rw [abs_le]
  have hkey : countOccurrences u ((List.range M).map (cfDigit img))
        ≤ (countOccurrences (patN true u) W + countOccurrences (patN false u) W)
          + (u.length + 1 + 2 * (1 + D + (u.sum + 2))) ∧
      (countOccurrences (patN true u) W + countOccurrences (patN false u) W)
        ≤ countOccurrences u ((List.range M).map (cfDigit img))
          + (u.length + 1 + 2 * (1 + D + (u.sum + 2))) := by
    constructor <;> omega
  obtain ⟨hk1, hk2⟩ := hkey
  have hc1 : ((countOccurrences u ((List.range M).map (cfDigit img)) : ℕ) : ℝ)
      ≤ ((countOccurrences (patN true u) W + countOccurrences (patN false u) W
          + (u.length + 1 + 2 * (1 + D + (u.sum + 2))) : ℕ) : ℝ) := Nat.cast_le.mpr hk1
  have hc2 : ((countOccurrences (patN true u) W + countOccurrences (patN false u) W : ℕ) : ℝ)
      ≤ ((countOccurrences u ((List.range M).map (cfDigit img))
          + (u.length + 1 + 2 * (1 + D + (u.sum + 2))) : ℕ) : ℝ) := Nat.cast_le.mpr hk2
  rw [cfCount]
  push_cast at hc1 hc2 ⊢
  constructor <;> linarith

end Count

/-! ## `hcount`, and the capstone -/

/-- **`hcount` for the Raney machine.**  The image's CF-occurrence count sampled at the run
clock has an `x`-independent Cesàro limit: the sum of the two parities' letter-level limits. -/
theorem exists_tendsto_cfCount_runClock (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (a : ℕ) (v : List ℕ) (hv : ∀ e ∈ a :: v, 1 ≤ e) :
    ∃ L : ℝ, ∀ x : ℝ, IsCFNormal (Int.fract x) →
      Tendsto (fun n => cfCount (a :: v) (imgOf D x) (runClock hD x n) / n) atTop (nhds L) := by
  have ha : 1 ≤ a := hv a (by simp)
  obtain ⟨LT, hLT⟩ := exists_tendsto_countOccurrences_patN D hD a v ha true
  obtain ⟨LF, hLF⟩ := exists_tendsto_countOccurrences_patN D hD a v ha false
  refine ⟨LT + LF, fun x hx => ?_⟩
  have hirr : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  obtain ⟨hif, h01f⟩ := fract_irr hirr
  have hT := hLT (Int.fract x) hx h01f
  have hF := hLF (Int.fract x) hx h01f
  refine cesaro_of_bounded_diff
    (C := (((a :: v).length + 1 + 2 * (1 + D + ((a :: v).sum + 2)) : ℕ) : ℝ))
    (fun n => cfCount_sub_letters_bound D hD hirr a v hv n) ?_
  refine (hT.add hF).congr ?_
  intro n
  ring

/-- **`ScaleUniformFreq`**: for prime `D`, the map `x ↦ D·x` has `x`-independent output window
frequencies.  Every hypothesis of `mobiusUniformFreq_of_runClock` is now a theorem about the
concrete Raney machine. -/
theorem scaleUniformFreq_holds : Literature.ScaleUniformFreq := by
  intro D hp
  haveI : Fact (Nat.Prime D) := ⟨hp⟩
  have hD : 0 < D := hp.pos
  have harg : ∀ x : ℝ,
      (((D : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ)) / (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) = (D : ℝ) * x := by
    intro x; push_cast; ring
  refine mobiusUniformFreq_of_runClock (r := runRate D hD) (zero_lt_runRate' D hD)
    (fun x n => runClock hD x n) (fun x => runClock_mono' hD x) (fun x _ hx => ?_)
    (fun w hne hpos => ?_)
  · exact tendsto_runClock_div D hD (Literature.irrational_of_isCFNormal_fract hx) hx
  · obtain ⟨a, v, rfl⟩ : ∃ a v, w = a :: v := by
      cases w with
      | nil => exact absurd rfl hne
      | cons a v => exact ⟨a, v, rfl⟩
    obtain ⟨L, hL⟩ := exists_tendsto_cfCount_runClock D hD a v hpos
    exact ⟨L, fun x _ hx => by simpa only [harg, imgOf] using hL x hx⟩

end NormalNumbers.VandeheyLR
