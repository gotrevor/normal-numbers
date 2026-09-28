/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyLRRuns

/-!
# The `L/R` pattern of a CF word

`VandeheyLRRuns` says the runs of the `L/R` expansion of `w` are the CF digits of `w`, with the
letter of run `n` determined by the parity of `n`.  So a CF word `v = (v₀,…,v_{k-1})` occurring
at CF index `n` shows up in the `L/R` stream as the word

  `runWord b v = b^{v₀} (!b)^{v₁} b^{v₂} ⋯`,  `b` = the parity letter of run `n`,

and the occurrence is of a *maximal* run block exactly when the two bordering letters are the
opposite ones.  Those are FORCED, so the pattern to look for is the single word

  `patWord b v = (!b) :: runWord b v ++ [xorB b k]`.

`patWord_alternation` records the one fact the trigger bound needs — `patWord` alternates at
index `0` — and `lrExpand_patWord` is the forward translation: if the CF digits of `w` from `n`
on agree with `v`, the stream reads `patWord` at `lrPos w n - 1`.
-/

namespace NormalNumbers.VandeheyLR

/-! ## The pattern -/

/-- The letter of run `i` when run `0` carries `b`. -/
def xorB (b : Bool) (i : ℕ) : Bool := if i % 2 = 0 then b else !b

@[simp] lemma xorB_zero (b : Bool) : xorB b 0 = b := by simp [xorB]

lemma xorB_succ (b : Bool) (i : ℕ) : xorB b (i + 1) = xorB (!b) i := by
  rcases Nat.even_or_odd i with he | ho
  · have h : i % 2 = 0 := Nat.even_iff.mp he
    simp [xorB, h, Nat.add_mod]
  · have h : i % 2 = 1 := Nat.odd_iff.mp ho
    simp [xorB, h, Nat.add_mod]

/-- The alternating run block of a CF word: `b^{v₀} (!b)^{v₁} b^{v₂} ⋯`. -/
def runWord : Bool → List ℕ → List Bool
  | _, [] => []
  | b, a :: v => List.replicate a b ++ runWord (!b) v

@[simp] lemma runWord_nil (b : Bool) : runWord b [] = [] := rfl

lemma runWord_cons (b : Bool) (a : ℕ) (v : List ℕ) :
    runWord b (a :: v) = List.replicate a b ++ runWord (!b) v := rfl

lemma runWord_length : ∀ (b : Bool) (v : List ℕ), (runWord b v).length = v.sum
  | _, [] => by simp
  | b, (a :: v) => by simp [runWord_cons, runWord_length (!b) v]

/-- Where run `i` of the block begins. -/
def vPos (v : List ℕ) (i : ℕ) : ℕ := (v.take i).sum

@[simp] lemma vPos_zero (v : List ℕ) : vPos v 0 = 0 := by simp [vPos]

lemma vPos_cons_succ (a : ℕ) (v : List ℕ) (i : ℕ) : vPos (a :: v) (i + 1) = a + vPos v i := by
  simp [vPos]

lemma vPos_length (v : List ℕ) : vPos v v.length = v.sum := by simp [vPos]

/-- **The letters of the block.**  Position `vPos v i + r` of `runWord b v`, for `r` inside
run `i`, carries the letter `xorB b i`. -/
lemma runWord_getElem? : ∀ (b : Bool) (v : List ℕ) (i r : ℕ), i < v.length → r < v[i]! →
    (runWord b v)[vPos v i + r]? = some (xorB b i)
  | _, [], i, r, hi, _ => by simp at hi
  | b, (a :: v), 0, r, _, hr => by
      have hra : r < a := by simpa using hr
      rw [vPos_zero, Nat.zero_add, runWord_cons,
        List.getElem?_append_left (by simpa using hra), List.getElem?_replicate_of_lt hra,
        xorB_zero]
  | b, (a :: v), (i + 1), r, hi, hr => by
      have hi' : i < v.length := by simpa using hi
      have hr' : r < v[i]! := by simpa using hr
      rw [vPos_cons_succ, runWord_cons, show a + vPos v i + r = a + (vPos v i + r) from by omega,
        List.getElem?_append_right (by simp), xorB_succ]
      simpa using runWord_getElem? (!b) v i r hi' hr'

/-- The pattern: the block, with the two bordering letters that force its runs to be maximal. -/
def patWord (b : Bool) (v : List ℕ) : List Bool :=
  (!b) :: (runWord b v ++ [xorB b v.length])

lemma patWord_length (b : Bool) (v : List ℕ) : (patWord b v).length = v.sum + 2 := by
  simp [patWord, runWord_length]

/-- **The pattern alternates at index `0`.**  This is precisely the hypothesis of
`VandeheyLRTrigger.lr_trigger_bounds`: a genuine CF word (first digit `≥ 1`) has a border letter
different from its first run's letter, so the encoded pattern is non-constant. -/
lemma patWord_alternation (b : Bool) (a : ℕ) (v : List ℕ) (ha : 1 ≤ a) :
    (patWord b (a :: v))[0]? ≠ (patWord b (a :: v))[1]? := by
  have h1 : (patWord b (a :: v))[0]? = some (!b) := by simp [patWord]
  have h2 : (patWord b (a :: v))[1]? = some b := by
    have := runWord_getElem? b (a :: v) 0 0 (by simp) (by simp; omega)
    simp only [vPos_zero, Nat.add_zero, xorB_zero] at this
    simp only [patWord, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [runWord_length]; simp; omega)]
    simpa using this
  rw [h1, h2]
  simp

/-! ## Parity bookkeeping -/

lemma xorB_decide (n i : ℕ) : xorB (decide (n % 2 = 0)) i = decide ((n + i) % 2 = 0) := by
  rcases Nat.even_or_odd i with he | ho
  · have hi : i % 2 = 0 := Nat.even_iff.mp he
    rw [xorB, if_pos hi]
    exact decide_eq_decide.mpr (by omega)
  · have hi : i % 2 = 1 := Nat.odd_iff.mp ho
    rw [xorB, if_neg (by omega)]
    rcases Nat.even_or_odd n with hn | hn
    · have h0 : n % 2 = 0 := Nat.even_iff.mp hn
      rw [decide_eq_true h0, Bool.not_true, decide_eq_false (by omega)]
    · have h0 : n % 2 = 1 := Nat.odd_iff.mp hn
      rw [decide_eq_false (by omega : ¬ n % 2 = 0), Bool.not_false,
        decide_eq_true (by omega : (n + i) % 2 = 0)]

/-! ## The forward translation

If the CF digits of `w` from index `n` on agree with `v`, then the `L/R` stream reads
`runWord` at `lrPos w n`, and `patWord` one position earlier.  The proof is a structural
induction on `v`: one run at a time, `lrPos w (n+1) = lrPos w n + cfDigit w n`. -/

section Translate

variable {w : ℝ} (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1)

/-- Peeling the first position of a mapped range. -/
lemma map_range'_succ_left (f : ℕ → Bool) (s m : ℕ) :
    (List.range' s (m + 1)).map f = f s :: (List.range' (s + 1) m).map f := by
  rw [List.range'_succ, List.map_cons]

/-- Peeling the last position of a mapped range. -/
lemma map_range'_snoc (f : ℕ → Bool) (s m : ℕ) :
    (List.range' s (m + 1)).map f = (List.range' s m).map f ++ [f (s + m)] := by
  rw [← List.range'_append_1 (s := s) (m := m) (n := 1), List.map_append]
  simp [List.range'_succ]

/-- Matching digits push `lrPos` forward by the word's sum.  No irrationality needed. -/
lemma lrPos_add_of_match : ∀ (v : List ℕ) (n : ℕ),
    (∀ i, i < v.length → cfDigit w (n + i) = v[i]!) →
    lrPos w (n + v.length) = lrPos w n + v.sum
  | [], n, _ => by simp
  | (a :: v), n, hm => by
      have ha : cfDigit w n = a := by simpa using hm 0 (by simp)
      have hm' : ∀ i, i < v.length → cfDigit w (n + 1 + i) = v[i]! := by
        intro i hi
        have h := hm (i + 1) (by simpa using hi)
        rw [show n + (i + 1) = n + 1 + i from by omega] at h
        simpa using h
      rw [show n + (a :: v).length = (n + 1) + v.length from by simp [Nat.add_comm]; omega,
        lrPos_add_of_match v (n + 1) hm', lrPos_succ, ha, List.sum_cons]
      omega

include hirr hw

omit hirr hw in
/-- The parity letter flips from one run to the next. -/
lemma decide_succ_parity (n : ℕ) :
    decide ((n + 1) % 2 = 0) = !(decide (n % 2 = 0)) := by
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.mp he
    rw [decide_eq_true h0, Bool.not_true, decide_eq_false (by omega)]
  · have h0 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [decide_eq_false (by omega : ¬ n % 2 = 0), Bool.not_false,
      decide_eq_true (by omega : (n + 1) % 2 = 0)]

/-- Every position of run `n` carries the run's letter. -/
lemma map_range'_lrPos_eq_replicate (n : ℕ) :
    (List.range' (lrPos w n) (cfDigit w n)).map (lrExpand w)
      = List.replicate (cfDigit w n) (decide (n % 2 = 0)) := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro x hx
  simp only [List.mem_map, List.mem_range'_1] at hx
  obtain ⟨P, ⟨hP1, hP2⟩, rfl⟩ := hx
  have hkey := lrExpand_run w hirr hw n (P - lrPos w n) (by omega)
  rw [show lrPos w n + (P - lrPos w n) = P from by omega] at hkey
  rw [hkey]

/-- **The block translation**: matching CF digits from `n` on make the stream read `runWord`. -/
theorem map_range'_eq_runWord : ∀ (v : List ℕ) (n : ℕ),
    (∀ i, i < v.length → cfDigit w (n + i) = v[i]!) →
    (List.range' (lrPos w n) v.sum).map (lrExpand w) = runWord (decide (n % 2 = 0)) v
  | [], n, _ => by simp
  | (a :: v), n, hm => by
      have ha : cfDigit w n = a := by simpa using hm 0 (by simp)
      have hnext : lrPos w (n + 1) = lrPos w n + cfDigit w n := lrPos_succ w n
      have hm' : ∀ i, i < v.length → cfDigit w (n + 1 + i) = v[i]! := by
        intro i hi
        have h := hm (i + 1) (by simpa using hi)
        rw [show n + (i + 1) = n + 1 + i from by omega] at h
        simpa using h
      rw [List.sum_cons, ← ha, ← List.range'_append_1, List.map_append,
        map_range'_lrPos_eq_replicate hirr hw n, ← hnext,
        map_range'_eq_runWord v (n + 1) hm', runWord_cons, ha,
        decide_succ_parity n]

/-- **The pattern translation.**  Matching CF digits from index `n ≥ 1` force the stream to read
`patWord` at `lrPos w n - 1`: the block, bordered by the two opposite letters that make its runs
maximal. -/
theorem map_range'_eq_patWord (v : List ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hm : ∀ i, i < v.length → cfDigit w (n + i) = v[i]!) :
    (List.range' (lrPos w n - 1) (v.sum + 2)).map (lrExpand w)
      = patWord (decide (n % 2 = 0)) v := by
  have hpos : 1 ≤ lrPos w n := le_trans hn (le_lrPos hirr hw n)
  have hP1 : lrPos w n - 1 + 1 = lrPos w n := by omega
  -- the border letter before the block
  have hhead : lrExpand w (lrPos w n - 1) = !(decide (n % 2 = 0)) := by
    have hprev : lrPos w (n - 1) < lrPos w n := by
      have h := lrPos_lt_succ hirr hw (n - 1)
      rwa [show n - 1 + 1 = n from by omega] at h
    have hidx : runIdx w (lrPos w n - 1) = n - 1 := by
      refine runIdx_eq hirr hw (n - 1) _ (by omega) ?_
      rw [show n - 1 + 1 = n from by omega]
      omega
    rw [lrExpand_eq_runIdx_parity hirr hw, hidx]
    have h := decide_succ_parity (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h
    rw [h, Bool.not_not]
  -- the border letter after the block
  have hlast : lrExpand w (lrPos w n + v.sum) = xorB (decide (n % 2 = 0)) v.length := by
    have hlrpos : lrPos w (n + v.length) = lrPos w n + v.sum := lrPos_add_of_match v n hm
    rw [← hlrpos, lrExpand_eq_runIdx_parity hirr hw,
      runIdx_eq hirr hw _ _ le_rfl (lrPos_lt_succ hirr hw _), xorB_decide]
  have hblock := map_range'_eq_runWord hirr hw v n hm
  show (List.range' (lrPos w n - 1) ((v.sum + 1) + 1)).map (lrExpand w) = _
  rw [map_range'_succ_left, hP1, map_range'_snoc, hblock, hhead, hlast, patWord]

end Translate

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms runWord_length
#print axioms runWord_getElem?
#print axioms patWord_length
#print axioms patWord_alternation
#print axioms xorB_decide
#print axioms map_range'_eq_runWord
#print axioms map_range'_eq_patWord
end
