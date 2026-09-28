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

/-- The block together with the border letter that closes it. -/
def patBody (b : Bool) (v : List ℕ) : List Bool := runWord b v ++ [xorB b v.length]

@[simp] lemma patBody_nil (b : Bool) : patBody b [] = [b] := by simp [patBody]

/-- **The structural identity.**  `patBody` of a cons is a run followed by `patBody` of the
tail with the letter flipped — so the border letter of the tail IS the first letter of the run
after it.  This is what makes both directions of the translation one-run inductions. -/
lemma patBody_cons (b : Bool) (a : ℕ) (v : List ℕ) :
    patBody b (a :: v) = List.replicate a b ++ patBody (!b) v := by
  rw [patBody, patBody, runWord_cons, List.append_assoc]
  congr 2
  rw [List.length_cons, xorB_succ]

lemma patBody_length (b : Bool) (v : List ℕ) : (patBody b v).length = v.sum + 1 := by
  simp [patBody, runWord_length]

/-- The first letter of `patBody` is the first run's letter (or, on the empty word, the border). -/
lemma patBody_getElem?_zero (b : Bool) (v : List ℕ) (hv : ∀ x ∈ v.take 1, 1 ≤ x) :
    (patBody b v)[0]? = some b := by
  cases v with
  | nil => simp
  | cons a v =>
    have ha : 1 ≤ a := hv a (by simp)
    rw [patBody_cons, List.getElem?_append_left (by simp; omega)]
    exact List.getElem?_replicate_of_lt (by omega)

/-- The pattern: the block, with the two bordering letters that force its runs to be maximal. -/
def patWord (b : Bool) (v : List ℕ) : List Bool := (!b) :: patBody b v

lemma patWord_length (b : Bool) (v : List ℕ) : (patWord b v).length = v.sum + 2 := by
  simp [patWord, patBody_length]

lemma patWord_getElem?_zero (b : Bool) (v : List ℕ) : (patWord b v)[0]? = some (!b) := by
  simp [patWord]

lemma patWord_getElem?_one (b : Bool) (v : List ℕ) (hv : ∀ x ∈ v.take 1, 1 ≤ x) :
    (patWord b v)[1]? = some b := by
  simp only [patWord, List.getElem?_cons_succ]
  exact patBody_getElem?_zero b v hv

/-- **The pattern alternates at index `0`.**  This is precisely the hypothesis of
`VandeheyLRTrigger.lr_trigger_bounds`: a genuine CF word (first digit `≥ 1`) has a border letter
different from its first run's letter, so the encoded pattern is non-constant. -/
lemma patWord_alternation (b : Bool) (a : ℕ) (v : List ℕ) (ha : 1 ≤ a) :
    (patWord b (a :: v))[0]? ≠ (patWord b (a :: v))[1]? := by
  have h1 : (patWord b (a :: v))[0]? = some (!b) := patWord_getElem?_zero b (a :: v)
  have h2 : (patWord b (a :: v))[1]? = some b := by
    refine patWord_getElem?_one b (a :: v) ?_
    intro x hx
    simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hx
    omega
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
  rw [map_range'_succ_left, hP1, map_range'_snoc, hblock, hhead, hlast, patWord, patBody]

/-! ### The converse

An occurrence of `patBody` at a run start forces the run lengths, hence the CF digits: the
letters inside a block are constant, so a run cannot end early, and the border letter differs,
so it cannot end late. -/

omit hirr hw in
lemma getElem?_map_range' (f : ℕ → Bool) (s m k : ℕ) (hk : k < m) :
    ((List.range' s m).map f)[k]? = some (f (s + k)) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]
  simp

/-- **The converse translation.**  If the stream reads `patBody` at the start of run `n`, the
next `|v|` CF digits of `w` are exactly `v`. -/
theorem cfDigit_of_map_range'_eq_patBody : ∀ (v : List ℕ) (n : ℕ), (∀ x ∈ v, 1 ≤ x) →
    (List.range' (lrPos w n) (v.sum + 1)).map (lrExpand w) = patBody (decide (n % 2 = 0)) v →
    ∀ i, i < v.length → cfDigit w (n + i) = v[i]!
  | [], n, _, _, i, hi => by simp at hi
  | (a :: v), n, hv, hEq, i, hi => by
      have ha : 1 ≤ a := hv a (by simp)
      have hv' : ∀ x ∈ v, 1 ≤ x := fun x hx => hv x (by simp [hx])
      set b : Bool := decide (n % 2 = 0) with hb
      have hsum : (a :: v).sum + 1 = a + (v.sum + 1) := by simp [List.sum_cons]; omega
      have hbody : patBody b (a :: v) = List.replicate a b ++ patBody (!b) v := patBody_cons b a v
      -- the letters strictly inside the first run
      have hin : ∀ r, r < a → lrExpand w (lrPos w n + r) = b := by
        intro r hr
        have h1 := getElem?_map_range' (lrExpand w) (lrPos w n) ((a :: v).sum + 1) r (by
          rw [hsum]; omega)
        rw [hEq, hbody, List.getElem?_append_left (by simp; omega),
          List.getElem?_replicate_of_lt hr] at h1
        exact (Option.some_inj.mp h1).symm
      -- the border letter just after the first run
      have hborder : lrExpand w (lrPos w n + a) = !b := by
        have h1 := getElem?_map_range' (lrExpand w) (lrPos w n) ((a :: v).sum + 1) a (by
          rw [hsum]; omega)
        rw [hEq, hbody, List.getElem?_append_right (by simp),
          show (List.replicate a b).length = a from by simp, Nat.sub_self,
          patBody_getElem?_zero (!b) v (fun x hx => hv' x (List.mem_of_mem_take hx))] at h1
        exact (Option.some_inj.mp h1).symm
      -- so the first run has length exactly `a`
      have hc : cfDigit w n = a := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- the run ends early: the letter at its end already belongs to run `n+1`
          have hidx : runIdx w (lrPos w n + cfDigit w n) = n + 1 := by
            refine runIdx_eq hirr hw (n + 1) _ (by rw [lrPos_succ]) ?_
            have h2 : lrPos w (n + 1) < lrPos w (n + 1 + 1) := lrPos_lt_succ hirr hw (n + 1)
            rw [lrPos_succ w n] at h2
            exact h2
          have h1 := hin (cfDigit w n) hlt
          rw [lrExpand_eq_runIdx_parity hirr hw, hidx, decide_succ_parity n] at h1
          simp [hb] at h1
        · -- the run ends late: the border letter would still be inside run `n`
          have hidx : runIdx w (lrPos w n + a) = n := by
            refine runIdx_eq hirr hw n _ (by omega) ?_
            rw [lrPos_succ]
            omega
          rw [lrExpand_eq_runIdx_parity hirr hw, hidx] at hborder
          simp [hb] at hborder
      -- recurse on the tail
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simpa using hc
      · have hnext : lrPos w (n + 1) = lrPos w n + a := by rw [lrPos_succ, hc]
        have hsplit : (List.range' (lrPos w (n + 1)) (v.sum + 1)).map (lrExpand w)
            = patBody (decide ((n + 1) % 2 = 0)) v := by
          have h1 : (List.range' (lrPos w n) a).map (lrExpand w)
              ++ (List.range' (lrPos w n + a) (v.sum + 1)).map (lrExpand w)
              = List.replicate a b ++ patBody (!b) v := by
            rw [← List.map_append,
              List.range'_append_1 (s := lrPos w n) (m := a) (n := v.sum + 1), ← hsum, hEq,
              hbody]
          have hlen : ((List.range' (lrPos w n) a).map (lrExpand w)).length
              = (List.replicate a b).length := by simp
          have h2 := (List.append_inj h1 hlen).2
          rw [hnext, h2, decide_succ_parity n]
        have h3 := cfDigit_of_map_range'_eq_patBody v (n + 1) hv' hsplit (i - 1) (by
          simp at hi; omega)
        rw [show n + i = n + 1 + (i - 1) from by omega, h3]
        rcases i with _ | i'
        · omega
        · simp

/-! ### The bijection

Putting the two directions together: for a genuine CF word, the CF occurrences in `[1,N)` and the
`L/R` occurrences of the forced pattern in `[lrPos 1 - 1, lrPos N - 1)` are in bijection, run
start by run start.  Reading the CF-word frequency off the `L/R` word is then a reindexing. -/

/-- **The converse, packaged.**  An occurrence of the pattern at `P` sits at the end of run
`runIdx P`, has the matching parity, and pins the next `|v|` CF digits. -/
theorem cf_of_patWord_occ (P : ℕ) (b : Bool) (a : ℕ) (v : List ℕ) (hv : ∀ x ∈ a :: v, 1 ≤ x)
    (hocc : (List.range' P ((a :: v).sum + 2)).map (lrExpand w) = patWord b (a :: v)) :
    P + 1 = lrPos w (runIdx w P + 1) ∧ decide ((runIdx w P + 1) % 2 = 0) = b ∧
      ∀ i, i < (a :: v).length → cfDigit w (runIdx w P + 1 + i) = (a :: v)[i]! := by
  set u : List ℕ := a :: v with hu
  set n : ℕ := runIdx w P + 1 with hn
  have hhead1 : ∀ x ∈ u.take 1, 1 ≤ x := fun x hx => hv x (List.mem_of_mem_take hx)
  -- the first two letters of the occurrence
  have h0 : lrExpand w P = !b := by
    have h := getElem?_map_range' (lrExpand w) P (u.sum + 2) 0 (by omega)
    rw [hocc, patWord_getElem?_zero] at h
    simpa using (Option.some_inj.mp h).symm
  have h1 : lrExpand w (P + 1) = b := by
    have h := getElem?_map_range' (lrExpand w) P (u.sum + 2) 1 (by omega)
    rw [hocc, patWord_getElem?_one b u hhead1] at h
    exact (Option.some_inj.mp h).symm
  -- so a run ends at `P`
  have hstart : P + 1 = lrPos w n := by
    refine (lrExpand_ne_succ_iff hirr hw P).mp ?_
    rw [h0, h1]
    simp
  -- the parity of that run
  have hpar : decide (n % 2 = 0) = b := by
    have hidx : runIdx w (lrPos w n) = n :=
      runIdx_eq hirr hw n _ le_rfl (lrPos_lt_succ hirr hw n)
    rw [← h1, hstart, lrExpand_eq_runIdx_parity hirr hw, hidx]
  -- and the digits
  refine ⟨hstart, hpar, ?_⟩
  have htail : (List.range' (lrPos w n) (u.sum + 1)).map (lrExpand w) = patBody b u := by
    have hcons : (List.range' P (u.sum + 2)).map (lrExpand w)
        = lrExpand w P :: (List.range' (P + 1) (u.sum + 1)).map (lrExpand w) := by
      show (List.range' P ((u.sum + 1) + 1)).map (lrExpand w) = _
      rw [map_range'_succ_left]
    rw [hcons, patWord] at hocc
    rw [← hstart]
    exact (List.cons_eq_cons.mp hocc).2
  rw [← hpar] at htail
  exact cfDigit_of_map_range'_eq_patBody hirr hw u n hv htail

/-- **The count identity.**  CF occurrences of a genuine word `v` at indices `[1,N)` with run
parity `b` correspond exactly to occurrences of `patWord b v` in the `L/R` stream at positions
`[lrPos 1 - 1, lrPos N - 1)`. -/
theorem card_cf_eq_card_patWord (b : Bool) (a : ℕ) (v : List ℕ) (hv : ∀ x ∈ a :: v, 1 ≤ x)
    (N : ℕ) :
    ((Finset.Ico 1 N).filter (fun n => decide (n % 2 = 0) = b ∧
        ∀ i, i < (a :: v).length → cfDigit w (n + i) = (a :: v)[i]!)).card
      = ((Finset.Ico (lrPos w 1 - 1) (lrPos w N - 1)).filter
          (fun P => (List.range' P ((a :: v).sum + 2)).map (lrExpand w)
            = patWord b (a :: v))).card := by
  classical
  set u : List ℕ := a :: v with hu
  have hmono := lrPos_strictMono hirr hw
  have hpos : ∀ m, 1 ≤ m → 1 ≤ lrPos w m := fun m hm => le_trans hm (le_lrPos hirr hw m)
  refine Finset.card_bij (fun n _ => lrPos w n - 1) ?_ ?_ ?_
  · -- forward
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, hpar, hdig⟩ := hn
    have h1 : lrPos w 1 - 1 ≤ lrPos w n - 1 := by
      have := hmono.monotone hn1
      omega
    have h2 : lrPos w n - 1 < lrPos w N - 1 := by
      have hlt := hmono hnN
      have := hpos n hn1
      omega
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [← hpar]
    exact map_range'_eq_patWord hirr hw u n hn1 hdig
  · -- injective
    intro n hn m hm hEq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn hm
    have h1 := hpos n hn.1.1
    have h2 := hpos m hm.1.1
    exact hmono.injective (by omega)
  · -- surjective
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_Ico] at hP
    obtain ⟨⟨hP1, hP2⟩, hocc⟩ := hP
    obtain ⟨hstart, hpar, hdig⟩ := cf_of_patWord_occ hirr hw P b a v hv hocc
    refine ⟨runIdx w P + 1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, ?_⟩, hpar, hdig⟩
    by_contra hcon
    have hle : N ≤ runIdx w P + 1 := by omega
    have := hmono.monotone hle
    omega

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
#print axioms cfDigit_of_map_range'_eq_patBody
#print axioms cf_of_patWord_occ
#print axioms card_cf_eq_card_patWord
end
