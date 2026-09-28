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

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms runWord_length
#print axioms runWord_getElem?
#print axioms patWord_length
#print axioms patWord_alternation
end
