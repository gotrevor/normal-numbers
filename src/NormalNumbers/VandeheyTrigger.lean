/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyOutputWord

/-!
# The trigger family of an output word

`VandeheyOutputWord` reduces Vandehey's §5-§6 to one identity: the number of occurrences of `v`
starting in the block emitted at input digit `i` — `fireOut v x i` — must be a function of the
input *window* at `i` and the automaton *state* at `i` alone.  This file supplies the run-from-a-
state layer that makes that identity provable, and the trigger family itself.

* `blocksOf` — the output emitted by running a finite input word from a given state.  It is
  additive (`blocksOf_append`), which is the whole point: the output of the first `i + j` input
  digits is the output of the first `i`, followed by `blocksOf` of the length-`j` window from the
  state at `i` (`outWord_add`).  So everything after position `i` is a function of
  `(stateAt i, digits from i on)`, with no reference to the past.
* `occIn v t q` — occurrences of `v` starting in the FIRST block of the run of `q` from `t` and
  completed within the run.  Monotone in `q` (`occIn_mono_concat`), because extending the input
  only appends output.
* `kOut v q t` — the trigger multiplicity, defined as the INCREMENT
  `occIn v t q - occIn v t q.dropLast`.  Telescoping (`sum_kOut_eq`) turns the truncated
  positionwise sum `fireAt` of `VandeheyOutputFreq` into `occIn` at the truncation length, with
  no minimality bookkeeping anywhere.
-/

namespace NormalNumbers.VandeheyOut

open Filter VandeheyAut

variable {S : Type*} [DecidableEq S]

/-! ## Running the transducer from a state -/

/-- The output emitted by reading the input word `q` starting from state `t`. -/
def blocksOf (δ : S → ℕ → S) (out : S → ℕ → List ℕ) : S → List ℕ → List ℕ
  | _, [] => []
  | t, a :: q => out t a ++ blocksOf δ out (δ t a) q

@[simp] lemma blocksOf_nil (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (t : S) :
    blocksOf δ out t [] = [] := rfl

@[simp] lemma blocksOf_cons (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (t : S) (a : ℕ)
    (q : List ℕ) : blocksOf δ out t (a :: q) = out t a ++ blocksOf δ out (δ t a) q := rfl

/-- **Additivity**: running `u` then `w` emits `u`'s output followed by `w`'s output from the
state `u` left the automaton in.  This is the only structural fact the trigger identity needs. -/
lemma blocksOf_append (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (t : S) (u w : List ℕ) :
    blocksOf δ out t (u ++ w) = blocksOf δ out t u ++ blocksOf δ out (runState δ t u) w := by
  induction u generalizing t with
  | nil => simp
  | cons a u ih => simp [ih, List.append_assoc]

lemma blocksOf_concat (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (t : S) (q : List ℕ) (a : ℕ) :
    blocksOf δ out t (q ++ [a]) = blocksOf δ out t q ++ out (runState δ t q) a := by
  simp [blocksOf_append]

lemma cfWord_succ' (x : ℝ) (n : ℕ) : cfWord x (n + 1) = cfWord x n ++ [cfDigit x n] := by
  rw [cfWord_add]
  simp [cfWindow]

/-- The output word is `blocksOf` over the input word. -/
lemma outWord_eq_blocksOf (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (s₀ : S) (x : ℝ) (n : ℕ) :
    outWord δ out s₀ x n = blocksOf δ out s₀ (cfWord x n) := by
  induction n with
  | zero => simp [cfWord]
  | succ n ih =>
    rw [outWord_succ, ih, cfWord_succ', blocksOf_concat, outBlock, stateAt]

/-- **The future is a function of (state, window).**  The output produced by input digits
`i, …, i+j-1` is the run of the length-`j` window from the state at `i`. -/
lemma outWord_add (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (s₀ : S) (x : ℝ) (i j : ℕ) :
    outWord δ out s₀ x (i + j)
      = outWord δ out s₀ x i ++ blocksOf δ out (stateAt δ s₀ x i) (cfWindow x i j) := by
  rw [outWord_eq_blocksOf, outWord_eq_blocksOf, cfWord_add, blocksOf_append, stateAt]

/-! ## The trigger family

`occIn v t q` counts the occurrences of `v` that START in the first block of the run of `q` from
`t` and are COMPLETED by the end of that run.  It is monotone in `q`, so its increments are a
well-defined nonnegative multiplicity — the trigger family — and they telescope. -/

variable (δ : S → ℕ → S) (out : S → ℕ → List ℕ)

/-- Occurrences of `v` starting in the first emitted block and completed within the run of `q`. -/
noncomputable def occIn (v : List ℕ) (t : S) (q : List ℕ) : ℕ :=
  ((Finset.range (blocksOf δ out t (q.take 1)).length).filter
    (fun p => p + v.length ≤ (blocksOf δ out t q).length ∧
      v = ((blocksOf δ out t q).drop p).take v.length)).card

@[simp] lemma occIn_nil (v : List ℕ) (t : S) : occIn δ out v t [] = 0 := by
  simp [occIn]

/-- Extending the input only appends output, so no completed occurrence is lost. -/
lemma occIn_mono_concat (v : List ℕ) (t : S) (q : List ℕ) (a : ℕ) :
    occIn δ out v t q ≤ occIn δ out v t (q ++ [a]) := by
  classical
  rcases eq_or_ne q [] with rfl | hq
  · simp
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  obtain ⟨hlt, hfit, hval⟩ := hp
  have htake : (q ++ [a]).take 1 = q.take 1 := by
    rcases q with _ | ⟨b, q⟩
    · exact absurd rfl hq
    · simp
  have hB : blocksOf δ out t (q ++ [a])
      = blocksOf δ out t q ++ out (runState δ t q) a := blocksOf_concat δ out t q a
  refine ⟨by rwa [htake], ?_, ?_⟩
  · rw [hB, List.length_append]; omega
  · rw [hB, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
      simp only [List.length_drop]; omega)]
    exact hval

/-- **The trigger multiplicity**: the occurrences that the last input digit of `q` is what
completes.  Nonnegative by `occIn_mono_concat`, and it telescopes by construction. -/
noncomputable def kOut (v : List ℕ) (q : List ℕ) (t : S) : ℕ :=
  occIn δ out v t q - occIn δ out v t q.dropLast

lemma cfWindow_succ (x : ℝ) (i j : ℕ) :
    cfWindow x i (j + 1) = cfWindow x i j ++ [cfDigit x (i + j)] := by
  simp [cfWindow, List.range_succ]

/-- **Telescoping.**  The truncated positionwise sum of `VandeheyOutputFreq.fireAt` is exactly
`occIn` at the truncation length: no minimality condition on triggers is needed. -/
lemma sum_kOut_eq (v : List ℕ) (x : ℝ) (s₀ : S) (i J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, kOut δ out v (cfWindow x i j) (stateAt δ s₀ x i)
      = occIn δ out v (stateAt δ s₀ x i) (cfWindow x i J) := by
  induction J with
  | zero => simp [cfWindow]
  | succ J ih =>
    have hdrop : (cfWindow x i (J + 1)).dropLast = cfWindow x i J := by
      rw [cfWindow_succ, List.dropLast_concat]
    have hmono : occIn δ out v (stateAt δ s₀ x i) (cfWindow x i J)
        ≤ occIn δ out v (stateAt δ s₀ x i) (cfWindow x i (J + 1)) := by
      rw [cfWindow_succ]
      exact occIn_mono_concat δ out v _ _ _
    have hins : Finset.Icc 1 (J + 1) = insert (J + 1) (Finset.Icc 1 J) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), ih, kOut, hdrop]
    omega


end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms blocksOf_append
#print axioms outWord_eq_blocksOf
#print axioms outWord_add
#print axioms occIn_mono_concat
#print axioms sum_kOut_eq
end
