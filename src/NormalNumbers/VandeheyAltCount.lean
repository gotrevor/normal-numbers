/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyTrigger

/-!
# Occurrences of a non-constant word are counted by alternations

The trigger bound `hK`/`hkK` of `VandeheyAssembly.mobiusUniformFreq_of_transducer` asks for a
uniform bound on the number of occurrences of a fixed word `v` STARTING inside one emitted block.
For the `L/R` transducer the blocks are long (a large ingested digit emits a long run), so no
bound on the block length is available.  What saves the day is that the words we must count are
**non-constant**: a genuine CF trigger word's `L/R` pattern contains both letters.

This file is the pure counting step.  If `v` has an alternation at index `i₀` (`v[i₀] ≠ v[i₀+1]`)
then an occurrence of `v` at position `P` forces an alternation of the stream at `P + i₀`.  The
shift `P ↦ P + i₀` is injective, so

  `#{occurrences starting in [a,b)} ≤ #{alternations of the stream in [a, b + |v|)}`
                                    `≤ #{alternations in [a,b)} + |v|`,

and the second summand is the only price paid for occurrences that run past the block's end.
Combined with `VandeheyRunBound.numAlt_lrOut_le_two_mul` (at most `2D` alternations inside a
block) this gives the uniform constant `K = 2D + 1 + |v|`.
-/

namespace NormalNumbers.VandeheyOut

variable {α : Type*} [DecidableEq α]

/-! ## Alternations of a stream on an interval -/

/-- The number of positions `p ∈ [a,b)` at which the stream `f` changes value. -/
def altCount (f : ℕ → α) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun p => f p ≠ f (p + 1))).card

lemma altCount_mono (f : ℕ → α) {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    altCount f a b ≤ altCount f a' b' := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro p hp
  simp only [Finset.mem_Ico] at hp ⊢
  omega

/-- Extending the interval on the right by `m` costs at most `m`. -/
lemma altCount_le_add (f : ℕ → α) (a b m : ℕ) :
    altCount f a (b + m) ≤ altCount f a b + m := by
  classical
  have hsplit : Finset.Ico a (b + m) ⊆ Finset.Ico a b ∪ Finset.Ico b (b + m) := by
    intro p hp
    simp only [Finset.mem_Ico, Finset.mem_union] at hp ⊢
    omega
  calc altCount f a (b + m)
      ≤ ((Finset.Ico a b ∪ Finset.Ico b (b + m)).filter (fun p => f p ≠ f (p + 1))).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hsplit)
    _ ≤ ((Finset.Ico a b).filter (fun p => f p ≠ f (p + 1))).card
        + ((Finset.Ico b (b + m)).filter (fun p => f p ≠ f (p + 1))).card := by
        rw [Finset.filter_union]; exact Finset.card_union_le _ _
    _ ≤ altCount f a b + m :=
        Nat.add_le_add_left (le_trans (Finset.card_filter_le _ _) (by simp)) _

/-! ## The counting bound -/

/-- **Occurrences are counted by alternations.**  If `v` alternates at index `i₀`, every
occurrence of `v` in the stream `f` starting in `[a,b)` produces a distinct alternation of `f`
in `[a + i₀, b + i₀)`.  The hypothesis is phrased with `getElem?` so that no index-bound
side goal escapes into the statement. -/
theorem card_occ_le_altCount (f : ℕ → α) (v : List α) (a b i₀ : ℕ)
    (hi : i₀ + 1 < v.length) (hne : v[i₀]? ≠ v[i₀ + 1]?) :
    ((Finset.Ico a b).filter (fun P => v = (List.range' P v.length).map f)).card
      ≤ altCount f (a + i₀) (b + i₀) := by
  classical
  refine Finset.card_le_card_of_injOn (fun P => P + i₀) ?_ ?_
  · intro P hP
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hP
    obtain ⟨⟨hPa, hPb⟩, hval⟩ := hP
    have hget : ∀ i, i < v.length → v[i]? = some (f (P + i)) := by
      intro i hiv
      have h1 : v[i]? = ((List.range' P v.length).map f)[i]? := by conv_lhs => rw [hval]
      have h2 : (List.range' P v.length)[i]? = some (P + i) := by
        rw [List.getElem?_eq_getElem (by simpa using hiv)]
        simp
      rw [h1, List.getElem?_map, h2, Option.map_some]
    simp only [altCount, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h1 := hget i₀ (by omega)
    have h2 := hget (i₀ + 1) (by omega)
    intro hcon
    rw [h1, h2] at hne
    exact hne (by rw [hcon, show P + i₀ + 1 = P + (i₀ + 1) from by omega])
  · intro P _ Q _ h
    exact Nat.add_right_cancel h

/-- **The form the trigger layer uses.**  Occurrences of a non-constant `v` starting in `[a,b)`
are at most the alternations of the stream inside `[a,b)` plus `|v|` — the price of occurrences
that run past `b`. -/
theorem card_occ_le_altCount_add (f : ℕ → α) (v : List α) (a b i₀ : ℕ)
    (hi : i₀ + 1 < v.length) (hne : v[i₀]? ≠ v[i₀ + 1]?) :
    ((Finset.Ico a b).filter (fun P => v = (List.range' P v.length).map f)).card
      ≤ altCount f a b + v.length := by
  refine (card_occ_le_altCount f v a b i₀ hi hne).trans ?_
  refine (altCount_mono f (a' := a) (b' := b + v.length) (by omega) (by omega)).trans ?_
  exact altCount_le_add f a b v.length

/-! ## Alternations of a LIST, and the padded stream

`numAlt` is the list-side alternation count — the number of runs of a nonempty list is
`numAlt + 1` — and it is what `VandeheyRunBound` bounds for an emitted block.  The bridge to
`altCount` is `altCount_getD_le`: reading a list as a stream padded with `d` past its end costs
at most one extra alternation, at the pad boundary. -/

/-- The number of adjacent unequal pairs of a list. -/
def numAlt : List α → ℕ
  | [] => 0
  | _ :: [] => 0
  | b :: c :: w => (if b = c then 0 else 1) + numAlt (c :: w)

@[simp] lemma numAlt_nil : numAlt ([] : List α) = 0 := rfl
@[simp] lemma numAlt_singleton (b : α) : numAlt [b] = 0 := rfl

lemma numAlt_cons_le (b : α) (w : List α) : numAlt (b :: w) ≤ numAlt w + 1 := by
  cases w with
  | nil => simp
  | cons c w =>
    rw [numAlt]
    split <;> omega

/-- The cons step, stated with the padded lookup so that it composes with `altCount`. -/
lemma numAlt_cons (x : α) (L : List α) (hL : L ≠ []) (d : α) :
    numAlt (x :: L) = (if x = L.getD 0 d then 0 else 1) + numAlt L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons y t =>
    simp only [numAlt, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]

/-- A constant list has no alternation. -/
lemma numAlt_eq_zero_of_const : ∀ (w : List α) (b : α), (∀ x ∈ w, x = b) → numAlt w = 0
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | (u :: v :: w), b, h => by
      have hu : u = b := h u (by simp)
      have hv : v = b := h v (by simp)
      rw [numAlt, if_pos (hu.trans hv.symm),
        numAlt_eq_zero_of_const (v :: w) b (fun x hx => h x (by simp [hx]))]

/-! ### `altCount` arithmetic -/

/-- At most one alternation per position. -/
lemma altCount_le_sub (f : ℕ → α) (a b : ℕ) : altCount f a b ≤ b - a := by
  classical
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Splitting the window. -/
lemma altCount_split (f : ℕ → α) (a c b : ℕ) (hac : a ≤ c) (hcb : c ≤ b) :
    altCount f a b ≤ altCount f a c + altCount f c b := by
  classical
  have hsplit : Finset.Ico a b ⊆ Finset.Ico a c ∪ Finset.Ico c b := by
    intro p hp
    simp only [Finset.mem_Ico, Finset.mem_union] at hp ⊢
    omega
  calc altCount f a b
      ≤ ((Finset.Ico a c ∪ Finset.Ico c b).filter (fun p => f p ≠ f (p + 1))).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hsplit)
    _ ≤ altCount f a c + altCount f c b := by
        rw [Finset.filter_union]; exact Finset.card_union_le _ _

/-- Streams that agree up to `b` have the same alternation count on `[a,b)`. -/
lemma altCount_congr {f g : ℕ → α} (a b : ℕ) (h : ∀ p ≤ b, f p = g p) :
    altCount f a b = altCount g a b := by
  classical
  simp only [altCount]
  congr 1
  refine Finset.filter_congr fun p hp => ?_
  simp only [Finset.mem_Ico] at hp
  rw [h p (by omega), h (p + 1) (by omega)]

/-- Dropping the first position shifts the stream. -/
lemma altCount_shift_one (f : ℕ → α) (m : ℕ) :
    altCount f 1 (m + 1) = altCount (fun p => f (p + 1)) 0 m := by
  classical
  have h := card_filter_range_shift 1 m (fun p => f p ≠ f (p + 1))
  rw [show (1 : ℕ) + m = m + 1 from by omega, Finset.range_eq_Ico] at h
  rw [altCount, ← h, altCount]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [show 1 + p = p + 1 from by omega]

/-- **A list read as a stream, padded with `d`, has at most `numAlt + 1` alternations.**  The
`+1` is the pad boundary, and nothing more: past the end the stream is constant. -/
lemma altCount_getD_le (d : α) : ∀ (L : List α) (m : ℕ),
    altCount (fun p => L.getD p d) 0 m ≤ numAlt L + 1 := by
  intro L
  induction L with
  | nil =>
    intro m
    have h0 : altCount (fun _ : ℕ => d) 0 m = 0 := by
      simp [altCount]
    have hcongr : altCount (fun p => ([] : List α).getD p d) 0 m = altCount (fun _ : ℕ => d) 0 m :=
      altCount_congr 0 m (fun p _ => by simp)
    rw [hcongr, h0]
    omega
  | cons x L ih =>
    intro m
    cases m with
    | zero => simp [altCount]
    | succ m =>
      have hshift : altCount (fun p => (x :: L).getD p d) 1 (m + 1)
          = altCount (fun p => L.getD p d) 0 m := by
        rw [altCount_shift_one]
        exact altCount_congr 0 m (fun p _ => by
          simp [List.getD_eq_getElem?_getD])
      have hone : altCount (fun p => (x :: L).getD p d) 0 1
          ≤ (if x = L.getD 0 d then 0 else 1) := by
        by_cases h : x = L.getD 0 d
        · rw [if_pos h, Nat.le_zero, altCount, Finset.card_eq_zero,
            Finset.filter_eq_empty_iff]
          intro p hp
          simp only [Finset.mem_Ico] at hp
          have hp0 : p = 0 := by omega
          subst hp0
          simp only [not_not, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
            Option.getD_some, Nat.zero_add, List.getElem?_cons_succ]
          exact h
        · rw [if_neg h]
          exact le_trans (altCount_le_sub _ 0 1) (by omega)
      have hsplit := altCount_split (fun p => (x :: L).getD p d) 0 1 (m + 1) (by omega) (by omega)
      rw [hshift] at hsplit
      have hA : (if x = L.getD 0 d then 0 else 1) ≤ 1 := by split <;> omega
      rcases eq_or_ne L [] with rfl | hne
      · have h0 : altCount (fun p => ([] : List α).getD p d) 0 m = 0 := by
          have hcongr : altCount (fun p => ([] : List α).getD p d) 0 m
              = altCount (fun _ : ℕ => d) 0 m := altCount_congr 0 m (fun p _ => by simp)
          rw [hcongr]
          simp [altCount]
        rw [h0] at hsplit
        simp only [numAlt_singleton]
        omega
      · have hc := numAlt_cons x L hne d
        have hih := ih m
        omega

/-! ## `hK` and `hkK` reduce to a single bound on `occIn`

The two trigger hypotheses of `VandeheyAssembly.mobiusUniformFreq_of_transducer` are, by
telescoping, one and the same statement: **at most `K` occurrences of `v` start in the first
emitted block of a run**.  `kOut` is an increment of `occIn`, and the `hK` sum telescopes to
`occIn` at the truncation length, exactly as `sum_kOut_eq` does for windows. -/

section Reduce

variable {S : Type*} [DecidableEq S] (δ : S → ℕ → S) (out : S → ℕ → List ℕ)

open VandeheyAut

/-- A list is the `getD`-map of its index range. -/
lemma eq_map_range_getD (W : List ℕ) : W = (List.range W.length).map (fun i => W.getD i 0) := by
  refine List.ext_getElem (by simp) ?_
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

/-- A window of a list, in stream form. -/
lemma take_drop_eq_map_range' (W : List ℕ) (p n : ℕ) (h : p + n ≤ W.length) :
    (W.drop p).take n = (List.range' p n).map (fun i => W.getD i 0) := by
  conv_lhs => rw [eq_map_range_getD W]
  rw [take_drop_map_range, min_eq_left (by omega)]

/-- **The uniform trigger bound, abstractly.**  For a word `v` with an alternation at index
`i₀`, the number of occurrences of `v` starting in the FIRST emitted block of the run of `q`
from `t` is bounded by that block's own alternation count plus `|v| + 2` — with no reference to
the block's LENGTH, which for the `L/R` transducer is unbounded.  With
`VandeheyRunBound.numAlt_lrOut_le_two_mul` this is Vandehey's Lemma 2.2 in the form
`trigger_bounds_of_occIn_le` consumes. -/
theorem occIn_le_numAlt_add (v : List ℕ) (i₀ : ℕ) (hi : i₀ + 1 < v.length)
    (hne : v[i₀]? ≠ v[i₀ + 1]?) (t : S) (q : List ℕ) :
    occIn δ out v t q ≤ numAlt (blocksOf δ out t (q.take 1)) + 2 + v.length := by
  classical
  set W : List ℕ := blocksOf δ out t q with hW
  set B : List ℕ := blocksOf δ out t (q.take 1) with hB
  set f : ℕ → ℕ := fun p => W.getD p 0 with hf
  -- `W` starts with `B`
  have hWB : ∃ R, W = B ++ R := by
    refine ⟨blocksOf δ out (runState δ t (q.take 1)) (q.drop 1), ?_⟩
    rw [hW, hB, ← blocksOf_append, List.take_append_drop]
  obtain ⟨R, hWR⟩ := hWB
  -- step 1: relax the `occIn` predicate to the stream form
  have h1 : occIn δ out v t q
      ≤ ((Finset.Ico 0 B.length).filter (fun P => v = (List.range' P v.length).map f)).card := by
    rw [occIn]
    refine Finset.card_le_card ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    obtain ⟨hlt, hfit, hval⟩ := hp
    exact ⟨⟨by omega, hlt⟩, hval.trans (take_drop_eq_map_range' W p v.length hfit)⟩
  -- step 2: occurrences are counted by alternations
  have h2 := card_occ_le_altCount_add f v 0 B.length i₀ hi hne
  -- step 3: the alternations inside the block are `numAlt B`, up to the boundary
  have h3 : altCount f 0 B.length ≤ numAlt B + 2 := by
    rcases Nat.eq_zero_or_pos B.length with h0 | hpos
    · rw [h0]
      simp [altCount]
    · have hsp := altCount_split f 0 (B.length - 1) B.length (by omega) (by omega)
      have hlast : altCount f (B.length - 1) B.length ≤ 1 :=
        le_trans (altCount_le_sub _ _ _) (by omega)
      have hcg : altCount f 0 (B.length - 1) = altCount (fun p => B.getD p 0) 0 (B.length - 1) := by
        refine altCount_congr 0 (B.length - 1) fun p hp => ?_
        rw [hf, hWR]
        exact List.getD_append B R 0 p (by omega)
      have hgd := altCount_getD_le (0 : ℕ) B (B.length - 1)
      rw [hcg] at hsp
      omega
  omega

/-- Telescoping along the CF prefixes of `y` (the shape `hK` is stated in). -/
lemma sum_kOut_cfWord_eq (v : List ℕ) (y : ℝ) (t : S) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, kOut δ out v (cfWord y j) t = occIn δ out v t (cfWord y J) := by
  induction J with
  | zero => simp [cfWord]
  | succ J ih =>
    have hdrop : (cfWord y (J + 1)).dropLast = cfWord y J := by
      rw [cfWord_succ', List.dropLast_concat]
    have hmono : occIn δ out v t (cfWord y J) ≤ occIn δ out v t (cfWord y (J + 1)) := by
      rw [cfWord_succ']
      exact occIn_mono_concat δ out v _ _ _
    have hins : Finset.Icc 1 (J + 1) = insert (J + 1) (Finset.Icc 1 J) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), ih, kOut, hdrop]
    omega

/-- **The trigger hypotheses, reduced.**  A single uniform bound on `occIn` supplies both
`hkK` and `hK`. -/
theorem trigger_bounds_of_occIn_le {K : ℕ} (v : List ℕ)
    (hocc : ∀ (t : S) (q : List ℕ), occIn δ out v t q ≤ K) :
    (∀ q t, kOut δ out v q t ≤ K) ∧
      (∀ (t : S) (y : ℝ) (J : ℕ), ∑ j ∈ Finset.Icc 1 J, kOut δ out v (cfWord y j) t ≤ K) := by
  refine ⟨fun q t => le_trans ?_ (hocc t q), fun t y J => ?_⟩
  · rw [kOut]; exact Nat.sub_le _ _
  · rw [sum_kOut_cfWord_eq]; exact hocc t _

end Reduce

end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms altCount_le_add
#print axioms card_occ_le_altCount
#print axioms card_occ_le_altCount_add
#print axioms sum_kOut_cfWord_eq
#print axioms occIn_le_numAlt_add
#print axioms trigger_bounds_of_occIn_le
end
