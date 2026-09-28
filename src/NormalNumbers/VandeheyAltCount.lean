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

/-! ## Alternations of a stream on an interval -/

/-- The number of positions `p ∈ [a,b)` at which the stream `f` changes value. -/
noncomputable def altCount (f : ℕ → ℕ) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun p => f p ≠ f (p + 1))).card

lemma altCount_mono (f : ℕ → ℕ) {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    altCount f a b ≤ altCount f a' b' := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro p hp
  simp only [Finset.mem_Ico] at hp ⊢
  omega

/-- Extending the interval on the right by `m` costs at most `m`. -/
lemma altCount_le_add (f : ℕ → ℕ) (a b m : ℕ) :
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
theorem card_occ_le_altCount (f : ℕ → ℕ) (v : List ℕ) (a b i₀ : ℕ)
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
theorem card_occ_le_altCount_add (f : ℕ → ℕ) (v : List ℕ) (a b i₀ : ℕ)
    (hi : i₀ + 1 < v.length) (hne : v[i₀]? ≠ v[i₀ + 1]?) :
    ((Finset.Ico a b).filter (fun P => v = (List.range' P v.length).map f)).card
      ≤ altCount f a b + v.length := by
  refine (card_occ_le_altCount f v a b i₀ hi hne).trans ?_
  refine (altCount_mono f (a' := a) (b' := b + v.length) (by omega) (by omega)).trans ?_
  exact altCount_le_add f a b v.length

/-! ## `hK` and `hkK` reduce to a single bound on `occIn`

The two trigger hypotheses of `VandeheyAssembly.mobiusUniformFreq_of_transducer` are, by
telescoping, one and the same statement: **at most `K` occurrences of `v` start in the first
emitted block of a run**.  `kOut` is an increment of `occIn`, and the `hK` sum telescopes to
`occIn` at the truncation length, exactly as `sum_kOut_eq` does for windows. -/

section Reduce

variable {S : Type*} [DecidableEq S] (δ : S → ℕ → S) (out : S → ℕ → List ℕ)

open VandeheyAut

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
#print axioms trigger_bounds_of_occIn_le
end
