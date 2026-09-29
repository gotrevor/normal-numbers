/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RC: the reference observable is a finite combination of computable events

This is directive item (b) and next-action #1 of lap 88's baton: discharge `RefCesaro` (S7-BF) from
S7-RQ.  The pieces are all in place:

* S7-WS: the state after the first `j` digits is `wordState refState v`, a closed function of the
  word `v`, and the emission factor is `digitEmit` of that state and the next digit;
* S7-RT: the target `mapBlockSet σ w 0` is order-connected;
* S7-RQ: for an order-connected `A ⊆ (0,1)`, the orbit frequency of `I_v ∩ G^{-|v|}A` is
  `relMass v A`, for every CF-normal input.

So, at digit bound `B`, the `j`-th slot observable of the reference run is

    slotObs w (pairStep^[j] (refState, z))
      = Σ_{u ∈ boundedWords B (j+1)} digitEmit (σ u) (aOf u) · 1_{relSet (vOf u) (targ u)} (z)
        + (an error supported off the bounded-digit family)

with `vOf u = u.take j`, `aOf u = u.getD j 0`, `σ u = wordState refState (vOf u)` and
`targ u = mapBlockSet (σ u) w 0 ∩ I_{[aOf u]}` — an order-connected target.  Each term's frequency
is computed by S7-RQ and is INDEPENDENT of the input, and the error's frequency is the
unbounded-digit mass, which `exists_boundedWords_sum_gt` makes as small as wanted.

## Guard rule

**Content locator.**  The decomposition is exact, not an estimate: the only inequality is the
error's support.  With `B` so large that the bounded family carries all the mass the statement
would be an identity; the content is that the family is FINITE, which is what makes the limit a
finite sum of `relMass`es and hence input-independent.

**Degenerate cases.**  `j = 0`: `vOf u = []`, `relSet [] A = (0,1) ∩ A`, and the statement is the
emission-weighted form of S7-EQ.  `w = []`: `mapBlockSet s [] 0 = (0,1)`, so the observable is the
emission indicator and the limit is the clock rate.  `B = 0`: the family is empty and the bound is
the trivial `|f| ≤ 1`.
-/
import NormalNumbers.VandeheyS7WordState

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

attribute [local instance] Classical.propDecidable

namespace MapState

/-! ## The pieces of the decomposition -/

/-- The word read before the tested step. -/
def vOf (j : ℕ) (u : List ℕ) : List ℕ := u.take j

/-- The digit read at the tested step. -/
def aOf (j : ℕ) (u : List ℕ) : ℕ := u.getD j 0

/-- The state at the tested step. -/
noncomputable def stateOf (j : ℕ) (u : List ℕ) : MapState := wordState refState (vOf j u)

/-- The target of the tested step: the state's pullback of `I_w`, intersected with the cylinder of
the digit that is read. -/
noncomputable def targOf (w : List ℕ) (j : ℕ) (u : List ℕ) : Set ℝ :=
  mapBlockSet (stateOf j u) w 0 ∩ cfCylinder [aOf j u]

/-- One term of the decomposition. -/
noncomputable def refPiece (w : List ℕ) (j : ℕ) (u : List ℕ) (z : ℝ) : ℝ :=
  digitEmit (stateOf j u) (aOf j u) * blockIndic (relSet (vOf j u) (targOf w j u)) z

lemma vOf_length {j : ℕ} {u : List ℕ} (h : u.length = j + 1) : (vOf j u).length = j := by
  rw [vOf, List.length_take]
  omega

lemma vOf_append_aOf {j : ℕ} {u : List ℕ} (h : u.length = j + 1) :
    vOf j u ++ [aOf j u] = u := by
  have hj : j < u.length := by omega
  rw [vOf, aOf, List.getD_eq_getElem _ _ hj, List.take_concat_get' u j hj]
  rw [← h]
  exact List.take_of_length_le (le_refl _)

lemma vOf_pos {B j : ℕ} {u : List ℕ} (hu : u ∈ boundedWords B (j + 1)) :
    ∀ a ∈ vOf j u, 1 ≤ a := by
  intro a ha
  exact boundedWords_pos hu a (List.mem_of_mem_take ha)

lemma targOf_subset (w : List ℕ) (j : ℕ) (u : List ℕ) :
    targOf w j u ⊆ Set.Ioo (0:ℝ) 1 := fun _ hz => hz.1.2

lemma measurableSet_targOf (w : List ℕ) (j : ℕ) (u : List ℕ) :
    MeasurableSet (targOf w j u) :=
  ((stateOf j u).measurableSet_mapBlockSet w).inter (measurableSet_cfCylinder _)

lemma targOf_ordConnected {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {B j : ℕ} {u : List ℕ}
    (hu : u ∈ boundedWords B (j + 1)) : (targOf w j u).OrdConnected := by
  refine Set.OrdConnected.inter ((stateOf j u).mapBlockSet_ordConnected hw) ?_
  refine cfCylinder_ordConnected _ ?_
  intro a ha
  have haa : a = aOf j u := by simpa using ha
  subst haa
  have hj : j < u.length := by
    have := boundedWords_len hu
    omega
  exact boundedWords_pos hu _ (by
    rw [aOf, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj)

/-! ## The pointwise decomposition -/

/-- The cylinder of `u` is where the piece of `u` lives. -/
lemma relSet_targOf_subset {B j : ℕ} {u : List ℕ} (hu : u ∈ boundedWords B (j + 1))
    (w : List ℕ) : relSet (vOf j u) (targOf w j u) ⊆ cfCylinder u := by
  have hlen := boundedWords_len hu
  have hsub : relSet (vOf j u) (targOf w j u) ⊆ relSet (vOf j u) (cfCylinder [aOf j u]) :=
    relSet_mono _ Set.inter_subset_right
  refine hsub.trans ?_
  have h := relSet_subset_append (vOf j u) [aOf j u]
  rw [vOf_append_aOf hlen] at h
  exact h

/-- **The pointwise decomposition.**  Exact on the bounded-digit family, and the error is supported
off it. -/
theorem abs_slotObs_sub_sum_refPiece_le {w : List ℕ} (B j : ℕ) {z : ℝ}
    (horb : ∀ k : ℕ, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1) :
    |slotObs w (pairStep^[j] (refState, z))
        - ∑ u ∈ boundedWords B (j + 1), refPiece w j u z|
      ≤ 1 - blockIndic (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) z := by
  have hz01 : z ∈ Set.Ioo (0:ℝ) 1 := by simpa using horb 0
  have hnn : 0 ≤ slotObs w (pairStep^[j] (refState, z)) := slotObs_nonneg _ _
  have hle1 : slotObs w (pairStep^[j] (refState, z)) ≤ 1 := slotObs_le_one' _ _
  by_cases hw : z ∈ ⋃ u ∈ boundedWords B (j + 1), cfCylinder u
  · obtain ⟨u₀, hu₀, hzu₀⟩ := Set.mem_iUnion₂.1 hw
    have hlen := boundedWords_len hu₀
    have hvlen : (vOf j u₀).length = j := vOf_length hlen
    -- the digits of `z` spell `u₀`
    have hdig : ∀ i < j + 1, cfDigit z i = u₀.getD i 0 := by
      intro i hi
      exact hzu₀.2 i (by omega)
    have hdigv : ∀ i < (vOf j u₀).length, cfDigit z i = (vOf j u₀).getD i 0 := by
      intro i hi
      rw [hvlen] at hi
      rw [vOf, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
        ← List.getD_eq_getElem?_getD]
      exact hdig i (by omega)
    -- the slot observable in closed form
    have hslot := slotObs_pairIter_eq refState w (vOf j u₀) z hdigv
    rw [hvlen] at hslot
    have hdigj : cfDigit (gaussMap^[j] z) 0 = aOf j u₀ := by
      rw [cfDigit_iter_shift, Nat.add_zero, aOf]
      exact hdig j (by omega)
    -- the tested point lies in the digit's cylinder
    have hdcyl : gaussMap^[j] z ∈ cfCylinder [aOf j u₀] := by
      refine ⟨horb j, fun i hi => ?_⟩
      have : i = 0 := by simpa using hi
      subst this
      simpa using hdigj
    have hzv : z ∈ cfCylinder (vOf j u₀) := ⟨hz01, hdigv⟩
    -- the piece of `u₀` equals the observable
    have hpiece : refPiece w j u₀ z = slotObs w (pairStep^[j] (refState, z)) := by
      rw [hslot, refPiece, hdigj, stateOf]
      congr 1
      by_cases hm : gaussMap^[j] z ∈ mapBlockSet (wordState refState (vOf j u₀)) w 0
      · have : z ∈ relSet (vOf j u₀) (targOf w j u₀) := by
          refine ⟨hzv, ?_⟩
          rw [hvlen]
          exact ⟨hm, hdcyl⟩
        rw [blockIndic_eq_one' this, blockIndic_eq_one' hm]
      · have : z ∉ relSet (vOf j u₀) (targOf w j u₀) := by
          rintro ⟨-, hmem⟩
          rw [hvlen] at hmem
          exact hm hmem.1
        rw [blockIndic_eq_zero' this, blockIndic_eq_zero' hm]
    -- all other pieces vanish
    have hother : ∀ u ∈ boundedWords B (j + 1), u ≠ u₀ → refPiece w j u z = 0 := by
      intro u hu hne
      have hdisj : Disjoint (cfCylinder u) (cfCylinder u₀) :=
        cfCylinder_disjoint (by rw [boundedWords_len hu, hlen]) hne
      have hznot : z ∉ relSet (vOf j u) (targOf w j u) := by
        intro hmem
        exact Set.disjoint_left.1 hdisj (relSet_targOf_subset hu w hmem) hzu₀
      rw [refPiece, blockIndic_eq_zero' hznot, mul_zero]
    have hsum : ∑ u ∈ boundedWords B (j + 1), refPiece w j u z = refPiece w j u₀ z :=
      Finset.sum_eq_single_of_mem u₀ hu₀ hother
    rw [hsum, hpiece, blockIndic_eq_one' hw]
    simp
  · have hpieces : ∀ u ∈ boundedWords B (j + 1), refPiece w j u z = 0 := by
      intro u hu
      have hznot : z ∉ relSet (vOf j u) (targOf w j u) := by
        intro hmem
        exact hw (Set.mem_iUnion₂.2 ⟨u, hu, relSet_targOf_subset hu w hmem⟩)
      rw [refPiece, blockIndic_eq_zero' hznot, mul_zero]
    rw [Finset.sum_eq_zero hpieces, blockIndic_eq_zero' hw, sub_zero]
    rw [abs_of_nonneg hnn]
    linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.abs_slotObs_sub_sum_refPiece_le

end Audit
