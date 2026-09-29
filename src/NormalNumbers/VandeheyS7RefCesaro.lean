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

/-! ## The level constant and the level limit -/

/-- The `j`-th level's limit at digit bound `B`: a finite sum of relative masses, depending on
neither the input nor the map. -/
noncomputable def refLevel (w : List ℕ) (j B : ℕ) : ℝ :=
  ∑ u ∈ boundedWords B (j + 1),
    digitEmit (stateOf j u) (aOf j u) * relMass (vOf j u) (targOf w j u)

lemma sum_refPiece_eq (w : List ℕ) (j B : ℕ) (x : ℝ) (p : ℕ) :
    ∑ m ∈ range p, ∑ u ∈ boundedWords B (j + 1), refPiece w j u (gaussMap^[m] x)
      = ∑ u ∈ boundedWords B (j + 1), digitEmit (stateOf j u) (aOf j u)
          * blockCount (relSet (vOf j u) (targOf w j u)) p x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [blockCount_apply, Finset.mul_sum]
  rfl

/-- The summed form of the pointwise decomposition. -/
lemma abs_sum_slotObs_sub_le {w : List ℕ} (B j : ℕ) {x : ℝ}
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (p : ℕ) :
    |(∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] x)))
        - ∑ u ∈ boundedWords B (j + 1), digitEmit (stateOf j u) (aOf j u)
            * blockCount (relSet (vOf j u) (targOf w j u)) p x|
      ≤ (p : ℝ) - blockCount (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) p x := by
  rw [← sum_refPiece_eq w j B x p, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hE : (p : ℝ) - blockCount (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) p x
      = ∑ m ∈ range p,
        (1 - blockIndic (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) (gaussMap^[m] x)) := by
    rw [blockCount_apply, Finset.sum_sub_distrib]
    simp
  rw [hE]
  refine Finset.sum_le_sum fun m _ => ?_
  refine abs_slotObs_sub_sum_refPiece_le B j (fun k => ?_)
  rw [← Function.iterate_add_apply]
  exact horb _

/-- **The level limit.**  For every tolerance there is a digit bound at which the `j`-th level's
Cesàro average is eventually within the tolerance of the constant `refLevel w j B`, for EVERY
CF-normal input. -/
theorem exists_eventually_abs_level_sub_le {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ x : ℝ, IsCFNormal x → (∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        |(∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] x))) / (p : ℝ)
          - refLevel w j B| ≤ ε := by
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt (j + 1)
    (show (0:ℝ) < ε / 4 by linarith)
  refine ⟨B, fun x hx horb => ?_⟩
  set E : Set ℝ := ⋃ u ∈ boundedWords B (j + 1), cfCylinder u with hEdef
  set mG := ∑ u ∈ boundedWords B (j + 1), (gaussMeasure (cfCylinder u)).toReal with hmG
  have hfE : Tendsto (fun p => blockCount E p x / (p : ℝ)) atTop (nhds mG) := by
    rw [hEdef, hmG]
    exact tendsto_windowFreq (S := boundedWords B (j + 1)) hx horb (Nat.succ_pos j)
      (fun u hu => boundedWords_len hu) (fun u hu => boundedWords_pos hu)
  have hfS : Tendsto (fun p => ∑ u ∈ boundedWords B (j + 1),
      digitEmit (stateOf j u) (aOf j u)
        * (blockCount (relSet (vOf j u) (targOf w j u)) p x / (p : ℝ))) atTop
      (nhds (refLevel w j B)) := by
    rw [refLevel]
    refine tendsto_finsetSum _ fun u hu => ?_
    exact (tendsto_blockCount_relSet_of_ordConnected hx horb (vOf_pos hu)
      (measurableSet_targOf w j u) (targOf_subset w j u)
      (targOf_ordConnected hw hu)).const_mul _
  have hevS := hfS.eventually (eventually_abs_sub_lt (refLevel w j B)
    (show (0:ℝ) < ε / 4 by linarith))
  have hevE := hfE.eventually (eventually_gt_nhds (show mG - ε / 4 < mG by linarith))
  filter_upwards [hevS, hevE, eventually_gt_atTop 0] with p hpS hpE hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hbnd := abs_sum_slotObs_sub_le (w := w) B j horb p
  have hdiv : |(∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] x))) / (p : ℝ)
      - ∑ u ∈ boundedWords B (j + 1), digitEmit (stateOf j u) (aOf j u)
          * (blockCount (relSet (vOf j u) (targOf w j u)) p x / (p : ℝ))|
      ≤ 1 - blockCount E p x / (p : ℝ) := by
    have hsplit : ∑ u ∈ boundedWords B (j + 1), digitEmit (stateOf j u) (aOf j u)
        * (blockCount (relSet (vOf j u) (targOf w j u)) p x / (p : ℝ))
        = (∑ u ∈ boundedWords B (j + 1), digitEmit (stateOf j u) (aOf j u)
            * blockCount (relSet (vOf j u) (targOf w j u)) p x) / (p : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hsplit, div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    have harith : (1 - blockCount E p x / (p : ℝ)) * (p : ℝ)
        = (p : ℝ) - blockCount E p x := by field_simp
    rw [harith]
    exact hbnd
  have hmass : (1:ℝ) - mG ≤ ε / 4 := by rw [hmG] at hB ⊢; linarith
  have h1 := abs_lt.1 hpS
  have h2 := abs_le.1 hdiv
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## The assembly: `RefCesaro` -/

/-- The Cesàro average of the block average, expanded over the levels. -/
lemma sum_blockAvg_div_eq (w : List ℕ) {T : ℕ} (hT : 0 < T) (x : ℝ) (p : ℕ) :
    (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)
      = (∑ j ∈ range T,
          (∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] x))) / (p : ℝ)) / T := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have key : ∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)
      = (∑ j ∈ range T, ∑ m ∈ range p,
          slotObs w (pairStep^[j] (refState, gaussMap^[m] x))) / T := by
    rw [Finset.sum_comm, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => rfl
  rw [key, ← Finset.sum_div, div_div, div_div, mul_comm]

end MapState

/-- **A uniform limit from uniform approximations.**  If, for every tolerance, ONE constant
approximates every member of a family eventually, then every member converges — to one and the same
limit. -/
theorem exists_uniform_limit_of_approx {ι : Type*} {F : ι → ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ i : ι, ∀ᶠ p in atTop, |F i p - L| ≤ ε) :
    ∃ L : ℝ, ∀ i : ι, Tendsto (F i) atTop (nhds L) := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    obtain ⟨a₀, ha₀⟩ := MapState.exists_tendsto_of_approx (F := F i₀)
      (fun ε hε => by
        obtain ⟨L, hL⟩ := h ε hε
        exact ⟨L, hL i₀⟩)
    refine ⟨a₀, fun i => ?_⟩
    obtain ⟨a, ha⟩ := MapState.exists_tendsto_of_approx (F := F i)
      (fun ε hε => by
        obtain ⟨L, hL⟩ := h ε hε
        exact ⟨L, hL i⟩)
    have heq : a = a₀ := by
      by_contra hne
      have hd : 0 < |a - a₀| := abs_pos.2 (sub_ne_zero.2 hne)
      obtain ⟨L, hL⟩ := h (|a - a₀| / 4) (by linarith)
      have h1 : |a - L| ≤ |a - a₀| / 4 := MapState.abs_limit_sub_le ha (hL i)
      have h2 : |a₀ - L| ≤ |a - a₀| / 4 := MapState.abs_limit_sub_le ha₀ (hL i₀)
      have h3 : |a - a₀| ≤ |a - L| + |L - a₀| := by
        have := abs_add_le (a - L) (L - a₀)
        simpa using this
      rw [abs_sub_comm L a₀] at h3
      linarith
    exact heq ▸ ha
  · exact ⟨0, fun i => absurd ⟨i⟩ hι⟩

namespace MapState

/-- **S7-RC, the headline: `RefCesaro` is a THEOREM.**  The reference-state Cesàro input of the
route-A architecture (S7-BF) is discharged — no cited input, no absolute continuity, no distortion
constant.  Only CF-normality of the input, S7-RQ's relative equidistribution, and the
order-connectedness of the reference target (S7-RT). -/
theorem refCesaro_holds {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) : RefCesaro w := by
  classical
  intro T hT
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  set ι := {x : ℝ // IsCFNormal x ∧ ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1} with hι
  have hmain : ∃ L : ℝ, ∀ i : ι,
      Tendsto (fun p => (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] i.1)) / (p : ℝ))
        atTop (nhds L) := by
    refine exists_uniform_limit_of_approx (fun ε hε => ?_)
    choose Bf hBf using fun j : ℕ => exists_eventually_abs_level_sub_le hw j hε
    refine ⟨(∑ j ∈ range T, refLevel w j (Bf j)) / T, fun i => ?_⟩
    have hall : ∀ᶠ p : ℕ in atTop, ∀ j ∈ range T,
        |(∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] i.1))) / (p : ℝ)
          - refLevel w j (Bf j)| ≤ ε := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact hBf j i.1 i.2.1 i.2.2
    filter_upwards [hall] with p hp
    have hsplit : (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] i.1)) / (p : ℝ)
        - (∑ j ∈ range T, refLevel w j (Bf j)) / T
        = (∑ j ∈ range T,
            ((∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] i.1))) / (p : ℝ)
              - refLevel w j (Bf j))) / T := by
      rw [sum_blockAvg_div_eq w hT i.1 p, ← sub_div, ← Finset.sum_sub_distrib]
    rw [hsplit, abs_div, abs_of_pos hTR, div_le_iff₀ hTR]
    calc |∑ j ∈ range T,
            ((∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] i.1))) / (p : ℝ)
              - refLevel w j (Bf j))|
        ≤ ∑ j ∈ range T,
            |(∑ m ∈ range p, slotObs w (pairStep^[j] (refState, gaussMap^[m] i.1))) / (p : ℝ)
              - refLevel w j (Bf j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range T, ε := Finset.sum_le_sum fun j hj => hp j hj
      _ = ε * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  obtain ⟨L, hL⟩ := hmain
  refine ⟨L, fun x hx horb => ?_⟩
  exact hL ⟨x, hx, horb⟩

/-- **The chain, with one input left.**  Route A's universality conclusion now rests on
`BlockForget` ALONE (plus the width affordability that each input must satisfy): `RefCesaro` is
discharged. -/
theorem exists_uniform_slotCountFreq_of_blockForget {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a)
    (hBF : BlockForget w) :
    ∃ L : ℝ, ∀ (Φ : MapState) (x : ℝ), IsCFNormal x →
      (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) → WidthAfford Φ x →
      Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop (nhds L) :=
  exists_uniform_slotCountFreq hBF (refCesaro_holds hw)

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.abs_slotObs_sub_sum_refPiece_le
#print axioms NormalNumbers.VandeheyS7.MapState.exists_eventually_abs_level_sub_le
#print axioms NormalNumbers.VandeheyS7.exists_uniform_limit_of_approx
#print axioms NormalNumbers.VandeheyS7.MapState.refCesaro_holds
#print axioms NormalNumbers.VandeheyS7.MapState.exists_uniform_slotCountFreq_of_blockForget

end Audit
