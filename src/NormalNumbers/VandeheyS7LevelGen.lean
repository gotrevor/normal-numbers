/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-LG: the level constants at an ARBITRARY state — the crux becomes arithmetic

S7-RC computed, for the reference state, the Cesàro limit of the `j`-th slot observable along a
CF-normal orbit: a finite sum `refLevel w j B` of relative Gauss masses, independent of the input.
Nothing in that proof used `refState` beyond `stateOf j u = wordState refState (vOf j u)`
(handoff lap 90, next action #3).  This module carries the whole chain over to an arbitrary state
`s`, producing

    levelAt s w j B = Σ_{u ∈ boundedWords B (j+1)} digitEmit (stateAt s j u) (aOf j u)
                        · relMass (vOf j u) (targAt s w j u),

and the level limit `exists_eventually_abs_levelAt_sub_le` valid for every CF-normal input.
Consequences:

* `blockCesaro_holds` — the fixed-state analogue of `RefCesaro`: for EVERY state `s` and every
  block length `T`, the Cesàro average of `blockAvg s T w` along a CF-normal orbit converges to a
  constant `blockLevel s T w` that does not depend on the input;
* `LevelForget` — the crux `BlockForgetRun`, restricted to a state held fixed along the run, is
  exactly the assertion that `blockLevel s T w` does not depend on `s`.  Since S7-RV computed the
  reference value (`blockLevel refState T w = γ(I_w)`, via `refCesaro_value`), the fixed-state
  coordinate of the crux is the *arithmetic* statement

    for every wide state `s`:   Σ_{j<T} levelAt s w j B / T  ≈  γ(I_w).

That statement has no dynamics, no normality and no limits in it beyond the finite sums: the
relative masses are Gauss masses of explicit order-connected sets.  This is the form in which the
crux can be attacked — or refuted — by computation.

## What this does NOT do

`BlockForgetRun` compares the run's state `runState Φ x m`, which VARIES with `m`, against
`refState`, with the absolute value INSIDE the Cesàro sum.  A family of fixed-state limits does not
by itself evaluate that mixed average: doing so needs either uniformity of the approach in `s`
(equicontinuity over the width-`≥η` box) or the state's empirical law.  `LevelForget` is therefore
the fixed-state coordinate of the crux, not the crux; it is what a probe can measure, and a
refutation of it refutes the crux.

## Guard rule

**Content locator.**  Every lemma here is S7-RC's with `refState` replaced by a variable; the
mathematical content is unchanged and is S7-RQ's relative equidistribution.  The new content is
the *statement* `LevelForget` and the equivalence `blockCesaro_holds`.

**Degenerate cases.**  `s = refState` recovers S7-RC exactly (`levelAt refState = refLevel`).
`T = 0` is excluded in `blockCesaro_holds` as in `RefCesaro`.
-/
import NormalNumbers.VandeheyS7RefCesaro

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

attribute [local instance] Classical.propDecidable

namespace MapState

variable (s : MapState)

/-- The state at the tested step. -/
noncomputable def stateAt (j : ℕ) (u : List ℕ) : MapState := wordState s (vOf j u)

/-- The target of the tested step: the state's pullback of `I_w`, intersected with the cylinder of
the digit that is read. -/
noncomputable def targAt (w : List ℕ) (j : ℕ) (u : List ℕ) : Set ℝ :=
  mapBlockSet (stateAt s j u) w 0 ∩ cfCylinder [aOf j u]

/-- One term of the decomposition. -/
noncomputable def pieceAt (w : List ℕ) (j : ℕ) (u : List ℕ) (z : ℝ) : ℝ :=
  digitEmit (stateAt s j u) (aOf j u) * blockIndic (relSet (vOf j u) (targAt s w j u)) z

lemma targAt_subset (w : List ℕ) (j : ℕ) (u : List ℕ) :
    targAt s w j u ⊆ Set.Ioo (0:ℝ) 1 := fun _ hz => hz.1.2

lemma measurableSet_targAt (w : List ℕ) (j : ℕ) (u : List ℕ) :
    MeasurableSet (targAt s w j u) :=
  ((stateAt s j u).measurableSet_mapBlockSet w).inter (measurableSet_cfCylinder _)

lemma targAt_ordConnected {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) {B j : ℕ} {u : List ℕ}
    (hu : u ∈ boundedWords B (j + 1)) : (targAt s w j u).OrdConnected := by
  refine Set.OrdConnected.inter ((stateAt s j u).mapBlockSet_ordConnected hw) ?_
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
lemma relSet_targAt_subset {B j : ℕ} {u : List ℕ} (hu : u ∈ boundedWords B (j + 1))
    (w : List ℕ) : relSet (vOf j u) (targAt s w j u) ⊆ cfCylinder u := by
  have hlen := boundedWords_len hu
  have hsub : relSet (vOf j u) (targAt s w j u) ⊆ relSet (vOf j u) (cfCylinder [aOf j u]) :=
    relSet_mono _ Set.inter_subset_right
  refine hsub.trans ?_
  have h := relSet_subset_append (vOf j u) [aOf j u]
  rw [vOf_append_aOf hlen] at h
  exact h

/-- **The pointwise decomposition.**  Exact on the bounded-digit family, and the error is supported
off it. -/
theorem abs_slotObs_sub_sum_pieceAt_le {w : List ℕ} (B j : ℕ) {z : ℝ}
    (horb : ∀ k : ℕ, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1) :
    |slotObs w (pairStep^[j] (s, z))
        - ∑ u ∈ boundedWords B (j + 1), pieceAt s w j u z|
      ≤ 1 - blockIndic (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) z := by
  have hz01 : z ∈ Set.Ioo (0:ℝ) 1 := by simpa using horb 0
  have hnn : 0 ≤ slotObs w (pairStep^[j] (s, z)) := slotObs_nonneg _ _
  have hle1 : slotObs w (pairStep^[j] (s, z)) ≤ 1 := slotObs_le_one' _ _
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
    have hslot := slotObs_pairIter_eq s w (vOf j u₀) z hdigv
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
    have hpiece : pieceAt s w j u₀ z = slotObs w (pairStep^[j] (s, z)) := by
      rw [hslot, pieceAt, hdigj, stateAt]
      congr 1
      by_cases hm : gaussMap^[j] z ∈ mapBlockSet (wordState s (vOf j u₀)) w 0
      · have : z ∈ relSet (vOf j u₀) (targAt s w j u₀) := by
          refine ⟨hzv, ?_⟩
          rw [hvlen]
          exact ⟨hm, hdcyl⟩
        rw [blockIndic_eq_one' this, blockIndic_eq_one' hm]
      · have : z ∉ relSet (vOf j u₀) (targAt s w j u₀) := by
          rintro ⟨-, hmem⟩
          rw [hvlen] at hmem
          exact hm hmem.1
        rw [blockIndic_eq_zero' this, blockIndic_eq_zero' hm]
    -- all other pieces vanish
    have hother : ∀ u ∈ boundedWords B (j + 1), u ≠ u₀ → pieceAt s w j u z = 0 := by
      intro u hu hne
      have hdisj : Disjoint (cfCylinder u) (cfCylinder u₀) :=
        cfCylinder_disjoint (by rw [boundedWords_len hu, hlen]) hne
      have hznot : z ∉ relSet (vOf j u) (targAt s w j u) := by
        intro hmem
        exact Set.disjoint_left.1 hdisj (relSet_targAt_subset s hu w hmem) hzu₀
      rw [pieceAt, blockIndic_eq_zero' hznot, mul_zero]
    have hsum : ∑ u ∈ boundedWords B (j + 1), pieceAt s w j u z = pieceAt s w j u₀ z :=
      Finset.sum_eq_single_of_mem u₀ hu₀ hother
    rw [hsum, hpiece, blockIndic_eq_one' hw]
    simp
  · have hpieces : ∀ u ∈ boundedWords B (j + 1), pieceAt s w j u z = 0 := by
      intro u hu
      have hznot : z ∉ relSet (vOf j u) (targAt s w j u) := by
        intro hmem
        exact hw (Set.mem_iUnion₂.2 ⟨u, hu, relSet_targAt_subset s hu w hmem⟩)
      rw [pieceAt, blockIndic_eq_zero' hznot, mul_zero]
    rw [Finset.sum_eq_zero hpieces, blockIndic_eq_zero' hw, sub_zero]
    rw [abs_of_nonneg hnn]
    linarith

/-! ## The level constant and the level limit -/

/-- The `j`-th level's limit at digit bound `B`: a finite sum of relative masses, depending on
neither the input nor the map. -/
noncomputable def levelAt (w : List ℕ) (j B : ℕ) : ℝ :=
  ∑ u ∈ boundedWords B (j + 1),
    digitEmit (stateAt s j u) (aOf j u) * relMass (vOf j u) (targAt s w j u)

lemma sum_pieceAt_eq (w : List ℕ) (j B : ℕ) (x : ℝ) (p : ℕ) :
    ∑ m ∈ range p, ∑ u ∈ boundedWords B (j + 1), pieceAt s w j u (gaussMap^[m] x)
      = ∑ u ∈ boundedWords B (j + 1), digitEmit (stateAt s j u) (aOf j u)
          * blockCount (relSet (vOf j u) (targAt s w j u)) p x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [blockCount_apply, Finset.mul_sum]
  rfl

/-- The summed form of the pointwise decomposition. -/
lemma abs_sum_slotObs_sub_le_at {w : List ℕ} (B j : ℕ) {x : ℝ}
    (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (p : ℕ) :
    |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x)))
        - ∑ u ∈ boundedWords B (j + 1), digitEmit (stateAt s j u) (aOf j u)
            * blockCount (relSet (vOf j u) (targAt s w j u)) p x|
      ≤ (p : ℝ) - blockCount (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) p x := by
  rw [← sum_pieceAt_eq s w j B x p, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hE : (p : ℝ) - blockCount (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) p x
      = ∑ m ∈ range p,
        (1 - blockIndic (⋃ u ∈ boundedWords B (j + 1), cfCylinder u) (gaussMap^[m] x)) := by
    rw [blockCount_apply, Finset.sum_sub_distrib]
    simp
  rw [hE]
  refine Finset.sum_le_sum fun m _ => ?_
  refine abs_slotObs_sub_sum_pieceAt_le s B j (fun k => ?_)
  rw [← Function.iterate_add_apply]
  exact horb _

/-- **The level limit.**  For every tolerance there is a digit bound at which the `j`-th level's
Cesàro average is eventually within the tolerance of the constant `levelAt s w j B`, for EVERY
CF-normal input. -/
theorem exists_eventually_abs_levelAt_sub_le' {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (s : MapState) (x : ℝ), IsCFNormal x →
      (∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
          - levelAt s w j B| ≤ ε := by
  obtain ⟨B, hB⟩ := VandeheyOut.exists_boundedWords_sum_gt (j + 1)
    (show (0:ℝ) < ε / 4 by linarith)
  refine ⟨B, fun s x hx horb => ?_⟩
  set E : Set ℝ := ⋃ u ∈ boundedWords B (j + 1), cfCylinder u with hEdef
  set mG := ∑ u ∈ boundedWords B (j + 1), (gaussMeasure (cfCylinder u)).toReal with hmG
  have hfE : Tendsto (fun p => blockCount E p x / (p : ℝ)) atTop (nhds mG) := by
    rw [hEdef, hmG]
    exact tendsto_windowFreq (S := boundedWords B (j + 1)) hx horb (Nat.succ_pos j)
      (fun u hu => boundedWords_len hu) (fun u hu => boundedWords_pos hu)
  have hfS : Tendsto (fun p => ∑ u ∈ boundedWords B (j + 1),
      digitEmit (stateAt s j u) (aOf j u)
        * (blockCount (relSet (vOf j u) (targAt s w j u)) p x / (p : ℝ))) atTop
      (nhds (levelAt s w j B)) := by
    rw [levelAt]
    refine tendsto_finsetSum _ fun u hu => ?_
    exact (tendsto_blockCount_relSet_of_ordConnected hx horb (vOf_pos hu)
      (measurableSet_targAt s w j u) (targAt_subset s w j u)
      (targAt_ordConnected s hw hu)).const_mul _
  have hevS := hfS.eventually (eventually_abs_sub_lt (levelAt s w j B)
    (show (0:ℝ) < ε / 4 by linarith))
  have hevE := hfE.eventually (eventually_gt_nhds (show mG - ε / 4 < mG by linarith))
  filter_upwards [hevS, hevE, eventually_gt_atTop 0] with p hpS hpE hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hbnd := abs_sum_slotObs_sub_le_at s (w := w) B j horb p
  have hdiv : |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
      - ∑ u ∈ boundedWords B (j + 1), digitEmit (stateAt s j u) (aOf j u)
          * (blockCount (relSet (vOf j u) (targAt s w j u)) p x / (p : ℝ))|
      ≤ 1 - blockCount E p x / (p : ℝ) := by
    have hsplit : ∑ u ∈ boundedWords B (j + 1), digitEmit (stateAt s j u) (aOf j u)
        * (blockCount (relSet (vOf j u) (targAt s w j u)) p x / (p : ℝ))
        = (∑ u ∈ boundedWords B (j + 1), digitEmit (stateAt s j u) (aOf j u)
            * blockCount (relSet (vOf j u) (targAt s w j u)) p x) / (p : ℝ) := by
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

/-- The level limit at a fixed state (S7-RC's shape). -/
theorem exists_eventually_abs_levelAt_sub_le {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ x : ℝ, IsCFNormal x → (∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
          - levelAt s w j B| ≤ ε := by
  obtain ⟨B, hB⟩ := exists_eventually_abs_levelAt_sub_le' hw j hε
  exact ⟨B, fun x hx horb => hB s x hx horb⟩

/-! ## The assembly: the fixed-state Cesàro limit -/

/-- The Cesàro average of the block average, expanded over the levels, at an arbitrary state. -/
lemma sum_blockAvg_div_eq_at (w : List ℕ) {T : ℕ} (hT : 0 < T) (x : ℝ) (p : ℕ) :
    (∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / (p : ℝ)
      = (∑ j ∈ range T,
          (∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)) / T := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have key : ∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)
      = (∑ j ∈ range T, ∑ m ∈ range p,
          slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / T := by
    rw [Finset.sum_comm, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => rfl
  rw [key, ← Finset.sum_div, div_div, div_div, mul_comm]

/-- **The fixed-state analogue of `RefCesaro`.**  For every state and every block length the
Cesàro average of the block average along a CF-normal orbit converges, to a limit that does not
depend on the input.  (S7-RC is the case `s = refState`.) -/
theorem blockCesaro_holds {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a) (T : ℕ) (hT : 0 < T) :
    ∃ L : ℝ, ∀ x : ℝ, IsCFNormal x → (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      Tendsto (fun p => (∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / p) atTop (nhds L) := by
  classical
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  set ι := {x : ℝ // IsCFNormal x ∧ ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1} with hι
  have hmain : ∃ L : ℝ, ∀ i : ι,
      Tendsto (fun p => (∑ m ∈ range p, blockAvg s T w (gaussMap^[m] i.1)) / (p : ℝ))
        atTop (nhds L) := by
    refine exists_uniform_limit_of_approx (fun ε hε => ?_)
    choose Bf hBf using fun j : ℕ => exists_eventually_abs_levelAt_sub_le s hw j hε
    refine ⟨(∑ j ∈ range T, levelAt s w j (Bf j)) / T, fun i => ?_⟩
    have hall : ∀ᶠ p : ℕ in atTop, ∀ j ∈ range T,
        |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] i.1))) / (p : ℝ)
          - levelAt s w j (Bf j)| ≤ ε := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact hBf j i.1 i.2.1 i.2.2
    filter_upwards [hall] with p hp
    have hsplit : (∑ m ∈ range p, blockAvg s T w (gaussMap^[m] i.1)) / (p : ℝ)
        - (∑ j ∈ range T, levelAt s w j (Bf j)) / T
        = (∑ j ∈ range T,
            ((∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] i.1))) / (p : ℝ)
              - levelAt s w j (Bf j))) / T := by
      rw [sum_blockAvg_div_eq_at s w hT i.1 p, ← sub_div, ← Finset.sum_sub_distrib]
    rw [hsplit, abs_div, abs_of_pos hTR, div_le_iff₀ hTR]
    calc |∑ j ∈ range T,
            ((∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] i.1))) / (p : ℝ)
              - levelAt s w j (Bf j))|
        ≤ ∑ j ∈ range T,
            |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] i.1))) / (p : ℝ)
              - levelAt s w j (Bf j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range T, ε := Finset.sum_le_sum fun j hj => hp j hj
      _ = ε * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  obtain ⟨L, hL⟩ := hmain
  exact ⟨L, fun x hx horb => hL ⟨x, hx, horb⟩⟩

/-! ## The crux's fixed-state coordinate, as arithmetic

The Cesàro average of the block average is, up to any tolerance and UNIFORMLY in the state and in
the input, the finite arithmetic sum `Σ_{j<T} levelAt s w j (Bf j) / T` of relative Gauss masses.
So the fixed-state coordinate of the crux is the arithmetic assertion that this sum is close to
`γ(I_w)` for every wide state — with no dynamics, no normality and no limits left in it.
-/

/-- **The uniform bridge.**  One digit-bound schedule `Bf`, good for EVERY state and every
CF-normal input at once: the Cesàro average of the block average is within `ε` of the finite sum of
relative masses. -/
theorem exists_Bf_abs_blockAvgCesaro_sub_levelSum_le {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a)
    {T : ℕ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ Bf : ℕ → ℕ, ∀ (s : MapState) (x : ℝ), IsCFNormal x →
      (∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        |(∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ j ∈ range T, levelAt s w j (Bf j)) / T| ≤ ε := by
  classical
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  choose Bf hBf using fun j : ℕ => exists_eventually_abs_levelAt_sub_le' hw j hε
  refine ⟨Bf, fun s x hx horb => ?_⟩
  have hall : ∀ᶠ p : ℕ in atTop, ∀ j ∈ range T,
      |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
        - levelAt s w j (Bf j)| ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro j _
    exact hBf j s x hx horb
  filter_upwards [hall] with p hp
  have hsplit : (∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / (p : ℝ)
      - (∑ j ∈ range T, levelAt s w j (Bf j)) / T
      = (∑ j ∈ range T,
          ((∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
            - levelAt s w j (Bf j))) / T := by
    rw [sum_blockAvg_div_eq_at s w hT x p, ← sub_div, ← Finset.sum_sub_distrib]
  rw [hsplit, abs_div, abs_of_pos hTR, div_le_iff₀ hTR]
  calc |∑ j ∈ range T,
          ((∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
            - levelAt s w j (Bf j))|
      ≤ ∑ j ∈ range T,
          |(∑ m ∈ range p, slotObs w (pairStep^[j] (s, gaussMap^[m] x))) / (p : ℝ)
            - levelAt s w j (Bf j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range T, ε := Finset.sum_le_sum fun j hj => hp j hj
    _ = ε * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The crux's fixed-state coordinate is arithmetic.**  If, at the digit-bound schedule the
bridge hands out, the finite sums of relative masses are within `ε` of `γ(I_w)` for every state of
width at least `η`, then for every such state and every CF-normal input the block average's Cesàro
limit is within `2ε` of `γ(I_w)`.  The hypothesis mentions no dynamics: `levelAt` is a finite sum
of relative Gauss masses of explicit order-connected sets. -/
theorem abs_blockAvgCesaro_sub_gauss_le_of_levelSum {w : List ℕ} (hw : ∀ a ∈ w, 1 ≤ a)
    {T : ℕ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) {η : ℝ} :
    ∃ Bf : ℕ → ℕ,
      (∀ s : MapState, η ≤ s.width →
          |(∑ j ∈ range T, levelAt s w j (Bf j)) / T
            - (gaussMeasure (cfCylinder w)).toReal| ≤ ε) →
      ∀ (s : MapState), η ≤ s.width → ∀ (x : ℝ), IsCFNormal x →
        (∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
        ∀ᶠ p : ℕ in atTop,
          |(∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / (p : ℝ)
            - (gaussMeasure (cfCylinder w)).toReal| ≤ 2 * ε := by
  obtain ⟨Bf, hBf⟩ := exists_Bf_abs_blockAvgCesaro_sub_levelSum_le hw hT hε
  refine ⟨Bf, fun hsum s hs x hx horb => ?_⟩
  filter_upwards [hBf s x hx horb] with p hp
  have h2 := hsum s hs
  have := abs_add_le ((∑ m ∈ range p, blockAvg s T w (gaussMap^[m] x)) / (p : ℝ)
      - (∑ j ∈ range T, levelAt s w j (Bf j)) / T)
    ((∑ j ∈ range T, levelAt s w j (Bf j)) / T - (gaussMeasure (cfCylinder w)).toReal)
  simp only [sub_add_sub_cancel] at this
  linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.exists_eventually_abs_levelAt_sub_le'
#print axioms NormalNumbers.VandeheyS7.MapState.blockCesaro_holds
#print axioms NormalNumbers.VandeheyS7.MapState.exists_Bf_abs_blockAvgCesaro_sub_levelSum_le
#print axioms NormalNumbers.VandeheyS7.MapState.abs_blockAvgCesaro_sub_gauss_le_of_levelSum

end Audit
