/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFSchedule
import NormalNumbers.TBrickRefine
import NormalNumbers.CFWordBridge

/-!
# B6 — the daryCell-free CF frequency-good block engine

The single missing atom for the B6 interleaved schedule (`CFScheduleA`): a
purely continued-fraction refinement lemma that, for any genuine word `w`, any
finite family `F` of genuine CF patterns, and any tolerance `δ > 0`, produces
arbitrarily long **frequency-good** blocks `u` — every `v ∈ F` occurs in `u`
within `δ·|u| + |v|` of `γ(I_v)·|u|` — together with a witness irrational point
of `cfCylinder (w ++ u)`.

This is exactly the CF payload of `TBrick.exists_refinement_uniform`
(`TBrickRefine.lean`) with the base-`d` `daryCell` conclusion DROPPED.  The
extraction is clean: instantiate `exists_good_avoiding_bad_of_large` at level
`t = 1`, where `Finset.Icc 2 1 = ∅` makes the whole d-ary bad-zone union
vacuous, leaving only the CF bad zone to avoid.  A trivial `TBrick 1` on `w`
(all cell obligations are over `2 ≤ d ≤ 1`, hence vacuous) supplies the required
brick.

Additive only: no frozen B5′ module is edited.
-/

namespace NormalNumbers

open MeasureTheory

/-- A trivial `TBrick 1` on any genuine word: there are no active bases
(`2 ≤ d ≤ 1` is impossible), so every cell obligation is vacuous. -/
noncomputable def trivBrick (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : TBrick 1 where
  w := w
  hw_ne := hw
  hw_pos := hpos
  m := fun _ => 0
  j := fun _ => 0
  r := fun _ => 0
  hr1 := fun d hd2 hd1 => absurd (le_trans hd2 hd1) (by norm_num)
  hr2 := fun d hd2 hd1 => absurd (le_trans hd2 hd1) (by norm_num)
  hsub := fun d hd2 hd1 => absurd (le_trans hd2 hd1) (by norm_num)
  hratio := fun d hd2 hd1 => absurd (le_trans hd2 hd1) (by norm_num)

@[simp] theorem trivBrick_w (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : (trivBrick w hw hpos).w = w := rfl

/-- **The B6 CF frequency-good block engine.**  For a genuine word `w`, a finite
family `F` of genuine CF patterns, and `δ > 0`, there is a length threshold `N`
such that every length `n ≥ N` admits a genuine block `u` (`|u| = n`) whose CF
window frequencies match the Gauss measure to within `δ` for every `v ∈ F`, and
such that `cfCylinder (w ++ u)` contains an irrational point.  The daryCell-free
core of `TBrick.exists_refinement_uniform`. -/
theorem exists_freq_good_block (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (F : Finset (List ℕ))
    (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) (hFne : ∀ v ∈ F, v ≠ [])
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → 0 < n → ∃ u : List ℕ,
      u ≠ [] ∧ u.length = n ∧ (∀ a ∈ u, 1 ≤ a) ∧
      (∀ v ∈ F, |(countOccurrences v u : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
      (∃ x : ℝ, x ∈ cfCylinder (w ++ u) ∧ Irrational x) := by
  obtain ⟨N, kmin₀, hgood⟩ :=
    exists_good_avoiding_bad_of_large 1 F hF (δ := δ) (ε := 1) hδ
      one_pos (by norm_num) (C := goodC) goodC_half
  set B := trivBrick w hw hpos with hB
  refine ⟨N, fun n hn hn0 => ?_⟩
  obtain ⟨x, hxG, hirr, hnot⟩ := hgood B n hn hn0 kmin₀ (le_refl _)
  -- the d-ary union is empty (`Icc 2 1 = ∅`); avoidance reduces to the CF zone
  have hBw : B.w = w := rfl
  rw [hBw] at hxG hnot
  obtain ⟨u, huGen, hK, hxu⟩ := exists_word_of_mem_goodExtSet hxG
  obtain ⟨hulen, hupos⟩ := huGen
  have hune : u ≠ [] := by
    intro h; rw [h] at hulen; simp at hulen; omega
  have hxw : x ∈ cfCylinder w := cfCylinder_append_subset _ _ hxu
  have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
    fun j => (irrational_orbit x hirr hxw.1 j).2
  refine ⟨u, hune, hulen, hupos, ?_, ⟨x, hxu, hirr⟩⟩
  intro v hv
  have hnotCF : x ∉ cfBadZone w v n δ :=
    fun h => hnot (Or.inl (Set.mem_biUnion hv h))
  have habs := abs_blockCount_lt_of_notMem_cfBadZone hxw hirr hnotCF
  have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv) w.length n
  have hword : (List.range n).map (fun i => cfDigit x (w.length + i)) = u := by
    rw [← hulen]; exact range_map_cfDigit_eq hxu
  rw [hword] at hbr
  obtain ⟨hbr1, hbr2⟩ := hbr
  set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[w.length] x) with hbc
  set γv : ℝ := (gaussMeasure (cfCylinder v)).toReal with hγv
  have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
  have habs' : |bc - γv * n| < δ * n := by
    have h1 : bc / n - γv = (bc - γv * n) / n := by field_simp
    rw [h1, abs_div, abs_of_pos hn0R, div_lt_iff₀ hn0R] at habs
    linarith [habs]
  rw [abs_lt] at habs' ⊢
  have hv0 : (0 : ℝ) ≤ v.length := by positivity
  constructor
  · linarith
  · linarith

end NormalNumbers
