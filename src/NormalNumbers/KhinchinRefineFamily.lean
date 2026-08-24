/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KhinchinFamily
import NormalNumbers.KhinchinRefine

/-!
# W5 (Khinchin, FAMILY form) — threading the summable log-tail family (route C′)

Family analogue of `TBrick.exists_refinement_uniform_khinchin`
(`KhinchinRefine.lean`): the refined brick's extension word `u` carries the
log-tail guarantee at EVERY family index `j < tK` simultaneously (not a
single level-tied `(K, η)` pair) — the corrected design from
`KhinchinFamily.lean`'s module docstring.
-/

namespace NormalNumbers

open MeasureTheory

/-- **B–Y Lemma 13, `t' = t` case, Khinchin FAMILY form.** Mirrors
`TBrick.exists_refinement_uniform_khinchin` (`KhinchinRefine.lean`) with the
log-tail payload holding at EVERY family index `j < tK`. -/
theorem TBrick.exists_refinement_uniform_khinchin_family (t : ℕ)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a)
    (hFne : ∀ v ∈ F, v ≠ [])
    {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1)
    {C : ℝ}
    (hhalf : ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤ 2 * volume (goodExtSet w C n)) :
    ∃ kmin₀ : ℕ, ∀ kmin, kmin₀ ≤ kmin → ∃ N : ℕ,
      ∀ (B : TBrick t) (n : ℕ), N ≤ n → 0 < n → ∀ tK : ℕ,
      ∃ (B' : TBrick t) (u : List ℕ),
        B'.w = B.w ++ u ∧ u.length = n ∧ (∀ a ∈ u, 1 ≤ a) ∧
        (cfK u : ℝ) ≤ Real.exp (C * n) ∧
        (∀ v ∈ F, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * n| < δ * n + v.length) ∧
        (∀ d, 2 ≤ d → d ≤ t → B.m d + kmin ≤ B'.m d) ∧
        (∀ d, 2 ≤ d → d ≤ t → ∀ y ∈ cfCylinder B'.w,
          ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
            ∃ β : Fin (B'.m d - B.m d) → Fin d,
              β ∉ badBlocks d (B'.m d - B.m d) ε ∧
              y ∈ daryCell d (B.m d + (B'.m d - B.m d))
                ((B.j d + i) * d ^ (B'.m d - B.m d)
                  + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1) ∧
        (∀ j, j < tK → (u.map (fun a : ℕ =>
            if khinchinK j < a then Real.log (a : ℝ) else 0)).sum
          ≤ khinchinEta j * n) := by
  obtain ⟨N₁, kmin₀, hmain⟩ :=
    exists_good_avoiding_bad_of_large_khinchin_family t F hF hδ hε0 hεt hhalf
  refine ⟨kmin₀, fun kmin hkmin => ?_⟩
  obtain ⟨N₂, hN₂⟩ := exists_fib_threshold (4 * (t : ℝ) ^ kmin)
  refine ⟨max N₁ N₂, fun B n hn hn0 tK => ?_⟩
  obtain ⟨x, hxG, hirr, hnotbad⟩ :=
    hmain B n (le_trans (le_max_left _ _) hn) hn0 kmin hkmin tK
  obtain ⟨u, huGen, hKlen, hxJ⟩ := exists_word_of_mem_goodExtSet hxG
  obtain ⟨hulen, hupos⟩ := huGen
  have hu_ne : u ≠ [] := by
    intro h
    rw [h] at hulen
    simp at hulen
    omega
  have hwu_ne : B.w ++ u ≠ [] := by simp [B.hw_ne]
  have hwu_pos : ∀ a ∈ B.w ++ u, 1 ≤ a := fun a ha =>
    (List.mem_append.1 ha).elim (B.hw_pos a) (hupos a)
  have hfib : ∀ d, 2 ≤ d → d ≤ t →
      4 * (d : ℝ) ^ kmin < (Nat.fib (u.length + 1) : ℝ) ^ 2 := by
    intro d hd2 hdt
    have hdt' : (d : ℝ) ≤ t := by exact_mod_cast hdt
    have h1 : (d : ℝ) ^ kmin ≤ (t : ℝ) ^ kmin :=
      pow_le_pow_left₀ (by positivity) hdt' _
    have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [hulen]
    linarith
  have hspec : ∀ d, 2 ≤ d → d ≤ t → ∃ m' : ℕ, ∃ j' : ℤ,
      B.m d + kmin ≤ m' ∧
      cfCylinder (B.w ++ u) ⊆ daryCell d m' j' 2 ∧
      ENNReal.ofReal ((d : ℝ) ^ m')⁻¹
        ≤ ENNReal.ofReal (2 * d) * volume (cfCylinder (B.w ++ u)) :=
    fun d hd2 hdt =>
      B.exists_refined_cell hd2 hdt hu_ne hupos kmin (hfib d hd2 hdt)
  choose! m' j' hm hsubJ hrat using hspec
  refine ⟨⟨B.w ++ u, hwu_ne, hwu_pos, m', j', fun _ => 2,
    fun _ _ _ => by norm_num, fun _ _ _ => le_refl 2, hsubJ, hrat⟩,
    u, rfl, hulen, hupos, hKlen, ?_, hm, ?_, ?_⟩
  · intro v hv
    have hxw : x ∈ cfCylinder B.w := cfCylinder_append_subset _ _ hxJ
    have hnotCF : x ∉ cfBadZone B.w v n δ :=
      fun h => hnotbad (Or.inl (Set.mem_biUnion hv h))
    have habs := abs_blockCount_lt_of_notMem_cfBadZone hxw hirr hnotCF
    have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1 :=
      fun j => (irrational_orbit x hirr hxJ.1 j).2
    have hbr := blockCount_sub_countOccurrences_bounds horb v (hFne v hv)
      B.w.length n
    have hword : (List.range n).map (fun i => cfDigit x (B.w.length + i))
        = u := by
      rw [← hulen]
      exact range_map_cfDigit_eq hxJ
    rw [hword] at hbr
    obtain ⟨hbr1, hbr2⟩ := hbr
    set bc : ℝ := blockCount (cfCylinder v) n (gaussMap^[B.w.length] x)
      with hbc
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
  · intro d hd2 hdt y hy
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
    have hmk : B.m d + (m' d - B.m d) = m' d := by
      have := hm d hd2 hdt
      omega
    have hyw : y ∈ cfCylinder B.w := cfCylinder_append_subset _ _ hy
    obtain ⟨i, hir, hyi⟩ := mem_daryCell_split hd1 (B.hsub d hd2 hdt hyw)
    have hi2 : i < 2 := lt_of_lt_of_le hir (B.hr2 d hd2 hdt)
    have havoid : x ∉ daryBadZoneWide d (B.m d) (B.j d + i) ε
        (m' d - B.m d) := by
      intro hmem
      apply hnotbad
      right
      left
      refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hd2, hdt⟩) ?_
      refine Set.mem_biUnion (Finset.mem_range.2 hi2) ?_
      refine Set.mem_iUnion.2 ⟨m' d - B.m d, Set.mem_iUnion.2 ⟨?_, hmem⟩⟩
      have := hm d hd2 hdt
      omega
    have hxc : x ∈ daryCell d (B.m d + (m' d - B.m d)) (j' d) 2 := by
      rw [hmk]
      exact hsubJ d hd2 hdt hxJ
    have hyc : y ∈ daryCell d (B.m d + (m' d - B.m d)) (j' d) 2 := by
      rw [hmk]
      exact hsubJ d hd2 hdt hy
    obtain ⟨β, hβgood, hymem⟩ := goodBlock_transfer d (B.m d)
      (m' d - B.m d) hd1 (j' d) hyi hxc hyc havoid
    exact ⟨i, hi2, hyi, β, hβgood, hymem⟩
  · -- the log-tail payload, from `x ∉ ⋃ j < tK, logBadZone B.w n (khinchinK j) (khinchinEta j)`
    intro j hj
    have hxw : x ∈ cfCylinder B.w := cfCylinder_append_subset _ _ hxJ
    have hnotlog : x ∉ logBadZone B.w n (khinchinK j) (khinchinEta j) :=
      fun h => hnotbad (Or.inr (Or.inr (Set.mem_biUnion (Finset.mem_range.2 hj) h)))
    have horbw : gaussMap^[B.w.length] x ∈ Set.Ioo (0 : ℝ) 1 :=
      (irrational_orbit x hirr hxJ.1 B.w.length).2
    have hle : logBirkhoffSum (khinchinK j) n (gaussMap^[B.w.length] x)
        ≤ khinchinEta j * n := by
      by_contra hlt
      push_neg at hlt
      exact hnotlog ⟨hxw, horbw, hlt⟩
    have hshift := logBirkhoffSum_shift (khinchinK j) n B.w.length x
    rw [hshift] at hle
    have hword : (List.range n).map (fun i => cfDigit x (B.w.length + i))
        = u := by
      rw [← hulen]
      exact range_map_cfDigit_eq hxJ
    have hsum_eq : (u.map (fun a : ℕ => if khinchinK j < a then Real.log (a : ℝ) else 0)).sum
        = ∑ i ∈ Finset.range n,
            (if khinchinK j < cfDigit x (B.w.length + i) then
              Real.log ((cfDigit x (B.w.length + i) : ℕ) : ℝ) else 0) := by
      rw [finset_sum_range_eq_list_sum', ← hword, List.map_map]
      rfl
    rw [hsum_eq]
    exact hle

end NormalNumbers
