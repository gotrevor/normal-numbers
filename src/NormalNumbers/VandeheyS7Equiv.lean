/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-Q: the word crux and the interval crux are the SAME statement

`orbitACBound_of_orbitCellBound` (lap 29) goes from cells to intervals.  This module closes the
loop in the other direction, at the level of the lap-43 crux: an interval bound gives the word
bound, because a cylinder *is* an interval along an irrational orbit.

* `cfCylinder_subset_uIcc` puts `I_w` inside the closed interval between `cfVal w` and
  `cfVal (bumpLast w)`, whose endpoints are rational — so an irrational orbit point of `I_w` lies
  in the OPEN interval, and `blockCount (cfCylinder w) ≤ blockCount (Ioo …)`.
* `gaussMeasure_cfCylinder` makes the interval's length at most `2 log 2` times the cylinder's
  Gauss mass (`sub_le_gaussMeasure_cfCylinder`), since `log(1+M) − log(1+m) ≥ (M−m)/(1+M)` and
  `M ≤ 1`.

Hence `orbitWordBound_of_orbitACBound : OrbitACBound q r₀ C → OrbitWordBound q r₀ (2 log 2 · C)`.
With lap 43 (`orbitCellBound_of_orbitWordBound`) and lap 29 the three formulations of the crux —
intervals, words, cells — are now mutually derivable, so the route has exactly ONE crux and the
choice of shape is free.
-/
import NormalNumbers.VandeheyS7Reduce

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers


/-- Digits of `bumpLast` stay positive (local copy: the original is file-private). -/
lemma bumpLast_pos' {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) : ∀ a ∈ bumpLast w, 1 ≤ a := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact hpos a (List.mem_of_mem_dropLast h)
  · simp only [List.mem_singleton] at h; omega

/-- `cfVal w ∈ [0,1]` for positive digits (local copy: the original is file-private). -/
lemma cfVal_mem_Icc' (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) : cfVal w ∈ Set.Icc (0 : ℚ) 1 := by
  induction w with
  | nil => simp [cfVal]
  | cons a m ih =>
      have ha : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hpos a (by simp)
      obtain ⟨h0, h1⟩ := ih fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have hd : (0 : ℚ) < (a : ℚ) + cfVal m := by linarith
      constructor
      · rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl]; positivity
      · rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl, div_le_one hd]; linarith

/-- The cylinder's interval length is at most `2 log 2` times its Gauss mass. -/
theorem sub_le_gaussMeasure_cfCylinder (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    max ((cfVal w : ℚ) : ℝ) ((cfVal (bumpLast w) : ℚ) : ℝ)
        - min ((cfVal w : ℚ) : ℝ) ((cfVal (bumpLast w) : ℚ) : ℝ)
      ≤ 2 * Real.log 2 * (gaussMeasure (cfCylinder w)).toReal := by
  set E0 : ℝ := ((cfVal w : ℚ) : ℝ) with hE0
  set E1 : ℝ := ((cfVal (bumpLast w) : ℚ) : ℝ) with hE1
  have hE0mem : E0 ∈ Set.Icc (0:ℝ) 1 := by
    have h := Set.mem_Icc.1 (cfVal_mem_Icc' w hpos)
    exact Set.mem_Icc.2 ⟨by rw [hE0]; exact_mod_cast h.1, by rw [hE0]; exact_mod_cast h.2⟩
  have hE1mem : E1 ∈ Set.Icc (0:ℝ) 1 := by
    have h := Set.mem_Icc.1 (cfVal_mem_Icc' (bumpLast w) (bumpLast_pos' hpos))
    exact Set.mem_Icc.2 ⟨by rw [hE1]; exact_mod_cast h.1, by rw [hE1]; exact_mod_cast h.2⟩
  set M : ℝ := max E0 E1 with hM
  set m : ℝ := min E0 E1 with hm
  have hm0 : 0 ≤ m := le_min hE0mem.1 hE1mem.1
  have hM1 : M ≤ 1 := max_le hE0mem.2 hE1mem.2
  have hmM : m ≤ M := min_le_max
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `log(1+M) − log(1+m) ≥ (M−m)/2`
  have hkey : (M - m) / 2 ≤ Real.log (1 + M) - Real.log (1 + m) := by
    have h1 : (0:ℝ) < 1 + m := by linarith
    have h2 : (0:ℝ) < 1 + M := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at h
    have heq : (1 + m) / (1 + M) - 1 = -((M - m) / (1 + M)) := by field_simp; ring
    rw [heq] at h
    have h3 : (M - m) / 2 ≤ (M - m) / (1 + M) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    linarith
  have hmeas := gaussMeasure_cfCylinder w hw hpos
  have htoReal : (gaussMeasure (cfCylinder w)).toReal
      = (Real.log (1 + M) - Real.log (1 + m)) / Real.log 2 := by
    rw [hmeas, ENNReal.toReal_ofReal (by
      have : Real.log (1 + m) ≤ Real.log (1 + M) :=
        Real.log_le_log (by linarith) (by linarith)
      positivity)]
  rw [htoReal]
  rw [show 2 * Real.log 2 * ((Real.log (1 + M) - Real.log (1 + m)) / Real.log 2)
      = 2 * (Real.log (1 + M) - Real.log (1 + m)) by field_simp]
  linarith

/-- **The interval crux gives the word crux.** -/
theorem orbitWordBound_of_orbitACBound {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀)
    (hac : OrbitACBound q r₀ C) : OrbitWordBound q r₀ (2 * Real.log 2 * C) := by
  intro x hx w hw ε hε
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set y := Int.fract (q * x + r₀) with hy
  by_cases hnil : w = []
  · subst hnil
    have h := hac x hx 0 1 le_rfl (by norm_num) le_rfl ε hε
    refine h.mono fun p hp => ?_
    have hset : blockCount (cfCylinder ([] : List ℕ)) p y = blockCount (Set.Ioo (0:ℝ) 1) p y := by
      rw [cfCylinder_nil]
    rw [hset]
    have hmass : (1:ℝ) ≤ (gaussMeasure (cfCylinder ([] : List ℕ))).toReal := by
      rw [cfCylinder_nil, ← cellSet_nil_one]
      exact le_of_eq gaussMeasure_cellSet_nil_one.symm
    have h2 : (1:ℝ) ≤ 2 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    nlinarith [hp, mul_nonneg hC (by linarith : (0:ℝ) ≤ 2 * Real.log 2)]
  · have hE0mem : ((cfVal w : ℚ) : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      have h := Set.mem_Icc.1 (cfVal_mem_Icc' w hw)
      exact Set.mem_Icc.2 ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hE1mem : ((cfVal (bumpLast w) : ℚ) : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      have h := Set.mem_Icc.1 (cfVal_mem_Icc' (bumpLast w) (bumpLast_pos' hw))
      exact Set.mem_Icc.2 ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    set E0 : ℝ := ((cfVal w : ℚ) : ℝ) with hE0
    set E1 : ℝ := ((cfVal (bumpLast w) : ℚ) : ℝ) with hE1
    set M : ℝ := max E0 E1 with hM
    set m : ℝ := min E0 E1 with hm
    have hm0 : (0:ℝ) ≤ m := le_min hE0mem.1 hE1mem.1
    have hM1 : M ≤ 1 := max_le hE0mem.2 hE1mem.2
    have hmM : m ≤ M := min_le_max
    have hne0 : ∀ t : ℝ, Irrational t → t ≠ E0 := fun t ht h => ht ⟨cfVal w, h.symm⟩
    have hne1 : ∀ t : ℝ, Irrational t → t ≠ E1 := fun t ht h => ht ⟨cfVal (bumpLast w), h.symm⟩
    have hsub : ∀ t : ℝ, Irrational t → t ∈ Set.Ioo (0:ℝ) 1 → t ∈ cfCylinder w →
        t ∈ Set.Ioo m M := by
      intro t htirr _ ht
      have h := cfCylinder_subset_uIcc w hnil hw ht
      rw [Set.uIcc, Set.mem_Icc] at h
      refine ⟨lt_of_le_of_ne h.1 ?_, lt_of_le_of_ne h.2 ?_⟩
      · rcases min_choice E0 E1 with hc | hc
        · rw [hm, hc]; exact fun hcon => hne0 t htirr hcon.symm
        · rw [hm, hc]; exact fun hcon => hne1 t htirr hcon.symm
      · rcases max_choice E0 E1 with hc | hc
        · rw [hM, hc]; exact fun hcon => hne0 t htirr hcon
        · rw [hM, hc]; exact fun hcon => hne1 t htirr hcon
    obtain ⟨hyirr, hymem⟩ := irrational_fract_mem (by
      have : Irrational (q * x + r₀) := by
        exact hirr x hx
      exact this)
    have h := hac x hx m M hm0 hmM hM1 ε hε
    refine h.mono fun p hp => ?_
    have hcount : blockCount (cfCylinder w) p y ≤ blockCount (Set.Ioo m M) p y :=
      blockCount_le_of_irrational_subset hyirr hymem hsub p
    have hmass := sub_le_gaussMeasure_cfCylinder w hnil hw
    have hppos : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
    have hdiv : blockCount (cfCylinder w) p y / p ≤ blockCount (Set.Ioo m M) p y / p := by
      gcongr
    have hCm : C * (M - m) ≤ C * (2 * Real.log 2 * (gaussMeasure (cfCylinder w)).toReal) :=
      mul_le_mul_of_nonneg_left hmass hC
    calc blockCount (cfCylinder w) p y / p ≤ blockCount (Set.Ioo m M) p y / p := hdiv
      _ ≤ C * (M - m) + ε := hp
      _ ≤ 2 * Real.log 2 * C * (gaussMeasure (cfCylinder w)).toReal + ε := by nlinarith

section Audit

#print axioms sub_le_gaussMeasure_cfCylinder
#print axioms orbitWordBound_of_orbitACBound

end Audit

end NormalNumbers.VandeheyS7
