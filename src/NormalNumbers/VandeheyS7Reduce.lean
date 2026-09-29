/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-C2: the threshold parameter is free — `OrbitCellBound` collapses to its `T = 1` case

Laps 38–42 closed every counting-side lane and left the crux in its irreducible form:
"the tail cell's visits are spread across the length-`n` words in proportion to `γ(I_w)`".
This module draws the consequence: the threshold `T` carries **no content at all**.

`OrbitWordBound q r₀ C` is the `T = 1` statement — an upper bound on the frequency of every
finite word in the image expansion, `freq(I_w) ≤ C γ(I_w) + ε`.  The theorem
`orbitCellBound_of_orbitWordBound` shows that it plus a Lévy bound on the image gives the full
`OrbitCellBound q r₀ C`.  The mechanism has three steps, all already in the repo:

* `cellSet w T` splits, along irrational points, as the finite union `⋃_{T ≤ a ≤ S} I_{w ++ [a]}`
  together with the residual cell `cellSet w (S+1)` (`cellSet_subset_union`);
* the residual is controlled by the FREE tightness bound — `blockCount_cellSet_le_shift` (lap 41)
  reduces it to the tail cell, and `tailFreq_le_of_levyBound` makes that `≤ Λ / log (S+1)`,
  which `tendsto_freeRate` sends to `0`;
* the finitely many cylinders are handed to the hypothesis, and their Gauss masses sum to at most
  `γ(cellSet w T)` because they are disjoint subsets of it (`sum_gaussMeasure_cfCylinder_le`).

**Consequence for the route.**  The crux is now a *one-parameter-free* statement: every remaining
line of Vandehey §7 Problem 1 rests on "the image expansion of a CF-normal `x` does not
over-represent any finite word", plus the cited `GaussACRigidity`.  The thresholds, the
Diophantine counting, the tail law and the bootstrap are all discharged or refuted.
-/
import NormalNumbers.VandeheyS7Boot
import NormalNumbers.VandeheyS7Tight

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The `T = 1` crux.**  An upper bound on the frequency of every finite word in the image
expansion of a CF-normal `x`. -/
def OrbitWordBound (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop,
      blockCount (cfCylinder w) p (Int.fract (q * x + r₀)) / p
        ≤ C * (gaussMeasure (cfCylinder w)).toReal + ε

/-- A point of `I_{w ++ [a]}` with `T ≤ a` lies in `cellSet w T`. -/
lemma mem_cellSet_of_mem_cfCylinder_snoc {w : List ℕ} {T a : ℕ} (hTa : T ≤ a) {t : ℝ}
    (ht : t ∈ cfCylinder (w ++ [a])) : t ∈ cellSet w T := by
  have hdig : cfDigit t w.length = a := by
    have h := ht.2 w.length (by simp)
    simpa using h
  refine ⟨⟨ht.1, fun i hi => ?_⟩, ?_⟩
  · have h := ht.2 i (by simp; omega)
    rwa [List.getD_append _ _ _ _ hi] at h
  · show T ≤ cfDigit t w.length
    rw [hdig]; exact hTa

/-- **The split.**  Along irrational points the cell is covered by the finitely many cylinders
`I_{w ++ [a]}`, `T ≤ a ≤ S`, together with the residual cell at threshold `S + 1`. -/
lemma cellSet_subset_union {w : List ℕ} {T S : ℕ} {t : ℝ} (ht : t ∈ cellSet w T) :
    t ∈ (⋃ a ∈ Finset.Icc T S, cfCylinder (w ++ [a])) ∪ cellSet w (S + 1) := by
  obtain ⟨hIw, hd⟩ := ht
  rcases Nat.lt_or_ge S (cfDigit t w.length) with h | h
  · refine Or.inr ⟨hIw, ?_⟩
    show S + 1 ≤ cfDigit t w.length
    omega
  · refine Or.inl ?_
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hd, h⟩) ?_
    exact mem_cfCylinder_snoc hIw

/-- The Gauss masses of the pieces sum to at most the mass of the cell they cover. -/
lemma sum_gaussMeasure_cfCylinder_le (w : List ℕ) (T S : ℕ) :
    ∑ a ∈ Finset.Icc T S, (gaussMeasure (cfCylinder (w ++ [a]))).toReal
      ≤ (gaussMeasure (cellSet w T)).toReal := by
  classical
  have hdisj : (↑(Finset.Icc T S) : Set ℕ).PairwiseDisjoint
      (fun a => cfCylinder (w ++ [a])) := by
    intro a _ b _ hne
    exact cfCylinder_disjoint_of_length_eq (by simp) (by
      intro h
      exact hne (by simpa using congrArg (fun l => List.getD l w.length 0) h))
  have hmeas : ∀ a ∈ Finset.Icc T S, MeasurableSet (cfCylinder (w ++ [a])) :=
    fun a _ => measurableSet_cfCylinder _
  have hun : gaussMeasure (⋃ a ∈ Finset.Icc T S, cfCylinder (w ++ [a]))
      = ∑ a ∈ Finset.Icc T S, gaussMeasure (cfCylinder (w ++ [a])) :=
    measure_biUnion_finset hdisj hmeas
  have hsub : (⋃ a ∈ Finset.Icc T S, cfCylinder (w ++ [a])) ⊆ cellSet w T := by
    refine Set.iUnion₂_subset fun a ha => ?_
    exact fun t ht => mem_cellSet_of_mem_cfCylinder_snoc (Finset.mem_Icc.1 ha).1 ht
  have hle : ∑ a ∈ Finset.Icc T S, gaussMeasure (cfCylinder (w ++ [a]))
      ≤ gaussMeasure (cellSet w T) := hun ▸ measure_mono hsub
  have hfin : gaussMeasure (cellSet w T) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
  exact ENNReal.toReal_mono hfin hle

/-- **Tightness of the image's digit distribution** — the *minimal* second hypothesis.  It is
all that lap 43's reduction uses, and it is strictly weaker than a Lévy bound
(`imageTight_of_levyBound`). -/
def ImageTight (y : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 2 ≤ T ∧ ∀ᶠ p : ℕ in atTop, blockCount (cellSet [] T) p y / p ≤ ε

/-- A Lévy bound implies tightness: the free rate `Λ / log T` tends to `0`. -/
theorem imageTight_of_levyBound {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {Λ : ℝ} (hL : LevyBound y Λ) : ImageTight y := by
  intro ε hε
  obtain ⟨M, hM⟩ := ((tendsto_freeRate Λ).eventually
    (eventually_lt_nhds hε) |>.and (eventually_ge_atTop 2)).exists_forall_of_atTop
  obtain ⟨h1, h2⟩ := hM M le_rfl
  exact ⟨M, h2, (tailFreq_le_of_levyBound hy hmem hL h2).mono fun p hp => le_of_lt
    (lt_of_le_of_lt hp h1)⟩

/-- **The threshold is free.**  The `T = 1` word bound plus tightness of the image gives the
full cell bound. -/
theorem orbitCellBound_of_orbitWordBound {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀)
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) → ImageTight (Int.fract (q * x + r₀)))
    (hword : OrbitWordBound q r₀ C) : OrbitCellBound q r₀ C := by
  classical
  intro x hx w T hw hT ε hε
  obtain ⟨hyirr, hymem⟩ := irrational_fract_mem (hirr x hx)
  set y := Int.fract (q * x + r₀) with hy
  -- choose the truncation `S` so the residual is below `ε/4`
  obtain ⟨T₀, hT₀2, hT₀ev⟩ := htight x hx (ε/4) (by linarith)
  obtain ⟨S, hST, hS2, hSrate⟩ : ∃ S : ℕ, T ≤ S ∧ 2 ≤ S + 1 ∧
      ∀ᶠ p : ℕ in atTop, blockCount (cellSet [] (S+1)) p y / p ≤ ε / 4 := by
    refine ⟨max T (T₀ - 1), le_max_left _ _, by omega, ?_⟩
    refine hT₀ev.mono fun p hp => ?_
    refine le_trans (le_trans (div_le_div_of_nonneg_right ?_ ?_) le_rfl) hp
    · exact blockCount_le_of_irrational_subset hyirr hymem
        (fun t _ _ ht => cellSet_mono_threshold [] (by omega) ht) p
    · exact Nat.cast_nonneg p
  set F : Finset ℕ := Finset.Icc T S with hF
  set N : ℕ := F.card with hN
  have hNpos : (0:ℝ) < N + 1 := by positivity
  set ε' : ℝ := ε / (4 * (N + 1)) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  -- the finitely many cylinder bounds, and the residual bound
  have hcyl : ∀ a ∈ F, ∀ᶠ p : ℕ in atTop,
      blockCount (cfCylinder (w ++ [a])) p y / p
        ≤ C * (gaussMeasure (cfCylinder (w ++ [a]))).toReal + ε' := by
    intro a ha
    refine hword x hx (w ++ [a]) ?_ ε' hε'pos
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact hw e h
    · have : e = a := by simpa using h
      exact this ▸ le_trans hT (Finset.mem_Icc.1 ha).1
  have hres := hSrate
  obtain ⟨M, hM⟩ := (eventually_all_finset (I := F)
      (p := fun a p => blockCount (cfCylinder (w ++ [a])) p y / p
        ≤ C * (gaussMeasure (cfCylinder (w ++ [a]))).toReal + ε')).2 hcyl |>.and
    (hres.and (eventually_gt_atTop (max 1 ⌈(4 * (w.length : ℝ)) / ε⌉₊))) |>.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop M] with p hp
  obtain ⟨hall, hrest, hbig⟩ := hM p hp
  have hppos : (0:ℝ) < p := by
    have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt (le_max_left 1 _) hbig)
    exact_mod_cast this
  -- step 1: the split
  have hsplit : blockCount (cellSet w T) p y
      ≤ (∑ a ∈ F, blockCount (cfCylinder (w ++ [a])) p y)
        + blockCount (cellSet w (S + 1)) p y := by
    refine le_trans (blockCount_le_of_irrational_subset hyirr hymem
      (fun t _ _ ht => cellSet_subset_union (S := S) ht) p) ?_
    refine le_trans (blockCount_union_le _ _ _ _) ?_
    have := blockCount_biUnion_le F (fun a => cfCylinder (w ++ [a])) p y
    linarith
  -- step 2: the residual
  have hresid : blockCount (cellSet w (S + 1)) p y / p ≤ ε / 4 + ε / 4 := by
    have h1 := blockCount_cellSet_le_shift hyirr hymem w (S + 1) p
    have h2 : (w.length : ℝ) / p ≤ ε / 4 := by
      rw [div_le_div_iff₀ hppos (by norm_num)]
      have : ((⌈(4 * (w.length : ℝ)) / ε⌉₊ : ℕ) : ℝ) < (p:ℝ) := by
        exact_mod_cast lt_of_le_of_lt (le_max_right 1 _) hbig
      have hceil : (4 * (w.length : ℝ)) / ε ≤ (⌈(4 * (w.length : ℝ)) / ε⌉₊ : ℝ) :=
        Nat.le_ceil _
      have : (4 * (w.length : ℝ)) / ε < (p:ℝ) := lt_of_le_of_lt hceil this
      rw [div_lt_iff₀ hε] at this
      linarith
    have h3 : blockCount (cellSet [] (S+1)) p y / p ≤ ε / 4 := hrest
    have h4 : blockCount (cellSet w (S + 1)) p y / p
        ≤ (blockCount (cellSet [] (S+1)) p y + (w.length : ℝ)) / p := by gcongr
    rw [add_div] at h4
    linarith
  -- step 3: assemble
  have hsum : (∑ a ∈ F, blockCount (cfCylinder (w ++ [a])) p y) / p
      ≤ C * (gaussMeasure (cellSet w T)).toReal + N * ε' := by
    rw [Finset.sum_div]
    have h1 : ∑ a ∈ F, blockCount (cfCylinder (w ++ [a])) p y / p
        ≤ ∑ a ∈ F, (C * (gaussMeasure (cfCylinder (w ++ [a]))).toReal + ε') :=
      Finset.sum_le_sum fun a ha => hall a ha
    have h2 : ∑ a ∈ F, (C * (gaussMeasure (cfCylinder (w ++ [a]))).toReal + ε')
        = C * (∑ a ∈ F, (gaussMeasure (cfCylinder (w ++ [a]))).toReal) + N * ε' := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [hN, hF]
    have h3 : C * (∑ a ∈ F, (gaussMeasure (cfCylinder (w ++ [a]))).toReal)
        ≤ C * (gaussMeasure (cellSet w T)).toReal :=
      mul_le_mul_of_nonneg_left (sum_gaussMeasure_cfCylinder_le w T S) hC
    linarith
  have hNε : (N:ℝ) * ε' ≤ ε / 4 := by
    rw [hε', ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε.le, Nat.cast_nonneg (α := ℝ) N]
  have hfinal : blockCount (cellSet w T) p y / p
      ≤ (∑ a ∈ F, blockCount (cfCylinder (w ++ [a])) p y) / p
        + blockCount (cellSet w (S + 1)) p y / p := by
    have h : blockCount (cellSet w T) p y / p
        ≤ ((∑ a ∈ F, blockCount (cfCylinder (w ++ [a])) p y)
            + blockCount (cellSet w (S + 1)) p y) / p := by gcongr
    rwa [add_div] at h
  linarith

section Audit

#print axioms orbitCellBound_of_orbitWordBound
#print axioms sum_gaussMeasure_cfCylinder_le
#print axioms imageTight_of_levyBound

end Audit

end NormalNumbers.VandeheyS7
