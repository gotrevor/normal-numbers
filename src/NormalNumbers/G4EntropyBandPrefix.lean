/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandSeq

/-!
# Entropy expedition — prefixes of a band

`tendsto_bandRead_freq` gives the correct word frequencies at the band cutoffs `bT (i+1)`.  This
module prices a cutoff *inside* a band: after `a` of band `i`'s windows, the read content is the
sub-collection `bandPre i a` of sample times, of relative size `a/|P_K|`, and a sample-time
restriction costs `(δ+1)/σ`.  So a prefix is certified as soon as `a ≫ |P_K|·δ/m_K`, i.e. as
soon as it is more than a `≈ K^{−1/2}` fraction of the band.

That is what turns the band cutoffs into a **density-one** set of cutoffs: only the first
`O(K^{−1/2})` fraction of each band is uncontrolled, and that fraction vanishes with the scale.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The prefix of a band -/

open Classical in
/-- The first `a` sample times of band `i`, in increasing order. -/
noncomputable def bandPre (i a : ℕ) : Finset ℕ := (Finset.range a).image (bnth i)

lemma bandPre_subset (i a : ℕ) (ha : a ≤ (bandS i).card) : bandPre i a ⊆ bandS i := by
  classical
  intro n hn
  rw [bandPre, Finset.mem_image] at hn
  obtain ⟨j, -, rfl⟩ := hn
  exact bnth_mem i j

lemma bandPre_subset_PK (i a : ℕ) (ha : a ≤ (bandS i).card) : bandPre i a ⊆ PK i :=
  fun n hn => bandS_subset i (bandPre_subset i a ha hn)

lemma card_bandPre (i a : ℕ) (ha : a ≤ (bandS i).card) : (bandPre i a).card = a := by
  classical
  rw [bandPre, Finset.card_image_of_injOn, Finset.card_range]
  intro j hj k hk hjk
  rcases Nat.lt_trichotomy j k with h | h | h
  · exact absurd hjk (by
      have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hk) ha)
      omega)
  · exact h
  · exact absurd hjk (by
      have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hj) ha)
      omega)

lemma bandPre_nonempty (i a : ℕ) (ha : 0 < a) : (bandPre i a).Nonempty := by
  classical
  refine ⟨bnth i 0, ?_⟩
  rw [bandPre, Finset.mem_image]
  exact ⟨0, Finset.mem_range.2 ha, rfl⟩

/-! ### The prefix law -/

open Classical in
/-- The window law at the good atom, restricted to the first `a` sample times of band `i`. -/
noncomputable def preLaw (i a : ℕ) (ha : 0 < a) (x : ℝ) : FinLaw (Unit → Fin (2 ^ kk i)) :=
  empirical (bandPre i a) (bandPre_nonempty i a ha)
    (fun n => fun _ : Unit => ZVec (gridAt i) (kk i) x n (goodAtom i))

open Classical in
lemma H₂_preLaw (i a : ℕ) (ha : 0 < a) (x : ℝ) :
    (preLaw i a ha x).H₂
      = (empirical (bandPre i a) (bandPre_nonempty i a ha)
          (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))).H₂ := by
  classical
  have hmap := (map_empirical (Ω := Fin (2 ^ kk i)) (Ω' := Unit → Fin (2 ^ kk i))
    (bandPre_nonempty i a ha) (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))
    (fun u => fun _ : Unit => u)).symm
  have hH := FinLaw.H₂_map_injective
    (empirical (bandPre i a) (bandPre_nonempty i a ha)
      (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i)))
    (g := fun u : Fin (2 ^ kk i) => fun _ : Unit => u) (fun u u' h => congrFun h ())
  rw [← hH, ← hmap]
  rfl

open Classical in
/-- **The prefix's deficit.**  A prefix of relative size `σ = a/|P_K|` costs `(δ+1)/σ`. -/
theorem H₂_preLaw_ge (i a : ℕ) (ha : 0 < a) (haS : a ≤ (bandS i).card) :
    (kk i : ℝ) - (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ)
      ≤ (preLaw i a ha (primeLambertAtBase 4)).H₂ := by
  classical
  set f : ℕ → Fin (2 ^ kk i) :=
    fun n => ZVec (gridAt i) (kk i) (primeLambertAtBase 4) n (goodAtom i) with hf
  have hfull : ((kk i : ℝ) - atomDeficit i) ≤ (empirical (PK i) (PK_nonempty i) f).H₂ := by
    have hmap := map_coord_jointLawAt i (primeLambertAtBase 4) (goodAtom i)
    have hd := goodAtom_deficit i
    rw [FinLaw.coordDeficit] at hd
    rw [hmap] at hd
    linarith
  have hrest := H₂_empirical_window_restrict_ge (m := kk i) (PK_nonempty i)
    (bandPre_nonempty i a ha) (bandPre_subset_PK i a haS) f (δ := atomDeficit i) hfull
  rw [card_bandPre i a haS] at hrest
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hdiv : (atomDeficit i + 1) / ((a : ℝ) / ((PK i).card : ℝ))
      = (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ) := by
    field_simp
  rw [hdiv] at hrest
  rw [H₂_preLaw]
  exact hrest

end NormalNumbers.G4.Sched
