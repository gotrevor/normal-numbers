/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWOverhang

/-!
# The mid-band sandwich

The pieces are all in place:

* `prod_cutLo_subset_pairsLe` / `pairsLe_subset_prod_cutHi` — the prefix pair set is bracketed
  between two **product** collections (`G4EntropyWTrunc`);
* `abs_occ_bandWtr_sub_le` — each product collection's occurrence count is certified
  (`G4EntropyWCount`);
* `card_flank_ratio` — the two flanks' sample counts agree to `1 + 16/K` (`G4EntropyWSandwich`);
* `overhang_gen_le_band` — the prefix's multiplicity overhang is `≤ 8·|bandWtr i (cutHi i c)|`
  (`G4EntropyWOverhang`);
* `fullGoodWPre_eq` / `startsOf_pairsLe` — the prefix read count is the start sum of `pairsLe`.

This module bolts them together.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The gate propagates to both flanks -/

lemma P₀_le_wFloor (i : ℕ) : (gridAt i).P₀ ≤ wFloor i := by
  have h := KK_mul_P₀_le_wFloor i
  have hK := KK_pos i
  have : (gridAt i).P₀ ≤ KK i * (gridAt i).P₀ := Nat.le_mul_of_pos_left _ hK
  omega

lemma gate_cutLo (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutLo i c := by
  have := P₀_le_wFloor i
  omega

lemma gate_cutHi (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutHi i c :=
  le_trans (gate_cutLo i c hg) (cutLo_le_cutHi i c)

/-! ### The prefix start sum, and its two flank sums -/

open Classical in
/-- The prefix read count is the start sum of the prefix pair set. -/
theorem fullGoodWPre_eq_startsOf (i c : ℕ) (x : ℝ) (v : List ℕ) :
    (fullGoodWPre i (aLe i c) x v : ℕ)
      = ∑ q ∈ startsOf i (pairsLe i c), winOccW i x v q := by
  rw [startsOf_pairsLe, fullGoodWPre_eq]
  rfl

open Classical in
/-- **The sum sandwich**: the prefix pair sum sits between the two flanks' pair sums. -/
theorem sum_pairsLe_sandwich (i c : ℕ) (x : ℝ) (v : List ℕ) (hle : cutLo i c ≤ wTop i) :
    ∑ z ∈ (bandWtr i (cutLo i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
        winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      ≤ ∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) ∧
    ∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      ≤ ∑ z ∈ (bandWtr i (cutHi i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
          winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) := by
  constructor
  · exact Finset.sum_le_sum_of_subset (prod_cutLo_subset_pairsLe i c hle)
  · exact Finset.sum_le_sum_of_subset (pairsLe_subset_prod_cutHi i c)

/-! ### The certified flank sums -/

open Classical in
/-- **A flank's pair sum is certified.**  `|Σ_{X'} − 2^{−ℓ}·|bandWtr i X'|·|Atom|·(kk−ℓ+1)|
≤ ε·|bandWtr i X'|·|Atom|·(kk−ℓ+1)`, the multiplied-out form of `abs_occ_bandWtr_sub_le`. -/
theorem abs_flank_sum_sub_le (i X' : ℕ) (v : List ℕ)
    (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1)))
    (hlen : 0 < v.length) (hℓm : 2 * v.length ≤ kk i)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    |((∑ z ∈ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom),
          winOccW i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
        - 1 / (2 : ℝ) ^ v.length * (((bandWtr i X').card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i))
          * (((bandWtr i X').card : ℝ)
              * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))) := by
  classical
  have hcard : (0 : ℝ) < ((bandWtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (bandWtr_nonempty hg)
    exact_mod_cast this
  have hQ : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hF : (0 : ℝ) < ((kk i - v.length + 1 : ℕ) : ℝ) := by
    have : 0 < kk i - v.length + 1 := Nat.succ_pos _
    exact_mod_cast this
  set D : ℝ := ((bandWtr i X').card : ℝ)
      * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) with hDdef
  have hD : (0 : ℝ) < D := mul_pos hcard (mul_pos hQ hF)
  have hDne : D ≠ 0 := ne_of_gt hD
  set S : ℝ := ((∑ z ∈ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom),
      winOccW i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ) with hSdef
  have hmain := abs_occ_bandWtr_sub_le i X' v hg hhi hlen hℓm hv
  have hsum : (∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
          (((bandWtr i X').filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℝ)) = S := by
    rw [hSdef, ← Nat.cast_sum]
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ))
      (pairCount_prod_eq i (bandWtr i X') (primeLambertAtBase 4) v)
  rw [hsum] at hmain
  have hstep := mul_le_mul_of_nonneg_right hmain (le_of_lt hD)
  have hfac : S - 1 / (2 : ℝ) ^ v.length * D = (S / D - 1 / (2 : ℝ) ^ v.length) * D := by
    field_simp
  have hrw : |S - 1 / (2 : ℝ) ^ v.length * D| = |S / D - 1 / (2 : ℝ) ^ v.length| * D := by
    rw [hfac, abs_mul, abs_of_pos hD]
  rw [hrw]
  exact hstep

/-! ### The prefix window count against the flanks' sample counts -/

open Classical in
lemma aLe_eq_card_startsOf (i c : ℕ) : aLe i c = (startsOf i (pairsLe i c)).card := by
  rw [startsOf_pairsLe, aLe]

open Classical in
lemma card_prod_bandWtr (i X' : ℕ) :
    ((bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom)).card
      = (bandWtr i X').card * Fintype.card (gridAt i).Atom := by
  rw [Finset.card_product, Finset.card_univ]

open Classical in
/-- The prefix pair set contains the lower flank's product. -/
lemma card_pairsLe_ge (i c : ℕ) (hle : cutLo i c ≤ wTop i) :
    (bandWtr i (cutLo i c)).card * Fintype.card (gridAt i).Atom ≤ (pairsLe i c).card := by
  rw [← card_prod_bandWtr]
  exact Finset.card_le_card (prod_cutLo_subset_pairsLe i c hle)

open Classical in
/-- The prefix pair set sits inside the upper flank's product. -/
lemma card_pairsLe_le (i c : ℕ) :
    (pairsLe i c).card ≤ (bandWtr i (cutHi i c)).card * Fintype.card (gridAt i).Atom := by
  rw [← card_prod_bandWtr]
  exact Finset.card_le_card (pairsLe_subset_prod_cutHi i c)

open Classical in
/-- **The prefix window count is at least the lower flank's pair count, less the overhang.** -/
theorem aLe_ge_real (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) (hhi : cutHi i c ≤ wTop i) :
    ((bandWtr i (cutLo i c)).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
        - 8 * ((bandWtr i (cutHi i c)).card : ℝ)
      ≤ (aLe i c : ℝ) := by
  classical
  have hov : (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ)
      ≤ 8 * ((bandWtr i (cutHi i c)).card : ℝ) :=
    overhang_gen_le_band i (cutHi i c) (pairsLe i c) (gate_cutHi i c hg)
      (pairsLe_subset_prod_cutHi i c)
  have hsub : (startsOf i (pairsLe i c)).card ≤ (pairsLe i c).card :=
    card_startsOf_le i (pairsLe i c)
  have hsplit : ((pairsLe i c).card : ℝ)
      ≤ (aLe i c : ℝ) + (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ) := by
    rw [aLe_eq_card_startsOf]
    have : (pairsLe i c).card
        = (startsOf i (pairsLe i c)).card
          + ((pairsLe i c).card - (startsOf i (pairsLe i c)).card) := by omega
    exact_mod_cast le_of_eq (by exact_mod_cast this)
  have hlo : cutLo i c ≤ wTop i := le_trans (cutLo_le_cutHi i c) hhi
  have hge : ((bandWtr i (cutLo i c)).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ ((pairsLe i c).card : ℝ) := by
    have := card_pairsLe_ge i c hlo
    exact_mod_cast this
  linarith

end NormalNumbers.G4.Sched
