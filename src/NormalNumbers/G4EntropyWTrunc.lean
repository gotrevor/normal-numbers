/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWPrefix

/-!
# The prefix pair set, and its two product flanks

`G4EntropyWSandwich` brackets the sample times a position cutoff keeps; `G4EntropyWPrefix` turns a
read index into a position cutoff.  This module joins them at the level of the **pair** sums that
the band law certifies.

* The multiplicity bridge of `G4EntropyFullSeqW` (`sum_pairsW_eq`, `sum_pairsW_sub_le`,
  `overhangW_le`) is re-proved **generic in the pair collection** `T ⊆ bandWPairs i`.  Nothing in
  it used the fact that `T` was all of `bandWPairs i`; the overhang of any sub-collection is
  bounded by the *same* `badWPairs i`, because a shared window inside `T` is a shared window
  inside `bandWPairs i`.
* `pairsLe i c` — the pairs a position cutoff `c` keeps — has `startsOf i (pairsLe i c) =
  startsLe i c` (the consumed starts) and is sandwiched between the two **product** collections
  `bandWtr i (cutLo i c) ×ˢ univ` and `bandWtr i (cutHi i c) ×ˢ univ`, which are exactly the
  shapes `abs_posAvg_bandWLaw_le` certifies.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The multiplicity bridge, generic in the pair collection -/

open Classical in
/-- The distinct window starts of a collection of `(n, α)` pairs. -/
noncomputable def startsOf (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom)) : Finset ℕ :=
  T.image (fun z => 2 * kIdx (gridAt i) z.1 z.2)

open Classical in
lemma startsOf_bandWPairs (i : ℕ) : startsOf i (bandWPairs i) = winStartsW i := rfl

open Classical in
lemma mem_startsOf (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom)) {q : ℕ} :
    q ∈ startsOf i T ↔ ∃ z ∈ T, 2 * kIdx (gridAt i) z.1 z.2 = q := by
  rw [startsOf, Finset.mem_image]

open Classical in
/-- **The pair sum is the multiplicity-weighted start sum**, for any collection. -/
theorem sum_pairs_eq_gen (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom)) (x : ℝ) (v : List ℕ) :
    ∑ z ∈ T, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ q ∈ startsOf i T,
          (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card * winOccW i x v q := by
  classical
  rw [startsOf]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image (fun z => 2 * kIdx (gridAt i) z.1 z.2))
    (g := fun z => 2 * kIdx (gridAt i) z.1 z.2)
    (fun z hz => Finset.mem_image_of_mem _ hz)
    (fun z => winOccW i x v (2 * kIdx (gridAt i) z.1 z.2))
  rw [← hfib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcongr : ∀ z ∈ T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q),
      winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) = winOccW i x v q := by
    intro z hz
    rw [(Finset.mem_filter.1 hz).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

open Classical in
theorem card_startsOf_le (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom)) :
    (startsOf i T).card ≤ T.card := Finset.card_image_le

open Classical in
/-- **The pair sum exceeds the start sum by at most the overhang**, for any collection. -/
theorem sum_pairs_sub_le_gen (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom)) (x : ℝ) (v : List ℕ) :
    ∑ q ∈ startsOf i T, winOccW i x v q
        ≤ ∑ z ∈ T, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) ∧
      ∑ z ∈ T, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
        ≤ ∑ q ∈ startsOf i T, winOccW i x v q
          + (T.card - (startsOf i T).card) * (kk i - v.length + 1) := by
  classical
  rw [sum_pairs_eq_gen i T x v]
  have hfib : ∀ q ∈ startsOf i T,
      1 ≤ (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := (mem_startsOf i T).1 hq
    exact Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hzq⟩⟩
  have hsumfib : ∑ q ∈ startsOf i T,
      (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card = T.card := by
    rw [startsOf]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun z hz => Finset.mem_image_of_mem _ hz)).symm
  constructor
  · refine Finset.sum_le_sum fun q hq => ?_
    have hc := hfib q hq
    exact Nat.le_mul_of_pos_left _ (by omega)
  · have hterm : ∀ q ∈ startsOf i T,
        (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card * winOccW i x v q
          ≤ winOccW i x v q
            + ((T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
              * (kk i - v.length + 1) := by
      intro q hq
      have h1 := hfib q hq
      have h2 := winOccW_le i x v q
      set c := (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card with hc
      have hc1 : c - 1 + 1 = c := by omega
      calc c * winOccW i x v q = ((c - 1) + 1) * winOccW i x v q := by rw [hc1]
        _ = winOccW i x v q + (c - 1) * winOccW i x v q := by ring
        _ ≤ winOccW i x v q + (c - 1) * (kk i - v.length + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    have hle : ∑ _q ∈ startsOf i T, 1 ≤ ∑ q ∈ startsOf i T,
        (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card :=
      Finset.sum_le_sum hfib
    have hcards : ∑ _q ∈ startsOf i T, (1 : ℕ) = (startsOf i T).card := by simp
    have hsplit : ∑ q ∈ startsOf i T,
        ((T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
        = (∑ q ∈ startsOf i T, (T.filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card)
          - ∑ _q ∈ startsOf i T, 1 := by
      rw [← Finset.sum_tsub_distrib]
      exact fun q hq => hfib q hq
    rw [hsplit, hsumfib, hcards]

open Classical in
/-- **The overhang of any sub-collection is bounded by the same shared pairs.** -/
theorem overhang_gen_le (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom))
    (hT : T ⊆ bandWPairs i) : T.card - (startsOf i T).card ≤ (badWPairs i).card := by
  classical
  have hinj : (T \ (badWPairs i)).card ≤ (startsOf i T).card := by
    refine Finset.card_le_card_of_injOn (fun z => 2 * kIdx (gridAt i) z.1 z.2) ?_ ?_
    · intro z hz
      simp only [Finset.coe_sdiff, Set.mem_diff] at hz
      exact (mem_startsOf i T).2 ⟨z, hz.1, rfl⟩
    · intro z hz z' hz' heq
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hz hz'
      simp only at heq
      have hzB : z ∈ bandWPairs i := hT hz.1
      have hzB' : z' ∈ bandWPairs i := hT hz'.1
      by_cases hat : z.2 = z'.2
      · have hz1 : z.1 ∈ bandW i := (Finset.mem_product.1 hzB).1
        have hz1' : z'.1 ∈ bandW i := (Finset.mem_product.1 hzB').1
        have hkk : 0 < kk i := by unfold kk; omega
        have heq' : 2 * kIdx (gridAt i) z.1 z.2 = 2 * kIdx (gridAt i) z'.1 z.2 := by
          rw [heq, ← hat]
        have hn : z.1 = z'.1 := by
          by_contra hne
          rcases Nat.lt_or_ge z.1 z'.1 with hlt | hge
          · have hg := window_gap_same_atom_at i (wTop i) z.2 (bandW_subset i hz1)
              (bandW_subset i hz1') hlt
            omega
          · have hgt : z'.1 < z.1 := by omega
            have hg := window_gap_same_atom_at i (wTop i) z.2 (bandW_subset i hz1')
              (bandW_subset i hz1) hgt
            omega
        exact Prod.ext hn hat
      · exfalso
        refine hz.2 ?_
        refine Finset.mem_filter.2 ⟨hzB, z'.2, fun h => hat h.symm, ?_⟩
        have hkeq : kIdx (gridAt i) z.1 z.2 = kIdx (gridAt i) z'.1 z'.2 := by omega
        rw [hkeq]
        exact activeIdx_kIdx (gridAt i) (bandW_subset i (Finset.mem_product.1 hzB').1) z'.2
  have hsub : T.card ≤ (T \ (badWPairs i)).card + (badWPairs i).card := by
    have h1 : T.card ≤ (T \ (badWPairs i)).card + (T ∩ (badWPairs i)).card := by
      have := Finset.card_sdiff_add_card_inter T (badWPairs i)
      omega
    have h2 : (T ∩ (badWPairs i)).card ≤ (badWPairs i).card :=
      Finset.card_le_card (Finset.inter_subset_right)
    omega
  omega

open Classical in
/-- **The overhang of any sub-collection, quantitatively.** -/
theorem overhang_gen_le_real (i : ℕ) (T : Finset (ℕ × (gridAt i).Atom))
    (hT : T ⊆ bandWPairs i) :
    ((T.card - (startsOf i T).card : ℕ) : ℝ)
      ≤ 2 * ((PKtr i (wTop i)).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
  refine le_trans ?_ (card_badWPairs_le_real i)
  exact_mod_cast overhang_gen_le i T hT

/-! ### The pairs a position cutoff keeps -/

open Classical in
/-- The band-`i` pairs whose window start is at most `c`. -/
noncomputable def pairsLe (i c : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 ≤ c)

open Classical in
lemma pairsLe_subset_bandWPairs (i c : ℕ) : pairsLe i c ⊆ bandWPairs i :=
  Finset.filter_subset _ _

open Classical in
/-- **The pairs a cutoff keeps produce exactly the starts it consumes.** -/
theorem startsOf_pairsLe (i c : ℕ) : startsOf i (pairsLe i c) = startsLe i c := by
  classical
  ext q
  rw [mem_startsOf, startsLe, Finset.mem_filter]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [pairsLe, Finset.mem_filter] at hz
    exact ⟨(mem_winStartsW i).2 ⟨z.1, (Finset.mem_product.1 hz.1).1, z.2, rfl⟩, hz.2⟩
  · rintro ⟨hq, hqc⟩
    obtain ⟨n, hn, α, rfl⟩ := (mem_winStartsW i).1 hq
    exact ⟨(n, α), by
      rw [pairsLe, Finset.mem_filter]
      exact ⟨Finset.mem_product.2 ⟨hn, Finset.mem_univ _⟩, hqc⟩, rfl⟩

open Classical in
/-- **The lower flank, as a product collection.** -/
theorem prod_cutLo_subset_pairsLe (i c : ℕ) (hle : cutLo i c ≤ wTop i) :
    (bandWtr i (cutLo i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom) ⊆ pairsLe i c := by
  intro z hz
  rw [Finset.mem_product] at hz
  have hnb : z.1 ∈ bandW i := bandWtr_cutLo_subset_bandW i c hle hz.1
  have hlt : z.1 < cutLo i c := mem_bandWtr_lt hz.1
  rw [pairsLe, Finset.mem_filter]
  exact ⟨Finset.mem_product.2 ⟨hnb, Finset.mem_univ _⟩,
    two_kIdx_le_of_lt_cutLo i c hlt z.2⟩

open Classical in
/-- **The upper flank, as a product collection.** -/
theorem pairsLe_subset_prod_cutHi (i c : ℕ) :
    pairsLe i c ⊆ (bandWtr i (cutHi i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom) := by
  intro z hz
  rw [pairsLe, Finset.mem_filter] at hz
  have hnb : z.1 ∈ bandW i := (Finset.mem_product.1 hz.1).1
  exact Finset.mem_product.2 ⟨mem_bandWtr_cutHi i c hnb z.2 hz.2, Finset.mem_univ _⟩

end NormalNumbers.G4.Sched
