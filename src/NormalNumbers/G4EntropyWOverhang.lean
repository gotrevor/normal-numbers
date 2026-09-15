/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWCount

/-!
# The multiplicity overhang at a **truncated** scale

`overhang_gen_le` bounds the overhang of any sub-collection of `bandWPairs i` by the *whole*
band's shared pairs `badWPairs i`.  That is useless for a mid-band prefix: a prefix carries only
`|bandWtr i (cutLo i c)|` sample times, which can be an arbitrarily small fraction of the band,
while `|badWPairs i|` is proportional to the whole band.

The fix is that a collision inside a truncated collection is a collision *between truncated sample
times*: if `T ⊆ bandWtr i X' ×ˢ univ`, the overhang of `T` is bounded by `badPairsAt i X'`, the
shared pairs of the truncated sample, and `card_multi_atom_le_real_at` is already `X'`-generic.

Two ingredients that the tile-top proofs got for free:

* `card_Atom_sq_le_PKtr` — `|Atom|² ≤ |PKtr i X'|` at every gated scale (`|Atom| ≤ 2^{K³+K}`
  while the gate forces `X' ≥ 16·Xlo = 16·2^{50·2^m}` and `P₀ ≤ 2^{2·2^m}`);
* `overhang_flank_le_real` — the prefix overhang against the *upper flank's* own count.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### `|Atom|² ≤ |P_K(X')|` at every gated scale -/

/-- **The atom count is dwarfed by the truncated sample**, at every scale above the gate.
`|Atom|² ≤ 2^{2K³+2K}` while `|PKtr i X'| ≥ X'/(2P₀) ≥ 16·Xlo/(2P₀) ≥ 8·2^{48·2^m}`. -/
theorem card_Atom_sq_le_PKtr (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ ((PKtr i X').card : ℝ) := by
  have hK100 : 100 ≤ KK i := by have := KK_ge i; omega
  have hP₀pos : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by
    have := (gridAt i).P₀_pos; exact_mod_cast this
  -- the sample is at least `X'/(2P₀)`
  have hhalf : (X' : ℝ) / (2 * ((gridAt i).P₀ : ℝ)) ≤ ((PKtr i X').card : ℝ) :=
    card_apSample_ge_half X' (gridAt i).P₀ (gridAt i).b₀ (gridAt i).P₀_pos
      (gridAt i).b₀_lt_P₀ (two_P₀_le_of_wgate hg)
  -- the gate forces `X' ≥ 16·Xlo`
  have hXlo : (16 : ℝ) * (Xlo (KK i) : ℝ) ≤ (X' : ℝ) := by
    have h1 : 4 * Xlo (KK i) ≤ wFloor i := Xlo_le_wFloor' i
    have h2 : 16 * Xlo (KK i) ≤ X' := by omega
    exact_mod_cast h2
  have hXloC : ((Xlo (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := Xlo_cast (KK i)
  have hP : ((gridAt i).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := P₀_le_two_pow hK100
  -- the atom count
  have hA : (Fintype.card (gridAt i).Atom : ℝ) ≤ (2 : ℝ) ^ (KK i ^ 3 + KK i) := by
    have h := card_Atom_le_two_pow i
    have : ((Fintype.card (gridAt i).Atom : ℕ) : ℝ) ≤ ((2 ^ (KK i ^ 3 + KK i) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    exact this
  have hAnn : (0 : ℝ) ≤ (Fintype.card (gridAt i).Atom : ℝ) := Nat.cast_nonneg _
  have hAsq : (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) := by
    calc (Fintype.card (gridAt i).Atom : ℝ) ^ 2
        ≤ ((2 : ℝ) ^ (KK i ^ 3 + KK i)) ^ 2 := pow_le_pow_left₀ hAnn hA 2
      _ = (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) := by rw [← pow_mul]; ring_nf
  -- the exponent comparison `2(K³+K) ≤ 48·2^m`
  have hexp : 2 * (KK i ^ 3 + KK i) ≤ 48 * 2 ^ m (KK i) := by
    have hcube : KK i ^ 3 ≤ m₁ (KK i) := m₁_ge_cube (by omega)
    have hm : m₁ (KK i) ≤ m (KK i) := m₁_le_m (KK i)
    have hpow : m (KK i) ≤ 2 ^ m (KK i) := Nat.le_of_lt Nat.lt_two_pow_self
    have hKc : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hstep : (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) ≤ (2 : ℝ) ^ (48 * 2 ^ m (KK i)) :=
    pow_le_pow_right₀ (by norm_num) hexp
  -- assemble
  refine le_trans hAsq (le_trans hstep ?_)
  refine le_trans ?_ hhalf
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * ((gridAt i).P₀ : ℝ))]
  have hlow : (2 : ℝ) ^ (48 * 2 ^ m (KK i)) * (2 * ((gridAt i).P₀ : ℝ))
      ≤ (2 : ℝ) ^ (48 * 2 ^ m (KK i)) * (2 * (2 : ℝ) ^ (2 * 2 ^ m (KK i))) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (48 * 2 ^ m (KK i)) := by positivity
    nlinarith [hP, hpos]
  refine le_trans hlow ?_
  have hcomb : (2 : ℝ) ^ (48 * 2 ^ m (KK i)) * (2 * (2 : ℝ) ^ (2 * 2 ^ m (KK i)))
      = 2 * (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := by
    rw [show (50 : ℕ) * 2 ^ m (KK i) = 48 * 2 ^ m (KK i) + 2 * 2 ^ m (KK i) by ring, pow_add]
    ring
  rw [hcomb, ← hXloC]
  linarith [hXlo]

/-! ### The shared pairs of a truncated sample -/

open Classical in
/-- The truncated band's pairs whose window is shared with another atom. -/
noncomputable def badPairsAt (i X' : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  ((bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom)).filter
    (fun z => ∃ β, β ≠ z.2 ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) z.1 z.2))

open Classical in
/-- **The overhang of a truncated sub-collection is bounded by the truncated shared pairs.**
Off `badPairsAt i X'` the window-start map is injective on `bandWtr i X' ×ˢ univ`. -/
theorem overhang_gen_le_at (i X' : ℕ) (T : Finset (ℕ × (gridAt i).Atom))
    (hT : T ⊆ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom)) :
    T.card - (startsOf i T).card ≤ (badPairsAt i X').card := by
  classical
  have hinj : (T \ (badPairsAt i X')).card ≤ (startsOf i T).card := by
    refine Finset.card_le_card_of_injOn (fun z => 2 * kIdx (gridAt i) z.1 z.2) ?_ ?_
    · intro z hz
      simp only [Finset.coe_sdiff, Set.mem_diff] at hz
      exact (mem_startsOf i T).2 ⟨z, hz.1, rfl⟩
    · intro z hz z' hz' heq
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hz hz'
      simp only at heq
      have hzB : z ∈ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom) := hT hz.1
      have hzB' : z' ∈ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom) := hT hz'.1
      have hz1 : z.1 ∈ bandWtr i X' := (Finset.mem_product.1 hzB).1
      have hz1' : z'.1 ∈ bandWtr i X' := (Finset.mem_product.1 hzB').1
      by_cases hat : z.2 = z'.2
      · have hkk : 0 < kk i := by unfold kk; omega
        have heq' : 2 * kIdx (gridAt i) z.1 z.2 = 2 * kIdx (gridAt i) z'.1 z.2 := by
          rw [heq, ← hat]
        have hn : z.1 = z'.1 := by
          by_contra hne
          rcases Nat.lt_or_ge z.1 z'.1 with hlt | hge
          · have hg := window_gap_same_atom_at i X' z.2 (bandWtr_subset i X' hz1)
              (bandWtr_subset i X' hz1') hlt
            omega
          · have hgt : z'.1 < z.1 := by omega
            have hg := window_gap_same_atom_at i X' z.2 (bandWtr_subset i X' hz1')
              (bandWtr_subset i X' hz1) hgt
            omega
        exact Prod.ext hn hat
      · exfalso
        refine hz.2 ?_
        refine Finset.mem_filter.2 ⟨hzB, z'.2, fun h => hat h.symm, ?_⟩
        have hkeq : kIdx (gridAt i) z.1 z.2 = kIdx (gridAt i) z'.1 z'.2 := by omega
        rw [hkeq]
        exact activeIdx_kIdx (gridAt i) (bandWtr_subset i X' hz1') z'.2
  have hsub : T.card ≤ (T \ (badPairsAt i X')).card + (badPairsAt i X').card := by
    have h1 : T.card ≤ (T \ (badPairsAt i X')).card + (T ∩ (badPairsAt i X')).card := by
      have := Finset.card_sdiff_add_card_inter T (badPairsAt i X')
      omega
    have h2 : (T ∩ (badPairsAt i X')).card ≤ (badPairsAt i X').card :=
      Finset.card_le_card (Finset.inter_subset_right)
    omega
  omega

open Classical in
/-- **The truncated shared pairs are few**: at most `2|P_K(X')| + 2|Atom|²`.  Same collision
chain as `card_badWPairs_le_real`, run at the truncated scale (`card_multi_atom_le_real_at` is
already `X'`-generic). -/
theorem card_badPairsAt_le_real (i X' : ℕ) (h2P : 2 * (gridAt i).P₀ ≤ X') :
    ((badPairsAt i X').card : ℝ)
      ≤ 2 * ((PKtr i X').card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
  classical
  have hsplit : (badPairsAt i X').card
      ≤ ∑ α : (gridAt i).Atom,
          ((PKtr i X').filter (fun n =>
            ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card := by
    have hsub : badPairsAt i X' ⊆ (Finset.univ : Finset (gridAt i).Atom).biUnion
        (fun α => ((PKtr i X').filter (fun n =>
          ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).image
            (fun n => (n, α))) := by
      intro z hz
      rw [badPairsAt, Finset.mem_filter] at hz
      obtain ⟨hz1, hz2⟩ := hz
      refine Finset.mem_biUnion.2 ⟨z.2, Finset.mem_univ _, ?_⟩
      refine Finset.mem_image.2 ⟨z.1, ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨bandWtr_subset i X' (Finset.mem_product.1 hz1).1, hz2⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    exact Finset.sum_le_sum fun α _ => Finset.card_image_le
  have hterm : ∀ α : (gridAt i).Atom,
      (((PKtr i X').filter (fun n =>
        ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℝ)
        ≤ 2 * ((PKtr i X').card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
          + 2 * (Fintype.card (gridAt i).Atom : ℝ) :=
    fun α => card_multi_atom_le_real_at i X' h2P α
  have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hsum : ((badPairsAt i X').card : ℝ)
      ≤ ∑ _α : (gridAt i).Atom, (2 * ((PKtr i X').card : ℝ)
          / (Fintype.card (gridAt i).Atom : ℝ)
          + 2 * (Fintype.card (gridAt i).Atom : ℝ)) := by
    have hsplitR : ((badPairsAt i X').card : ℝ)
        ≤ ∑ α : (gridAt i).Atom,
            ((((PKtr i X').filter (fun n =>
              ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℕ) : ℝ) := by
      exact_mod_cast hsplit
    exact le_trans hsplitR (Finset.sum_le_sum fun α _ => hterm α)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hexp : (Fintype.card (gridAt i).Atom : ℝ)
      * (2 * ((PKtr i X').card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
        + 2 * (Fintype.card (gridAt i).Atom : ℝ))
      = 2 * ((PKtr i X').card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
    field_simp
  rw [hexp] at hsum
  exact hsum

open Classical in
/-- **The truncated overhang against the truncated band**: `ov ≤ 8·|bandWtr i X'|`. -/
theorem overhang_gen_le_band (i X' : ℕ) (T : Finset (ℕ × (gridAt i).Atom))
    (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X')
    (hT : T ⊆ (bandWtr i X') ×ˢ (Finset.univ : Finset (gridAt i).Atom)) :
    ((T.card - (startsOf i T).card : ℕ) : ℝ) ≤ 8 * ((bandWtr i X').card : ℝ) := by
  have hov : ((T.card - (startsOf i T).card : ℕ) : ℝ) ≤ ((badPairsAt i X').card : ℝ) := by
    exact_mod_cast overhang_gen_le_at i X' T hT
  have hbad := card_badPairsAt_le_real i X' (two_P₀_le_of_wgate hg)
  have hsq := card_Atom_sq_le_PKtr i X' hg
  have hband := card_bandWtr_ge i X' hg
  linarith

end NormalNumbers.G4.Sched
