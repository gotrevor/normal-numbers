/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWHead

/-!
# The flanks, capped at the band's own tile top

`abs_prefix_ratio_sub_le` carries the hypothesis `cutHi i c ≤ wTop i`, and that hypothesis
**fails for the top `O(1/K)` of every band**: a start is `c = 2·kIdx(n,α) ≤ 2n/d_α`, so
`cutHi i c ≈ (K+1)/(2K)·d_ref·c ≈ wTop·(1+2/K) > wTop i`.  Above `wTop i = Xlo (KK (i+1))` the
certificate says nothing, so the flank must be **capped**:

* `cutBot i c := min (cutLo i c) (wTop i)`, `cutTop i c := min (cutHi i c) (wTop i)`.

Both inclusions survive the cap, because `pairsLe i c ⊆ bandWPairs i` already forces every pair's
sample time below `wTop i`:

* `prod_cutBot_subset_pairsLe` — `bandWtr i (cutBot i c) ⊆ bandWtr i (cutLo i c)`, so the lower
  inclusion is the old one composed with monotonicity (and the `hle` hypothesis is no longer
  needed: the cap supplies it);
* `pairsLe_subset_prod_cutTop` — a pair of `pairsLe i c` has `z.1 ∈ bandW i` (below `wTop i`) and
  `z.1 < cutHi i c`, hence `z.1 < min` of the two.

`card_flank_ratio` survives by a case split on `cutLo i c ≤ wTop i`: below the cap it is the old
statement, above it both flanks are `bandWtr i (wTop i)` and the ratio is `1`.

The endpoint `abs_prefix_ratio_sub_le_cap` is `abs_prefix_ratio_sub_le` **with no upper
hypothesis at all** — the estimate now holds at *every* cutoff above the gate.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The capped flanks -/

/-- The lower flank, capped at the tile top. -/
noncomputable def cutBot (i c : ℕ) : ℕ := min (cutLo i c) (wTop i)

/-- The upper flank, capped at the tile top. -/
noncomputable def cutTop (i c : ℕ) : ℕ := min (cutHi i c) (wTop i)

lemma cutBot_le_cutTop (i c : ℕ) : cutBot i c ≤ cutTop i c :=
  min_le_min (cutLo_le_cutHi i c) le_rfl

lemma cutBot_le_wTop (i c : ℕ) : cutBot i c ≤ wTop i := min_le_right _ _
lemma cutTop_le_wTop (i c : ℕ) : cutTop i c ≤ wTop i := min_le_right _ _
lemma cutBot_le_cutLo (i c : ℕ) : cutBot i c ≤ cutLo i c := min_le_left _ _
lemma cutTop_le_cutHi (i c : ℕ) : cutTop i c ≤ cutHi i c := min_le_left _ _

lemma gate_cutBot (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutBot i c :=
  le_min (gate_cutLo i c hg) (wgate_wTop i)

lemma gate_cutTop (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutTop i c :=
  le_min (gate_cutHi i c hg) (wgate_wTop i)

open Classical in
lemma mem_bandWtr_min {i X Y n : ℕ} (hX : n ∈ bandWtr i X) (hY : n ∈ bandWtr i Y) :
    n ∈ bandWtr i (min X Y) := by
  rw [bandWtr, Finset.mem_filter, PKtr, apSample, Finset.mem_filter, Finset.mem_range] at hX hY ⊢
  exact ⟨⟨lt_min hX.1.1 hY.1.1, hX.1.2⟩, hX.2⟩

/-! ### The two inclusions, capped -/

open Classical in
theorem prod_cutBot_subset_pairsLe (i c : ℕ) :
    (bandWtr i (cutBot i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom) ⊆ pairsLe i c := by
  intro z hz
  rw [Finset.mem_product] at hz
  have hsub : bandWtr i (cutBot i c) ⊆ bandW i := by
    rw [bandW]
    exact bandWtr_mono i (cutBot_le_wTop i c)
  have hnb : z.1 ∈ bandW i := hsub hz.1
  have hlt : z.1 < cutLo i c :=
    lt_of_lt_of_le (mem_bandWtr_lt hz.1) (cutBot_le_cutLo i c)
  rw [pairsLe, Finset.mem_filter]
  exact ⟨Finset.mem_product.2 ⟨hnb, Finset.mem_univ _⟩,
    two_kIdx_le_of_lt_cutLo i c hlt z.2⟩

open Classical in
theorem pairsLe_subset_prod_cutTop (i c : ℕ) :
    pairsLe i c ⊆ (bandWtr i (cutTop i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom) := by
  intro z hz
  have hz' := hz
  rw [pairsLe, Finset.mem_filter] at hz'
  have hnb : z.1 ∈ bandW i := (Finset.mem_product.1 hz'.1).1
  have h1 : z.1 ∈ bandWtr i (cutHi i c) := mem_bandWtr_cutHi i c hnb z.2 hz'.2
  have h2 : z.1 ∈ bandWtr i (wTop i) := by rwa [← bandW]
  exact Finset.mem_product.2 ⟨mem_bandWtr_min h1 h2, Finset.mem_univ _⟩

/-! ### The flank ratio, capped -/

open Classical in
theorem card_flank_ratio_cap (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    (KK i : ℝ) * ((bandWtr i (cutTop i c)).card : ℝ)
      ≤ ((KK i : ℝ) + 16) * ((bandWtr i (cutBot i c)).card : ℝ) := by
  rcases le_or_gt (cutLo i c) (wTop i) with hle | hgt
  · have hbot : cutBot i c = cutLo i c := min_eq_left hle
    have hmono : ((bandWtr i (cutTop i c)).card : ℝ) ≤ ((bandWtr i (cutHi i c)).card : ℝ) :=
      card_bandWtr_mono i (cutTop_le_cutHi i c)
    have hK : (0 : ℝ) ≤ (KK i : ℝ) := Nat.cast_nonneg _
    have h := card_flank_ratio i c hg
    rw [hbot]
    nlinarith [h, hmono, hK]
  · have hbot : cutBot i c = wTop i := min_eq_right (le_of_lt hgt)
    have htop : cutTop i c = wTop i :=
      min_eq_right (le_trans (le_of_lt hgt) (cutLo_le_cutHi i c))
    rw [hbot, htop]
    have hnn : (0 : ℝ) ≤ ((bandWtr i (wTop i)).card : ℝ) := Nat.cast_nonneg _
    nlinarith [hnn]

/-! ### The consumed-window count, capped -/

open Classical in
theorem aLe_ge_real_cap (i c : ℕ) (hg : 8 * wFloor i ≤ cutLo i c) :
    ((bandWtr i (cutBot i c)).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
        - 8 * ((bandWtr i (cutTop i c)).card : ℝ)
      ≤ (aLe i c : ℝ) := by
  classical
  have hov : (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ)
      ≤ 8 * ((bandWtr i (cutTop i c)).card : ℝ) :=
    overhang_gen_le_band i (cutTop i c) (pairsLe i c) (gate_cutTop i c hg)
      (pairsLe_subset_prod_cutTop i c)
  have hsub : (startsOf i (pairsLe i c)).card ≤ (pairsLe i c).card :=
    card_startsOf_le i (pairsLe i c)
  have hsplit : ((pairsLe i c).card : ℝ)
      ≤ (aLe i c : ℝ) + (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ) := by
    rw [aLe_eq_card_startsOf]
    have : (pairsLe i c).card
        = (startsOf i (pairsLe i c)).card
          + ((pairsLe i c).card - (startsOf i (pairsLe i c)).card) := by omega
    exact_mod_cast le_of_eq (by exact_mod_cast this)
  have hge : ((bandWtr i (cutBot i c)).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ ((pairsLe i c).card : ℝ) := by
    have h : (bandWtr i (cutBot i c)).card * Fintype.card (gridAt i).Atom
        ≤ (pairsLe i c).card := by
      rw [← card_prod_bandWtr]
      exact Finset.card_le_card (prod_cutBot_subset_pairsLe i c)
    exact_mod_cast h
  linarith

open Classical in
theorem aLe_le_real_cap (i c : ℕ) :
    (aLe i c : ℝ)
      ≤ ((bandWtr i (cutTop i c)).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
  have h1 : aLe i c ≤ (pairsLe i c).card := by
    rw [aLe_eq_card_startsOf]; exact card_startsOf_le i (pairsLe i c)
  have h2 : (pairsLe i c).card
      ≤ (bandWtr i (cutTop i c)).card * Fintype.card (gridAt i).Atom := by
    rw [← card_prod_bandWtr]
    exact Finset.card_le_card (pairsLe_subset_prod_cutTop i c)
  have : aLe i c ≤ (bandWtr i (cutTop i c)).card * Fintype.card (gridAt i).Atom :=
    le_trans h1 h2
  exact_mod_cast this

/-! ### MID-BAND PREFIX CONTROL, with no upper hypothesis -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- **`abs_prefix_ratio_sub_le`, uncapped in `c`.**  At *every* position cutoff above the gate —
including the top `O(1/K)` of the band, where `cutHi i c` runs past the tile top — the prefix
read's word frequency is within `ε_i + 128/K_i` of `2^{−|v|}`. -/
theorem abs_prefix_ratio_sub_le_cap (i c : ℕ) (v : List ℕ)
    (hg : 8 * wFloor i ≤ cutLo i c)
    (hlen : 0 < v.length) (hℓm : 2 * v.length ≤ kk i)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    |(fullGoodWPre i (aLe i c) (primeLambertAtBase 4) v : ℝ)
          / ((aLe i c : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
        - 1 / (2 : ℝ) ^ v.length|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i))
          + 128 / (KK i : ℝ) := by
  classical
  set x : ℝ := primeLambertAtBase 4 with hx
  set L : ℝ := ((bandWtr i (cutBot i c)).card : ℝ) with hLdef
  set H : ℝ := ((bandWtr i (cutTop i c)).card : ℝ) with hHdef
  set Q : ℝ := (Fintype.card (gridAt i).Atom : ℝ) with hQdef
  set F : ℝ := ((kk i - v.length + 1 : ℕ) : ℝ) with hFdef
  set A : ℝ := (aLe i c : ℝ) with hAdef
  set S : ℝ := (fullGoodWPre i (aLe i c) x v : ℝ) with hSdef
  set r : ℝ := 1 / (2 : ℝ) ^ v.length with hrdef
  set ε : ℝ := 2 * Real.sqrt (808 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i)) with hεdef
  have hgLo : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutBot i c := gate_cutBot i c hg
  have hgHi : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ cutTop i c := gate_cutTop i c hg
  have hhiX : cutTop i c ≤ Xlo (KK (i + 1)) := by rw [← wTop_eq i]; exact cutTop_le_wTop i c
  have hloX : cutBot i c ≤ Xlo (KK (i + 1)) := by rw [← wTop_eq i]; exact cutBot_le_wTop i c
  have hK : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
  have hQK : (KK i : ℝ) ≤ Q := by
    have := KK_le_card_Atom i
    rw [hQdef]; exact_mod_cast this
  have hL : (1 : ℝ) ≤ L := by
    have := Finset.card_pos.2 (bandWtr_nonempty hgLo)
    rw [hLdef]; exact_mod_cast this
  have hLH : L ≤ H := card_bandWtr_mono i (cutBot_le_cutTop i c)
  have hF : (1 : ℝ) ≤ F := by
    have : 1 ≤ kk i - v.length + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [hFdef]; exact_mod_cast this
  have hflank : (KK i : ℝ) * H ≤ ((KK i : ℝ) + 16) * L := card_flank_ratio_cap i c hg
  have hA1 : L * Q - 8 * H ≤ A := aLe_ge_real_cap i c hg
  have hA2 : A ≤ H * Q := aLe_le_real_cap i c
  have hr0 : (0 : ℝ) < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 / 2 := by
    rw [hrdef]
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ v.length := pow_le_pow_right₀ (by norm_num) hlen
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    simpa using h2
  have hε : (0 : ℝ) ≤ ε := by
    rw [hεdef]; exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; exact Nat.cast_nonneg _
  have hSAF : S ≤ A * F := by
    have h := fullGoodWPre_le i (aLe i c) x v
    have : ((fullGoodWPre i (aLe i c) x v : ℕ) : ℝ)
        ≤ ((aLe i c * (kk i - v.length + 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [hSdef, hAdef, hFdef]
    push_cast at this ⊢
    exact this
  have hbridge := sum_pairs_sub_le_gen i (pairsLe i c) x v
  have hstart : (fullGoodWPre i (aLe i c) x v : ℕ)
      = ∑ q ∈ startsOf i (pairsLe i c), winOccW i x v q := fullGoodWPre_eq_startsOf i c x v
  have hov : (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ) ≤ 8 * H :=
    overhang_gen_le_band i (cutTop i c) (pairsLe i c) hgHi (pairsLe_subset_prod_cutTop i c)
  have hsand1 : ∑ z ∈ (bandWtr i (cutBot i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
        winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      ≤ ∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) :=
    Finset.sum_le_sum_of_subset (prod_cutBot_subset_pairsLe i c)
  have hsand2 : ∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      ≤ ∑ z ∈ (bandWtr i (cutTop i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
          winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) :=
    Finset.sum_le_sum_of_subset (pairsLe_subset_prod_cutTop i c)
  have hcertHi := abs_flank_sum_sub_le i (cutTop i c) v hgHi hhiX hlen hℓm hv
  have hcertLo := abs_flank_sum_sub_le i (cutBot i c) v hgLo hloX hlen hℓm hv
  rw [abs_le] at hcertHi hcertLo
  have hS1 : S ≤ (r + ε) * (H * Q * F) := by
    have h1 : S ≤ ((∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ) := by
      rw [hSdef, hstart]
      exact_mod_cast hbridge.1
    have h2 : ((∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
        ≤ ((∑ z ∈ (bandWtr i (cutTop i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
              winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ) := by
      exact_mod_cast hsand2
    have h3 := hcertHi.2
    rw [← hx, ← hHdef, ← hQdef, ← hFdef, ← hrdef, ← hεdef] at h3
    linarith
  have hS2 : (r - ε) * (L * Q * F) - 8 * (H * F) ≤ S := by
    have h1 : ((∑ z ∈ (bandWtr i (cutBot i c)) ×ˢ (Finset.univ : Finset (gridAt i).Atom),
            winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
        ≤ ((∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ) := by
      exact_mod_cast hsand1
    have h2 : ((∑ z ∈ pairsLe i c, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
        ≤ S + (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ) * F := by
      have := hbridge.2
      rw [hSdef, hstart, hFdef]
      exact_mod_cast this
    have h3 := hcertLo.1
    rw [← hx, ← hLdef, ← hQdef, ← hFdef, ← hrdef, ← hεdef] at h3
    have hFnn : (0:ℝ) ≤ F := by linarith
    have h4 : (((pairsLe i c).card - (startsOf i (pairsLe i c)).card : ℕ) : ℝ) * F
        ≤ 8 * H * F := mul_le_mul_of_nonneg_right hov hFnn
    linarith
  exact mid_ratio_arith hK hQK hL hLH hF hflank hA1 hA2 hS1 hS2 hS0 hSAF hr0 hr1 hε

end NormalNumbers.G4.Sched
