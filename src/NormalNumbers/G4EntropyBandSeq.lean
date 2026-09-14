/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFreq

/-!
# Entropy expedition — the band sequence, and its strictly increasing position map

The band-`i` window family at the good atom is certified (`abs_posAvg_bandLaw_le`), pairwise
disjoint with a full window's margin (`window_gap_same_atom`), and confined to band `i`
(`pos_lt_bandTop`, `bandLo_le_of_mem_bandS`).  Reading the bands in order therefore produces a
**genuinely increasing** sequence of digit positions, block by block, with no repetition: this
module builds that map and proves it strictly monotone.

* `bnth i a` — the `a`-th band-`i` sample time, in increasing order.
* `bpos i a` — the digit position at which that window opens; `bpos_gap` separates consecutive
  windows by a full window length.
* `bL i = |bandS i|·m_i`, `bT i = Σ_{j<i} bL j` — the block lengths and the cutoffs.
* `bandPos j` — the position of the `j`-th digit read; `bandPos_strictMono`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### Enumerating one band -/

lemma card_bandS_pos (i : ℕ) : 0 < (bandS i).card := Finset.card_pos.2 (bandS_nonempty i)

/-- The `a`-th band-`i` sample time, in increasing order (cyclically extended). -/
noncomputable def bnth (i a : ℕ) : ℕ :=
  (bandS i).orderEmbOfFin rfl ⟨a % (bandS i).card, Nat.mod_lt _ (card_bandS_pos i)⟩

lemma bnth_mem (i a : ℕ) : bnth i a ∈ bandS i := by
  rw [bnth]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma bnth_mem_PK (i a : ℕ) : bnth i a ∈ PK i := bandS_subset i (bnth_mem i a)

lemma bnth_lt_bnth {i a b : ℕ} (hab : a < b) (hb : b < (bandS i).card) :
    bnth i a < bnth i b := by
  have ha : a < (bandS i).card := lt_trans hab hb
  rw [bnth, bnth]
  refine (Finset.orderEmbOfFin (bandS i) rfl).strictMono ?_
  refine Fin.mk_lt_mk.2 ?_
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

/-- The digit position at which the `a`-th band-`i` window opens. -/
noncomputable def bpos (i a : ℕ) : ℕ := 2 * kIdx (gridAt i) (bnth i a) (goodAtom i)

/-- **Consecutive windows are a full window apart.** -/
lemma bpos_gap {i a b : ℕ} (hab : a < b) (hb : b < (bandS i).card) :
    bpos i a + kk i ≤ bpos i b :=
  window_gap_same_atom i (goodAtom i) (bnth_mem_PK i a) (bnth_mem_PK i b)
    (bnth_lt_bnth hab hb)

lemma bpos_add_lt_bandTop (i a : ℕ) {p : ℕ} (hp : p < kk i) : bpos i a + p < bandTop i :=
  pos_lt_bandTop i (bnth_mem_PK i a) (goodAtom i) hp

lemma bandLo_le_bpos (i a : ℕ) : bandLo i ≤ bpos i a :=
  bandLo_le_of_mem_bandS i (bnth_mem i a)

/-! ### The block lengths and the cutoffs -/

/-- The number of digits band `i` contributes. -/
noncomputable def bL (i : ℕ) : ℕ := (bandS i).card * kk i

lemma kk_pos' (i : ℕ) : 0 < kk i := by unfold kk; omega

lemma bL_pos (i : ℕ) : 0 < bL i := Nat.mul_pos (card_bandS_pos i) (kk_pos' i)

/-- The cutoff after the first `i` bands. -/
noncomputable def bT : ℕ → ℕ
  | 0 => 0
  | (i + 1) => bT i + bL i

lemma bT_lt_succ (i : ℕ) : bT i < bT (i + 1) := by
  have := bL_pos i
  show bT i < bT i + bL i
  omega

lemma bT_mono : Monotone bT := monotone_nat_of_le_succ fun i => (bT_lt_succ i).le

lemma self_le_bT (i : ℕ) : i ≤ bT i := by
  induction i with
  | zero => simp [bT]
  | succ i ih => have := bT_lt_succ i; omega

/-- The band a read index belongs to. -/
noncomputable def bgrp (j : ℕ) : ℕ := Nat.findGreatest (fun m => bT m ≤ j) j

lemma bgrp_eq {i j : ℕ} (h1 : bT i ≤ j) (h2 : j < bT (i + 1)) : bgrp j = i := by
  classical
  have hij : i ≤ j := le_trans (self_le_bT i) h1
  have hle : i ≤ bgrp j := Nat.le_findGreatest hij h1
  by_contra hne
  have hlt : i < bgrp j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : bT (bgrp j) ≤ j :=
    Nat.findGreatest_spec (P := fun m => bT m ≤ j) hij h1
  have : bT (i + 1) ≤ bT (bgrp j) := bT_mono (by omega)
  omega

lemma bT_bgrp_le (j : ℕ) : bT (bgrp j) ≤ j := by
  classical
  exact Nat.findGreatest_spec (P := fun m => bT m ≤ j) (Nat.zero_le j) (by simp [bT])

lemma lt_bT_bgrp_succ (j : ℕ) : j < bT (bgrp j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : bgrp j + 1 ≤ j := le_trans (self_le_bT (bgrp j + 1)) hcon
  have h2 : bgrp j + 1 ≤ bgrp j := Nat.le_findGreatest h1 hcon
  omega

/-! ### The position map -/

/-- **The position of the `j`-th digit read.**  Bands in order; inside a band, windows in order;
inside a window, the `m_i` consecutive digit positions. -/
noncomputable def bandPos (j : ℕ) : ℕ :=
  bpos (bgrp j) ((j - bT (bgrp j)) / kk (bgrp j)) + (j - bT (bgrp j)) % kk (bgrp j)

lemma bandPos_eq {i j : ℕ} (h1 : bT i ≤ j) (h2 : j < bT (i + 1)) :
    bandPos j = bpos i ((j - bT i) / kk i) + (j - bT i) % kk i := by
  rw [bandPos, bgrp_eq h1 h2]

/-- **The position map is strictly increasing**: a genuine subsequence of `G₄`'s digits. -/
theorem bandPos_strictMono : StrictMono bandPos := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  set i := bgrp j with hi
  have h1 : bT i ≤ j := bT_bgrp_le j
  have h2 : j < bT (i + 1) := lt_bT_bgrp_succ j
  have hbT : bT (i + 1) = bT i + bL i := rfl
  set r : ℕ := j - bT i with hr
  have hrlt : r < bL i := by omega
  have hkk : 0 < kk i := kk_pos' i
  set a : ℕ := r / kk i with ha
  set p : ℕ := r % kk i with hp
  have hpk : p < kk i := Nat.mod_lt _ hkk
  have hra : r = a * kk i + p := (Nat.div_add_mod' r (kk i)).symm
  have hacard : a < (bandS i).card := by
    by_contra hcon
    push_neg at hcon
    have : (bandS i).card * kk i ≤ a * kk i := Nat.mul_le_mul_right _ hcon
    rw [bL] at hrlt
    omega
  have hj : bandPos j = bpos i a + p := bandPos_eq h1 h2
  rcases Nat.lt_or_ge (p + 1) (kk i) with hcase | hcase
  · -- inside the same window
    have hr1 : j + 1 - bT i = r + 1 := by omega
    have hlt1 : j + 1 < bT (i + 1) := by
      rw [hbT, bL]
      have : (a + 1) * kk i ≤ (bandS i).card * kk i := Nat.mul_le_mul_right _ hacard
      have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
      omega
    have hdiv : (r + 1) / kk i = a := by
      rw [hra]
      have : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [this, Nat.mul_add_div hkk, Nat.div_eq_of_lt hcase]
      omega
    have hmod : (r + 1) % kk i = p + 1 := by
      rw [hra]
      have : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hcase]
    have := bandPos_eq (i := i) (j := j + 1) (by omega) hlt1
    rw [this, hr1, hdiv, hmod, hj]
    omega
  · have hpk1 : p + 1 = kk i := by omega
    rcases Nat.lt_or_ge (a + 1) (bandS i).card with hcase2 | hcase2
    · -- next window, same band
      have hr1 : j + 1 - bT i = r + 1 := by omega
      have hreq : r + 1 = (a + 1) * kk i := by
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hlt1 : j + 1 < bT (i + 1) := by
        rw [hbT, bL]
        have : (a + 1) * kk i < (bandS i).card * kk i :=
          Nat.mul_lt_mul_of_lt_of_le hcase2 (le_refl _) hkk
        omega
      have hdiv : (r + 1) / kk i = a + 1 := by
        rw [hreq, Nat.mul_div_cancel _ hkk]
      have hmod : (r + 1) % kk i = 0 := by
        rw [hreq, Nat.mul_mod_left]
      have heq := bandPos_eq (i := i) (j := j + 1) (by omega) hlt1
      rw [heq, hr1, hdiv, hmod, hj]
      have hgap := bpos_gap (i := i) (a := a) (b := a + 1) (by omega) hcase2
      omega
    · -- next band
      have hacard' : a + 1 = (bandS i).card := by omega
      have hreq : r + 1 = bL i := by
        rw [bL, ← hacard']
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hj1 : j + 1 = bT (i + 1) := by rw [hbT]; omega
      have hlt2 : bT (i + 1) ≤ j + 1 := by omega
      have hlt3 : j + 1 < bT (i + 1 + 1) := by
        have := bT_lt_succ (i + 1)
        omega
      have heq := bandPos_eq (i := i + 1) (j := j + 1) hlt2 hlt3
      have hzero : j + 1 - bT (i + 1) = 0 := by omega
      rw [heq, hzero, Nat.zero_div, Nat.zero_mod, hj]
      have hup : bandLo (i + 1) ≤ bpos (i + 1) 0 := bandLo_le_bpos (i + 1) 0
      have hlo : bandLo (i + 1) = bandTop i := rfl
      have hdown : bpos i a + p < bandTop i := bpos_add_lt_bandTop i a hpk
      omega

end NormalNumbers.G4.Sched
