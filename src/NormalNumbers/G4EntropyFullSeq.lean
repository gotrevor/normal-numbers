/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFull
import NormalNumbers.G4EntropyBandSeq

/-!
# Entropy expedition — the schedule-only band read

`G4EntropyBandSeq`'s read picks one *good atom* per scale, which depends on `G₄`'s entropy data.
With `windows_eq_or_disjoint` (`Q ∣ P₀`) the read can take the **whole** sample's windows in a
band, and everything becomes schedule-only.

* `winStarts i` — the band-`i` window starts, as a `Finset`: `{2·kIdx(n,α) : n ∈ bandT i, α}`.
  A *set*, so coinciding windows are counted once; `windows_eq_or_disjoint` makes distinct
  elements at least `m_i` apart.
* `fnth i a` — the `a`-th of them, in increasing order.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The band's window starts -/

open Classical in
/-- The distinct window starts of band `i`. -/
noncomputable def winStarts (i : ℕ) : Finset ℕ :=
  ((bandT i) ×ˢ (Finset.univ : Finset (gridAt i).Atom)).image
    (fun z => 2 * kIdx (gridAt i) z.1 z.2)

open Classical in
lemma mem_winStarts (i : ℕ) {q : ℕ} :
    q ∈ winStarts i ↔ ∃ n ∈ bandT i, ∃ α : (gridAt i).Atom, q = 2 * kIdx (gridAt i) n α := by
  classical
  rw [winStarts, Finset.mem_image]
  constructor
  · rintro ⟨⟨n, α⟩, hz, rfl⟩
    exact ⟨n, (Finset.mem_product.1 hz).1, α, rfl⟩
  · rintro ⟨n, hn, α, rfl⟩
    exact ⟨(n, α), Finset.mem_product.2 ⟨hn, Finset.mem_univ _⟩, rfl⟩

lemma winStarts_nonempty (i : ℕ) : (winStarts i).Nonempty := by
  classical
  obtain ⟨n, hn⟩ := bandT_nonempty i
  exact ⟨2 * kIdx (gridAt i) n (Classical.arbitrary _),
    (mem_winStarts i).2 ⟨n, hn, Classical.arbitrary _, rfl⟩⟩

lemma card_winStarts_pos (i : ℕ) : 0 < (winStarts i).card :=
  Finset.card_pos.2 (winStarts_nonempty i)

/-- **Distinct window starts are a full window apart.**  This is `windows_eq_or_disjoint` read on
the `Finset` of starts. -/
theorem winStarts_gap (i : ℕ) {q q' : ℕ} (hq : q ∈ winStarts i) (hq' : q' ∈ winStarts i)
    (hlt : q < q') : q + kk i ≤ q' := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  obtain ⟨n', hn', β, rfl⟩ := (mem_winStarts i).1 hq'
  rcases windows_eq_or_disjoint i (bandT_subset i hn) (bandT_subset i hn') α β with h | h | h
  · omega
  · exact h
  · omega

/-- Every band-`i` window start is above the band floor. -/
lemma bandLo_le_winStarts (i : ℕ) {q : ℕ} (hq : q ∈ winStarts i) : bandLo i ≤ q := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  exact bandLo_le_pos_of_mem_bandT i hn α

/-- Every band-`i` window lies below the band ceiling. -/
lemma winStarts_add_lt_bandTop (i : ℕ) {q : ℕ} (hq : q ∈ winStarts i) {p : ℕ} (hp : p < kk i) :
    q + p < bandTop i := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  exact pos_lt_bandTop i (bandT_subset i hn) α hp

/-! ### Enumerating them -/

/-- The `a`-th window start of band `i`, in increasing order (cyclically extended). -/
noncomputable def fnth (i a : ℕ) : ℕ :=
  (winStarts i).orderEmbOfFin rfl ⟨a % (winStarts i).card, Nat.mod_lt _ (card_winStarts_pos i)⟩

lemma fnth_mem (i a : ℕ) : fnth i a ∈ winStarts i := by
  rw [fnth]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma fnth_lt_fnth {i a b : ℕ} (hab : a < b) (hb : b < (winStarts i).card) :
    fnth i a < fnth i b := by
  have ha : a < (winStarts i).card := lt_trans hab hb
  rw [fnth, fnth]
  refine (Finset.orderEmbOfFin (winStarts i) rfl).strictMono ?_
  refine Fin.mk_lt_mk.2 ?_
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

/-- **Consecutive window starts are a full window apart.** -/
lemma fnth_gap {i a b : ℕ} (hab : a < b) (hb : b < (winStarts i).card) :
    fnth i a + kk i ≤ fnth i b :=
  winStarts_gap i (fnth_mem i a) (fnth_mem i b) (fnth_lt_fnth hab hb)

lemma bandLo_le_fnth (i a : ℕ) : bandLo i ≤ fnth i a :=
  bandLo_le_winStarts i (fnth_mem i a)

lemma fnth_add_lt_bandTop (i a : ℕ) {p : ℕ} (hp : p < kk i) : fnth i a + p < bandTop i :=
  winStarts_add_lt_bandTop i (fnth_mem i a) hp

/-! ### The schedule-only position map -/

/-- The number of digits band `i` contributes to the schedule-only read. -/
noncomputable def fL (i : ℕ) : ℕ := (winStarts i).card * kk i

lemma fL_pos (i : ℕ) : 0 < fL i :=
  Nat.mul_pos (card_winStarts_pos i) (by unfold kk; omega)

/-- The cutoff after the first `i` bands. -/
noncomputable def fT : ℕ → ℕ
  | 0 => 0
  | (i + 1) => fT i + fL i

lemma fT_lt_succ (i : ℕ) : fT i < fT (i + 1) := by
  have := fL_pos i
  show fT i < fT i + fL i
  omega

lemma fT_mono : Monotone fT := monotone_nat_of_le_succ fun i => (fT_lt_succ i).le

lemma self_le_fT (i : ℕ) : i ≤ fT i := by
  induction i with
  | zero => simp [fT]
  | succ i ih => have := fT_lt_succ i; omega

/-- The band a read index belongs to. -/
noncomputable def fgrp (j : ℕ) : ℕ := Nat.findGreatest (fun m => fT m ≤ j) j

lemma fgrp_eq {i j : ℕ} (h1 : fT i ≤ j) (h2 : j < fT (i + 1)) : fgrp j = i := by
  classical
  have hij : i ≤ j := le_trans (self_le_fT i) h1
  have hle : i ≤ fgrp j := Nat.le_findGreatest hij h1
  by_contra hne
  have hlt : i < fgrp j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : fT (fgrp j) ≤ j := Nat.findGreatest_spec (P := fun m => fT m ≤ j) hij h1
  have : fT (i + 1) ≤ fT (fgrp j) := fT_mono (by omega)
  omega

lemma fT_fgrp_le (j : ℕ) : fT (fgrp j) ≤ j := by
  classical
  exact Nat.findGreatest_spec (P := fun m => fT m ≤ j) (Nat.zero_le j) (by simp [fT])

lemma lt_fT_fgrp_succ (j : ℕ) : j < fT (fgrp j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : fgrp j + 1 ≤ j := le_trans (self_le_fT (fgrp j + 1)) hcon
  have h2 : fgrp j + 1 ≤ fgrp j := Nat.le_findGreatest h1 hcon
  omega

/-- **The schedule-only position map.**  Bands in order; inside a band, the distinct window
starts in order; inside a window, the `m_i` consecutive positions.  No reference to `G₄`. -/
noncomputable def fullPos (j : ℕ) : ℕ :=
  fnth (fgrp j) ((j - fT (fgrp j)) / kk (fgrp j)) + (j - fT (fgrp j)) % kk (fgrp j)

lemma fullPos_eq {i j : ℕ} (h1 : fT i ≤ j) (h2 : j < fT (i + 1)) :
    fullPos j = fnth i ((j - fT i) / kk i) + (j - fT i) % kk i := by
  rw [fullPos, fgrp_eq h1 h2]

/-- **The schedule-only read is a genuine subsequence.** -/
theorem fullPos_strictMono : StrictMono fullPos := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  set i := fgrp j with hi
  have h1 : fT i ≤ j := fT_fgrp_le j
  have h2 : j < fT (i + 1) := lt_fT_fgrp_succ j
  have hfT : fT (i + 1) = fT i + fL i := rfl
  set r : ℕ := j - fT i with hr
  have hrlt : r < fL i := by omega
  have hkk : 0 < kk i := by unfold kk; omega
  set a : ℕ := r / kk i with ha
  set p : ℕ := r % kk i with hp
  have hpk : p < kk i := Nat.mod_lt _ hkk
  have hra : r = a * kk i + p := (Nat.div_add_mod' r (kk i)).symm
  have hacard : a < (winStarts i).card := by
    by_contra hcon
    push_neg at hcon
    have : (winStarts i).card * kk i ≤ a * kk i := Nat.mul_le_mul_right _ hcon
    rw [fL] at hrlt
    omega
  have hj : fullPos j = fnth i a + p := fullPos_eq h1 h2
  rcases Nat.lt_or_ge (p + 1) (kk i) with hcase | hcase
  · have hr1 : j + 1 - fT i = r + 1 := by omega
    have hlt1 : j + 1 < fT (i + 1) := by
      rw [hfT, fL]
      have : (a + 1) * kk i ≤ (winStarts i).card * kk i := Nat.mul_le_mul_right _ hacard
      have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
      omega
    have hdiv : (r + 1) / kk i = a := by
      rw [hra]
      have hc : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hcase]
      omega
    have hmod : (r + 1) % kk i = p + 1 := by
      rw [hra]
      have hc : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hcase]
    have := fullPos_eq (i := i) (j := j + 1) (by omega) hlt1
    rw [this, hr1, hdiv, hmod, hj]
    omega
  · have hpk1 : p + 1 = kk i := by omega
    rcases Nat.lt_or_ge (a + 1) (winStarts i).card with hcase2 | hcase2
    · have hr1 : j + 1 - fT i = r + 1 := by omega
      have hreq : r + 1 = (a + 1) * kk i := by
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hlt1 : j + 1 < fT (i + 1) := by
        rw [hfT, fL]
        have : (a + 1) * kk i < (winStarts i).card * kk i :=
          Nat.mul_lt_mul_of_lt_of_le hcase2 (le_refl _) hkk
        omega
      have hdiv : (r + 1) / kk i = a + 1 := by rw [hreq, Nat.mul_div_cancel _ hkk]
      have hmod : (r + 1) % kk i = 0 := by rw [hreq, Nat.mul_mod_left]
      have heq := fullPos_eq (i := i) (j := j + 1) (by omega) hlt1
      rw [heq, hr1, hdiv, hmod, hj]
      have hgap := fnth_gap (i := i) (a := a) (b := a + 1) (by omega) hcase2
      omega
    · have hacard' : a + 1 = (winStarts i).card := by omega
      have hreq : r + 1 = fL i := by
        rw [fL, ← hacard']
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hj1 : j + 1 = fT (i + 1) := by rw [hfT]; omega
      have hlt2 : fT (i + 1) ≤ j + 1 := by omega
      have hlt3 : j + 1 < fT (i + 1 + 1) := by
        have := fT_lt_succ (i + 1)
        omega
      have heq := fullPos_eq (i := i + 1) (j := j + 1) hlt2 hlt3
      have hzero : j + 1 - fT (i + 1) = 0 := by omega
      rw [heq, hzero, Nat.zero_div, Nat.zero_mod, hj]
      have hup : bandLo (i + 1) ≤ fnth (i + 1) 0 := bandLo_le_fnth (i + 1) 0
      have hlo : bandLo (i + 1) = bandTop i := rfl
      have hdown : fnth i a + p < bandTop i := fnth_add_lt_bandTop i a hpk
      omega

/-! ### The digits read, and the window dictionary -/

/-- The digit sequence read along `fullPos`. -/
noncomputable def fullDig (x : ℝ) (j : ℕ) : ℕ := digitOf 2 (Int.fract x) (fullPos j)

lemma fullDig_lt (x : ℝ) (j : ℕ) : fullDig x j < 2 := Nat.mod_lt _ (by omega)

/-- Inside band `i`, the `a`-th window occupies the read indices `fT i + a·m_i + q`. -/
lemma fullPos_window (i a q : ℕ) (ha : a < (winStarts i).card) (hq : q < kk i) :
    fullPos (fT i + a * kk i + q) = fnth i a + q := by
  have hkk : 0 < kk i := by unfold kk; omega
  have hlt : a * kk i + q < fL i := by
    rw [fL]
    have : (a + 1) * kk i ≤ (winStarts i).card * kk i := Nat.mul_le_mul_right _ ha
    have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
    omega
  have h1 : fT i ≤ fT i + a * kk i + q := by omega
  have h2 : fT i + a * kk i + q < fT (i + 1) := by
    show fT i + a * kk i + q < fT i + fL i
    omega
  have hsub : fT i + a * kk i + q - fT i = a * kk i + q := by omega
  have hdiv : (a * kk i + q) / kk i = a := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hq]
    omega
  have hmod : (a * kk i + q) % kk i = q := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  rw [fullPos_eq h1 h2, hsub, hdiv, hmod]

/-- **The dictionary**: a window of `v` fitting inside one band window is an occurrence of `v`
in `x` at the corresponding digit position. -/
lemma matchesAt_fullDig_iff (x : ℝ) (i a q : ℕ) (v : List ℕ) (ha : a < (winStarts i).card)
    (hq : q + v.length ≤ kk i) :
    MatchesAt (fullDig x) v (fT i + a * kk i + q) ↔ OccursAt 2 x v (fnth i a + q) := by
  have hkey : ∀ t < v.length,
      fullDig x (fT i + a * kk i + q + t) = digitOf 2 (Int.fract x) (fnth i a + q + t) := by
    intro t ht
    have hqt : q + t < kk i := by omega
    have hrw : fT i + a * kk i + q + t = fT i + a * kk i + (q + t) := by ring
    rw [fullDig, hrw, fullPos_window i a (q + t) ha hqt]
    ring_nf
  constructor
  · intro h t ht
    have h' := h t ht
    rw [hkey t ht] at h'
    rw [h']
    exact (List.getD_eq_getElem v 0 ht)
  · intro h t ht
    show fullDig x (fT i + a * kk i + q + t) = _
    rw [hkey t ht, h t ht]
    exact (List.getD_eq_getElem v 0 ht).symm

set_option maxHeartbeats 1000000 in
/-- Summing over the band's window-start enumeration is summing over the starts. -/
lemma sum_range_fnth {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (winStarts i).card, g (fnth i a) = ∑ q ∈ winStarts i, g q := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (fnth i a))]
  have hstep : ∀ a : Fin (winStarts i).card,
      g (fnth i (a : ℕ)) = g ((winStarts i).orderEmbOfFin rfl a) := by
    intro a
    have hfin : (⟨(a : ℕ) % (winStarts i).card, Nat.mod_lt _ (card_winStarts_pos i)⟩ :
        Fin (winStarts i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [fnth, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [← Finset.sum_attach (winStarts i) g]
  refine Fintype.sum_bijective (fun a : Fin (winStarts i).card =>
    (⟨(winStarts i).orderEmbOfFin rfl a, Finset.orderEmbOfFin_mem _ _ _⟩ :
      (winStarts i : Finset ℕ))) ?_ _ _ (fun a => rfl)
  constructor
  · intro a b hab
    have : ((winStarts i).orderEmbOfFin rfl a : ℕ) = (winStarts i).orderEmbOfFin rfl b :=
      congrArg Subtype.val hab
    exact (winStarts i).orderEmbOfFin rfl |>.injective (by exact_mod_cast this)
  · rintro ⟨q, hq⟩
    have hrange : q ∈ Set.range ((winStarts i).orderEmbOfFin (rfl : (winStarts i).card = _)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hq
    obtain ⟨a, ha⟩ := hrange
    exact ⟨a, Subtype.ext ha⟩

end NormalNumbers.G4.Sched
