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

end NormalNumbers.G4.Sched
