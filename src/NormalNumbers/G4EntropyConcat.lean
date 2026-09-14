/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOcc

/-!
# Entropy expedition — the `(scale, repetition)` assembly (rung 3, abstract)

Rungs 1–2 produce, for each scale `i`, one finite **block**: `L i` digits whose every window
frequency approaches `b^{−|v|}` as `i → ∞`.  This module turns that *sequence of finite
statements* into **one infinite sequence** that is normal.

The obstruction is the prefix problem: `L (i+1) ≫ ∑_{j ≤ i} L j` (in the application `L i` is
`|P_i|·|Atom_i|·m_i`, which explodes with `i`), so a prefix ending part-way through a fresh
block is never negligible.  The fix is **repetition**: group `m` is block `m` repeated `rep m`
times, with `rep m` chosen so that group `m` dominates everything before it *and* the next
block.  A repeated block costs no seam at all — inside a group the sequence is exactly
`L m`-periodic, so `card_filter_periodic` counts its windows cyclically with no error.

* `per`/`cyc` — the periodic extension of a block and its **cyclic** window count.
* `Tacc`/`rep` — the accumulated lengths and the repetition counts,
  `rep m · L m > (m+2)·(Tacc m + L (m+1))`.
* `seq` — the concatenated digit sequence; `grp` locates the group of a position.
* `tendsto_winCount_seq` — the assembly: `cyc i / L i → c` and `L i → ∞` give
  `winCount (seq) v N / N → c`.
* `isNormalSequence_seq` — with rung 1's criterion, `IsNormalSequence b (seq L d)`.

Nothing here mentions `G₄`.
-/

namespace NormalNumbers
namespace BlockConcat

open Filter Finset

/-! ### The periodic extension of one block -/

/-- The `L i`-periodic extension of block `i`. -/
def per (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ := d i (j % L i)

lemma per_periodic (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (i x : ℕ) :
    per L d i (x + L i) = per L d i x := by
  unfold per; rw [Nat.add_mod_right]

lemma matchesAt_per_periodic (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (i : ℕ) (v : List ℕ) (p : ℕ) :
    MatchesAt (per L d i) v (p + L i) ↔ MatchesAt (per L d i) v p := by
  have hrw : ∀ j : ℕ, p + L i + j = (p + j) + L i := by intro j; ring
  constructor <;> intro h j hj
  · have h' := h j hj
    rw [hrw j, per_periodic] at h'
    exact h'
  · have h' := h j hj
    rw [hrw j, per_periodic]
    exact h'

/-- **Cyclic window count**: the number of windows of `v` in one period of block `i`,
wrap-around included. -/
def cyc (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (i : ℕ) : ℕ :=
  winCount (per L d i) v (L i)

lemma cyc_le (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (i : ℕ) : cyc L d v i ≤ L i :=
  winCount_le _ _ _

/-- The window count of a repeated block is exactly `r` cyclic counts — **no seam**. -/
lemma winCount_per_mul (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (i r : ℕ) :
    winCount (per L d i) v (r * L i) = r * cyc L d v i :=
  card_filter_periodic (matchesAt_per_periodic L d i v) r

/-! ### The schedule of repetitions -/

/-- Accumulated length after `m` groups. -/
def Tacc (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Tacc L m + ((m + 2) * (Tacc L m + L (m + 1)) / L m + 1) * L m

/-- How many times block `m` is repeated. -/
def rep (L : ℕ → ℕ) (m : ℕ) : ℕ := (m + 2) * (Tacc L m + L (m + 1)) / L m + 1

lemma Tacc_succ (L : ℕ → ℕ) (m : ℕ) : Tacc L (m + 1) = Tacc L m + rep L m * L m := rfl

lemma rep_pos (L : ℕ → ℕ) (m : ℕ) : 0 < rep L m := Nat.succ_pos _

/-- **The defining inequality**: group `m` dominates everything before it and the next block. -/
lemma lt_rep_mul (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (m : ℕ) :
    (m + 2) * (Tacc L m + L (m + 1)) < rep L m * L m := by
  set x := (m + 2) * (Tacc L m + L (m + 1)) with hx
  have hLm := hL m
  have hdm := Nat.div_add_mod x (L m)
  have hmod := Nat.mod_lt x hLm
  have hexp : rep L m * L m = (x / L m) * L m + L m := by
    unfold rep; rw [← hx]; ring
  have hcomm : L m * (x / L m) = (x / L m) * L m := by ring
  omega

lemma Tacc_lt_succ (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (m : ℕ) : Tacc L m < Tacc L (m + 1) := by
  have h := lt_rep_mul L hL m
  rw [Tacc_succ]
  omega

lemma Tacc_mono (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) : Monotone (Tacc L) := by
  refine monotone_nat_of_le_succ fun m => ?_
  exact (Tacc_lt_succ L hL m).le

lemma self_le_Tacc (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (m : ℕ) : m ≤ Tacc L m := by
  induction m with
  | zero => simp [Tacc]
  | succ m ih => have := Tacc_lt_succ L hL m; omega

/-- Group `m` dominates the accumulated past. -/
lemma Tacc_le_div (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (m : ℕ) :
    (m + 2) * Tacc L m ≤ Tacc L (m + 1) := by
  have h := lt_rep_mul L hL m
  have : (m + 2) * Tacc L m ≤ (m + 2) * (Tacc L m + L (m + 1)) := by
    exact Nat.mul_le_mul_left _ (by omega)
  rw [Tacc_succ]
  omega

/-- Group `m` dominates the **next** block's length. -/
lemma mul_L_succ_le (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (m : ℕ) :
    (m + 2) * L (m + 1) ≤ Tacc L (m + 1) := by
  have h := lt_rep_mul L hL m
  have : (m + 2) * L (m + 1) ≤ (m + 2) * (Tacc L m + L (m + 1)) := by
    exact Nat.mul_le_mul_left _ (by omega)
  rw [Tacc_succ]
  omega

/-! ### The concatenated sequence -/

/-- The group a position belongs to. -/
def grp (L : ℕ → ℕ) (j : ℕ) : ℕ := Nat.findGreatest (fun m => Tacc L m ≤ j) j

/-- **The concatenated digit sequence**: group `m` is block `m` repeated `rep m` times. -/
def seq (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  per L d (grp L j) (j - Tacc L (grp L j))

lemma grp_eq (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) {m j : ℕ}
    (h1 : Tacc L m ≤ j) (h2 : j < Tacc L (m + 1)) : grp L j = m := by
  classical
  have hmj : m ≤ j := le_trans (self_le_Tacc L hL m) h1
  have hle : m ≤ grp L j := Nat.le_findGreatest hmj h1
  by_contra hne
  have hlt : m < grp L j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : Tacc L (grp L j) ≤ j := by
    have h := Nat.findGreatest_spec (P := fun m => Tacc L m ≤ j) hmj h1
    exact h
  have : Tacc L (m + 1) ≤ Tacc L (grp L j) := Tacc_mono L hL (by omega)
  omega

lemma seq_lt {b : ℕ} (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hd : ∀ i j, d i j < b) (j : ℕ) :
    seq L d j < b := hd _ _

/-- **Localization**: a window lying inside group `m` is a window of the periodic block. -/
lemma matchesAt_seq_iff (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i)
    {v : List ℕ} {m p : ℕ} (h1 : Tacc L m ≤ p) (h2 : p + v.length ≤ Tacc L (m + 1)) :
    MatchesAt (seq L d) v p ↔ MatchesAt (per L d m) v (p - Tacc L m) := by
  have hgrp : ∀ j < v.length, grp L (p + j) = m := by
    intro j hj
    exact grp_eq L hL (by omega) (by omega)
  constructor <;> intro h j hj
  · have h' := h j hj
    unfold seq at h'
    rw [hgrp j hj] at h'
    have : p + j - Tacc L m = (p - Tacc L m) + j := by omega
    rwa [this] at h'
  · have h' := h j hj
    show seq L d (p + j) = _
    unfold seq
    rw [hgrp j hj]
    have : p + j - Tacc L m = (p - Tacc L m) + j := by omega
    rw [this]
    exact h'


/-! ### Counting inside one group

Inside group `m` the sequence is exactly `L m`-periodic, so counting is cyclic and exact; the
only error is at the group's right edge, where a window may run out of the group.  That edge
costs at most `|v|` windows, once per group. -/

/-- Windows of `v` starting in `[a, b)`. -/
def cntIco (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (MatchesAt (seq L d) v)).card

lemma cntIco_mono (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) {a b c : ℕ} (h : b ≤ c) :
    cntIco L d v a b ≤ cntIco L d v a c := by
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact Finset.Ico_subset_Ico le_rfl h

lemma cntIco_le (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (a b : ℕ) :
    cntIco L d v a b ≤ b - a := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Nat.card_Ico]

/-- Splitting the count of `[0, n)` at an interior point. -/
lemma winCount_seq_split (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) {a n : ℕ} (h : a ≤ n) :
    winCount (seq L d) v n = winCount (seq L d) v a + cntIco L d v a n :=
  winCount_split _ _ h

/-- The right edge of a window range costs at most `l` windows. -/
lemma card_edge_le {s : Finset ℕ} {a c l : ℕ} (hs : s ⊆ Finset.Ico a c)
    (P : ℕ → Prop) [DecidablePred P] :
    (s.filter P).card ≤ (s.filter (fun p => P p ∧ p + l ≤ c)).card + l := by
  classical
  have hsub : s.filter P
      ⊆ (s.filter (fun p => P p ∧ p + l ≤ c)) ∪ Finset.Ico (c - l) c := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    by_cases hc : p + l ≤ c
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp.1, hp.2, hc⟩)
    · refine Finset.mem_union_right _ ?_
      have := hs hp.1
      simp only [Finset.mem_Ico] at this
      simp only [Finset.mem_Ico]
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Nat.card_Ico]
  omega

/-- **The group count is the cyclic count, up to one edge.**  For every `r ≤ rep m`, the number
of `v`-windows starting in the first `r` copies of block `m` differs from `r · cyc m` by at most
`|v|`. -/
lemma cntIco_group (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {m r : ℕ} (hr : r ≤ rep L m) :
    cntIco L d v (Tacc L m) (Tacc L m + r * L m) ≤ r * cyc L d v m + v.length
      ∧ r * cyc L d v m ≤ cntIco L d v (Tacc L m) (Tacc L m + r * L m) + v.length := by
  classical
  set A := Tacc L m with hA
  set R := r * L m with hR
  set l := v.length with hl
  -- the "good" windows: those that fit inside the first `r` copies
  set Sg := (Finset.Ico A (A + R)).filter (fun p => MatchesAt (seq L d) v p ∧ p + l ≤ A + R)
    with hSg
  set Sg' := (Finset.range R).filter (fun o => MatchesAt (per L d m) v o ∧ o + l ≤ R) with hSg'
  have hrep : A + R ≤ Tacc L (m + 1) := by
    rw [Tacc_succ, hR, ← hA]
    have : r * L m ≤ rep L m * L m := Nat.mul_le_mul_right _ hr
    omega
  have hbij : Sg.card = Sg'.card := by
    rw [Finset.card_bij (fun p _ => p - A)]
    · intro p hp
      simp only [hSg, Finset.mem_filter, Finset.mem_Ico] at hp
      simp only [hSg', Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_, by omega⟩
      exact (matchesAt_seq_iff L d hL (by omega) (by omega)).1 hp.2.1
    · intro p hp q hq hpq
      simp only [hSg, Finset.mem_filter, Finset.mem_Ico] at hp hq
      omega
    · intro o ho
      simp only [hSg', Finset.mem_filter, Finset.mem_range] at ho
      refine ⟨o + A, ?_, by omega⟩
      simp only [hSg, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨by omega, ?_, by omega⟩
      refine (matchesAt_seq_iff L d hL (m := m) (p := o + A) (by omega) (by omega)).2 ?_
      have : o + A - A = o := by omega
      rw [this]
      exact ho.2.1
  -- the edge, on both sides, costs at most `l`
  have hsubset : ∀ (t u : Finset ℕ) (Q R' : ℕ → Prop) [DecidablePred Q] [DecidablePred R'],
      t = u → (∀ p, Q p → R' p) → (t.filter Q).card ≤ (u.filter R').card := by
    intro t u Q R' _ _ htu hQR
    subst htu
    exact Finset.card_le_card (fun p hp => by
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hQR p hp.2⟩)
  have hfull : winCount (per L d m) v R = r * cyc L d v m := winCount_per_mul L d v m r
  have hA1 : cntIco L d v A (A + R) ≤ Sg.card + l :=
    card_edge_le (l := l) (Finset.Subset.refl (Finset.Ico A (A + R))) (MatchesAt (seq L d) v)
  have hA2 : Sg'.card ≤ r * cyc L d v m := by
    rw [← hfull]
    exact hsubset _ _ _ _ rfl (fun p hp => hp.1)
  have hA3 : r * cyc L d v m ≤ Sg'.card + l := by
    rw [← hfull]
    refine card_edge_le (l := l) (a := 0) ?_ (MatchesAt (per L d m) v)
    rw [Finset.range_eq_Ico]
  have hA4 : Sg.card ≤ cntIco L d v A (A + R) :=
    hsubset _ _ _ _ rfl (fun p hp => hp.1)
  refine ⟨le_trans hA1 ?_, le_trans hA3 ?_⟩
  · rw [hbij]; omega
  · rw [← hbij]; omega

end BlockConcat
end NormalNumbers
