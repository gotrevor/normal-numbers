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

/-- **A prefix of a group**: after `q` whole copies of block `m` and a partial copy. -/
lemma cntIco_partial (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {m N : ℕ} (h1 : Tacc L m ≤ N) (h2 : N < Tacc L (m + 1)) :
    cntIco L d v (Tacc L m) N
        ≤ ((N - Tacc L m) / L m + 1) * cyc L d v m + v.length
      ∧ ((N - Tacc L m) / L m) * cyc L d v m
        ≤ cntIco L d v (Tacc L m) N + v.length := by
  set A := Tacc L m with hA
  set q := (N - A) / L m with hq
  have hLm := hL m
  have hdm := Nat.div_add_mod (N - A) (L m)
  rw [← hq] at hdm
  have hmod := Nat.mod_lt (N - A) hLm
  have hcomm : L m * q = q * L m := by rw [hq]; ring
  have hqp1 : (q + 1) * L m = q * L m + L m := by ring
  have hq1 : q * L m ≤ N - A := by omega
  have hq2 : N - A < (q + 1) * L m := by omega
  have hNA : N - A < rep L m * L m := by rw [Tacc_succ] at h2; omega
  have hqlt : q < rep L m := by
    by_contra hcon
    have hcon' : rep L m ≤ q := by omega
    have : rep L m * L m ≤ q * L m := Nat.mul_le_mul hcon' (le_refl (L m))
    omega
  refine ⟨?_, ?_⟩
  · have hstep : cntIco L d v A N ≤ cntIco L d v A (A + (q + 1) * L m) :=
      cntIco_mono L d v (by omega)
    exact le_trans hstep (cntIco_group L d hL v (r := q + 1) (by omega)).1
  · have hstep : cntIco L d v A (A + q * L m) ≤ cntIco L d v A N :=
      cntIco_mono L d v (by omega)
    exact le_trans (cntIco_group L d hL v (r := q) (by omega)).2
      (Nat.add_le_add_right hstep _)

/-- The group index of a position, characterised. -/
lemma grp_spec (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) (j : ℕ) :
    Tacc L (grp L j) ≤ j ∧ j < Tacc L (grp L j + 1) := by
  classical
  have h0 : Tacc L 0 ≤ j := by simp [Tacc]
  have hlo : Tacc L (grp L j) ≤ j := by
    have h := Nat.findGreatest_spec (P := fun m => Tacc L m ≤ j) (Nat.zero_le j) h0
    exact h
  refine ⟨hlo, ?_⟩
  by_contra hcon
  have hcon' : Tacc L (grp L j + 1) ≤ j := by omega
  have hle : grp L j + 1 ≤ j := le_trans (self_le_Tacc L hL _) hcon'
  exact Nat.findGreatest_is_greatest (P := fun m => Tacc L m ≤ j) (Nat.lt_succ_self _) hle hcon'

lemma le_grp (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) {M j : ℕ} (h : Tacc L M ≤ j) : M ≤ grp L j :=
  Nat.le_findGreatest (le_trans (self_le_Tacc L hL M) h) h

/-- `L m ≤ Tacc m` for `m ≥ 1`. -/
lemma L_le_Tacc (L : ℕ → ℕ) (hL : ∀ i, 0 < L i) {m : ℕ} (hm : 1 ≤ m) :
    (m + 1) * L m ≤ Tacc L m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact mul_L_succ_le L hL k

/-! ### The deviation estimate -/

/-- The deviation of the prefix window count from the ideal `c·N`. -/
noncomputable def dev (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (winCount (seq L d) v N : ℝ) - c * N

lemma abs_dev_le_self (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (v : List ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (N : ℕ) : |dev L d v c N| ≤ (N : ℝ) := by
  have h1 : (winCount (seq L d) v N : ℝ) ≤ (N : ℝ) := by exact_mod_cast winCount_le _ _ _
  have h2 : (0 : ℝ) ≤ (winCount (seq L d) v N : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ c * N := mul_nonneg hc0 hN
  have h4 : c * (N : ℝ) ≤ (N : ℝ) := by nlinarith
  unfold dev
  rw [abs_le]
  constructor <;> linarith

/-- **One group's contribution.**  If block `m` is `γ`-good then group `m` moves the deviation
by at most `γ` times the group's length. -/
lemma abs_dev_group (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {c γ : ℝ} {m : ℕ}
    (hγ : |(cyc L d v m : ℝ) - c * L m| + (v.length : ℝ) ≤ γ * L m) :
    |dev L d v c (Tacc L (m + 1)) - dev L d v c (Tacc L m)|
      ≤ γ * ((Tacc L (m + 1) : ℝ) - (Tacc L m : ℝ)) := by
  have hTsucc : Tacc L (m + 1) = Tacc L m + rep L m * L m := Tacc_succ L m
  have hsplit : winCount (seq L d) v (Tacc L (m + 1))
      = winCount (seq L d) v (Tacc L m) + cntIco L d v (Tacc L m) (Tacc L (m + 1)) :=
    winCount_seq_split L d v (Tacc_mono L hL (Nat.le_succ m))
  obtain ⟨hg1, hg2⟩ := cntIco_group L d hL v (m := m) (r := rep L m) le_rfl
  rw [← hTsucc] at hg1 hg2
  have hrep1 : (1 : ℝ) ≤ (rep L m : ℝ) := by exact_mod_cast rep_pos L m
  have hLm0 : (0 : ℝ) ≤ (L m : ℝ) := Nat.cast_nonneg _
  -- real shorthands
  have hXC : |(cntIco L d v (Tacc L m) (Tacc L (m + 1)) : ℝ)
        - (rep L m : ℝ) * (cyc L d v m : ℝ)| ≤ (v.length : ℝ) := by
    rw [abs_le]
    constructor
    · have : ((rep L m * cyc L d v m : ℕ) : ℝ)
          ≤ ((cntIco L d v (Tacc L m) (Tacc L (m + 1)) + v.length : ℕ) : ℝ) := by
        exact_mod_cast hg2
      push_cast at this
      linarith
    · have : ((cntIco L d v (Tacc L m) (Tacc L (m + 1)) : ℕ) : ℝ)
          ≤ ((rep L m * cyc L d v m + v.length : ℕ) : ℝ) := by
        exact_mod_cast hg1
      push_cast at this
      linarith
  have hdiff : dev L d v c (Tacc L (m + 1)) - dev L d v c (Tacc L m)
      = ((cntIco L d v (Tacc L m) (Tacc L (m + 1)) : ℝ)
          - (rep L m : ℝ) * (cyc L d v m : ℝ))
        + (rep L m : ℝ) * ((cyc L d v m : ℝ) - c * (L m : ℝ)) := by
    unfold dev
    rw [hsplit]
    have : ((Tacc L (m + 1) : ℕ) : ℝ) = (Tacc L m : ℝ) + (rep L m : ℝ) * (L m : ℝ) := by
      rw [hTsucc]; push_cast; ring
    rw [this]
    push_cast
    ring
  have hlen : ((Tacc L (m + 1) : ℝ) - (Tacc L m : ℝ)) = (rep L m : ℝ) * (L m : ℝ) := by
    rw [hTsucc]; push_cast; ring
  rw [hdiff, hlen]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (rep L m : ℝ))]
  have hstep : (rep L m : ℝ) * |(cyc L d v m : ℝ) - c * (L m : ℝ)| + (v.length : ℝ)
      ≤ (rep L m : ℝ) * (γ * (L m : ℝ)) := by
    have h1 : (v.length : ℝ) ≤ (rep L m : ℝ) * (v.length : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) v.length]
    nlinarith [abs_nonneg ((cyc L d v m : ℝ) - c * (L m : ℝ))]
  calc |(cntIco L d v (Tacc L m) (Tacc L (m + 1)) : ℝ) - (rep L m : ℝ) * (cyc L d v m : ℝ)|
        + (rep L m : ℝ) * |(cyc L d v m : ℝ) - c * (L m : ℝ)|
      ≤ (v.length : ℝ) + (rep L m : ℝ) * |(cyc L d v m : ℝ) - c * (L m : ℝ)| := by linarith
    _ ≤ (rep L m : ℝ) * (γ * (L m : ℝ)) := by linarith
    _ = γ * ((rep L m : ℝ) * (L m : ℝ)) := by ring

/-- **The accumulated deviation.**  From scale `M` on, the relative deviation at a group
boundary is at most `Tacc M` (a constant) plus `γ` times the length. -/
lemma abs_dev_Tacc (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {c γ : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {M : ℕ}
    (hγ : ∀ j, M ≤ j → |(cyc L d v j : ℝ) - c * (L j : ℝ)| + (v.length : ℝ) ≤ γ * (L j : ℝ)) :
    ∀ m, M ≤ m → |dev L d v c (Tacc L m)| ≤ (Tacc L M : ℝ) + γ * (Tacc L m : ℝ) := by
  have hγ0 : 0 ≤ γ := by
    have h := hγ M le_rfl
    have hLM : (0 : ℝ) < (L M : ℝ) := by exact_mod_cast hL M
    nlinarith [abs_nonneg ((cyc L d v M : ℝ) - c * (L M : ℝ)),
      Nat.cast_nonneg (α := ℝ) v.length]
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h := abs_dev_le_self L d v hc0 hc1 (Tacc L M)
    nlinarith [Nat.cast_nonneg (α := ℝ) (Tacc L M)]
  | succ m hm ih =>
    have hstep := abs_dev_group L d hL v (hγ m hm)
    have htri := abs_sub_abs_le_abs_sub (dev L d v c (Tacc L (m + 1))) (dev L d v c (Tacc L m))
    linarith

/-- **A prefix inside group `m`.**  The deviation at any `N` is the deviation at the group
boundary plus a partial-group term that is `γ·N` up to the length of one block. -/
lemma abs_dev_prefix (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {c γ : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {M N m : ℕ}
    (hγ : ∀ j, M ≤ j → |(cyc L d v j : ℝ) - c * (L j : ℝ)| + (v.length : ℝ) ≤ γ * (L j : ℝ))
    (hm : M ≤ m) (h1 : Tacc L m ≤ N) (h2 : N < Tacc L (m + 1)) :
    |dev L d v c N| ≤ (Tacc L M : ℝ) + γ * (Tacc L m : ℝ)
      + (γ * ((N : ℝ) + (L m : ℝ)) + c * (L m : ℝ) + (v.length : ℝ)) := by
  classical
  have hγ0 : 0 ≤ γ := by
    have h := hγ M le_rfl
    have hLM : (0 : ℝ) < (L M : ℝ) := by exact_mod_cast hL M
    nlinarith [abs_nonneg ((cyc L d v M : ℝ) - c * (L M : ℝ)),
      Nat.cast_nonneg (α := ℝ) v.length]
  set A := Tacc L m with hA
  set q := (N - A) / L m with hq
  obtain ⟨hp1, hp2⟩ := cntIco_partial L d hL v (m := m) h1 h2
  rw [← hA, ← hq] at hp1 hp2
  have hLm := hL m
  have hdm := Nat.div_add_mod (N - A) (L m)
  rw [← hq] at hdm
  have hmod := Nat.mod_lt (N - A) hLm
  have hcomm : L m * q = q * L m := by ring
  have hqp1 : (q + 1) * L m = q * L m + L m := by ring
  have hq1 : q * L m ≤ N - A := by omega
  have hq2 : N - A < (q + 1) * L m := by omega
  -- real versions
  have hDcast : ((N - A : ℕ) : ℝ) = (N : ℝ) - (A : ℝ) := by
    rw [Nat.cast_sub h1]
  have hq1R : (q : ℝ) * (L m : ℝ) ≤ (N : ℝ) - (A : ℝ) := by
    have : ((q * L m : ℕ) : ℝ) ≤ ((N - A : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [hDcast] at this; push_cast at this; linarith
  have hq2R : (N : ℝ) - (A : ℝ) ≤ ((q : ℝ) + 1) * (L m : ℝ) := by
    have : ((N - A : ℕ) : ℝ) ≤ (((q + 1) * L m : ℕ) : ℝ) := by exact_mod_cast hq2.le
    rw [hDcast] at this; push_cast at this; linarith
  have hp1R : (cntIco L d v A N : ℝ) ≤ ((q : ℝ) + 1) * (cyc L d v m : ℝ) + (v.length : ℝ) := by
    have : ((cntIco L d v A N : ℕ) : ℝ) ≤ (((q + 1) * cyc L d v m + v.length : ℕ) : ℝ) := by
      exact_mod_cast hp1
    push_cast at this; linarith
  have hp2R : (q : ℝ) * (cyc L d v m : ℝ) ≤ (cntIco L d v A N : ℝ) + (v.length : ℝ) := by
    have : ((q * cyc L d v m : ℕ) : ℝ) ≤ ((cntIco L d v A N + v.length : ℕ) : ℝ) := by
      exact_mod_cast hp2
    push_cast at this; linarith
  have hgood : |(cyc L d v m : ℝ) - c * (L m : ℝ)| ≤ γ * (L m : ℝ) := by
    have := hγ m hm
    have := Nat.cast_nonneg (α := ℝ) v.length
    linarith [hγ m hm, Nat.cast_nonneg (α := ℝ) v.length]
  have habs := abs_le.1 hgood
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hLmR : (0 : ℝ) ≤ (L m : ℝ) := Nat.cast_nonneg _
  -- the partial-group deviation
  have hpart : |(cntIco L d v A N : ℝ) - c * ((N : ℝ) - (A : ℝ))|
      ≤ γ * ((N : ℝ) + (L m : ℝ)) + c * (L m : ℝ) + (v.length : ℝ) := by
    have hANle : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    have hupper : (cntIco L d v A N : ℝ) - c * ((N : ℝ) - (A : ℝ))
        ≤ γ * ((N : ℝ) + (L m : ℝ)) + c * (L m : ℝ) + (v.length : ℝ) := by
      have hsize : ((q : ℝ) + 1) * (L m : ℝ) ≤ (N : ℝ) + (L m : ℝ) := by nlinarith
      nlinarith [habs.1, habs.2]
    have hlower : c * ((N : ℝ) - (A : ℝ)) - (cntIco L d v A N : ℝ)
        ≤ γ * ((N : ℝ) + (L m : ℝ)) + c * (L m : ℝ) + (v.length : ℝ) := by
      have hsize : (q : ℝ) * (L m : ℝ) ≤ (N : ℝ) + (L m : ℝ) := by nlinarith
      nlinarith [habs.1, habs.2]
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- assemble
  have hsplit : winCount (seq L d) v N = winCount (seq L d) v A + cntIco L d v A N :=
    winCount_seq_split L d v h1
  have hdiff : dev L d v c N - dev L d v c A
      = (cntIco L d v A N : ℝ) - c * ((N : ℝ) - (A : ℝ)) := by
    unfold dev
    rw [hsplit]
    push_cast
    ring
  have hbase := abs_dev_Tacc L d hL v hc0 hc1 hγ m hm
  rw [← hA] at hbase
  have htri := abs_sub_abs_le_abs_sub (dev L d v c N) (dev L d v c A)
  rw [hdiff] at htri
  linarith

/-! ### The assembly -/

/-- **Rung 3.**  If the blocks' cyclic window frequencies converge to `c` and the block lengths
tend to infinity, the concatenated sequence has window frequency `c`. -/
theorem tendsto_winCount_seq (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ) (hL : ∀ i, 0 < L i) (v : List ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcyc : Tendsto (fun i => (cyc L d v i : ℝ) / (L i : ℝ)) atTop (nhds c))
    (hLinf : Tendsto (fun i => (L i : ℝ)) atTop atTop) :
    Tendsto (fun N => (winCount (seq L d) v N : ℝ) / (N : ℝ)) atTop (nhds c) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set γ := ε / 12 with hγdef
  have hγpos : (0 : ℝ) < γ := by rw [hγdef]; positivity
  have h8 : (0 : ℝ) < ε / 8 := by positivity
  -- (a) the blocks are eventually `γ`-good
  have hgood : ∀ᶠ j in atTop,
      |(cyc L d v j : ℝ) - c * (L j : ℝ)| + (v.length : ℝ) ≤ γ * (L j : ℝ) := by
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hcyc (γ / 2) (by positivity)
    have h2 : ∀ᶠ j in atTop, (v.length : ℝ) ≤ γ / 2 * (L j : ℝ) :=
      (Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < γ / 2) hLinf).eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop J, h2] with j hj hj2
    have hLj : (0 : ℝ) < (L j : ℝ) := by exact_mod_cast hL j
    have hj1 : |(cyc L d v j : ℝ) / (L j : ℝ) - c| < γ / 2 := by
      have := hJ j hj
      rwa [Real.dist_eq] at this
    have hkey : |(cyc L d v j : ℝ) - c * (L j : ℝ)|
        = |(cyc L d v j : ℝ) / (L j : ℝ) - c| * (L j : ℝ) := by
      have hre : (cyc L d v j : ℝ) / (L j : ℝ) - c
          = ((cyc L d v j : ℝ) - c * (L j : ℝ)) / (L j : ℝ) := by
        field_simp
      rw [hre, abs_div, abs_of_pos hLj]
      field_simp
    rw [hkey]
    nlinarith
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hgood
  -- (b) a scale index whose reciprocal is small
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (8 / ε)
  have hM₁' : 1 ≤ ((M₁ : ℝ) + 1) * (ε / 8) := by
    have hlt : (8 : ℝ) / ε < (M₁ : ℝ) + 1 := by linarith
    have hmul := mul_lt_mul_of_pos_right hlt h8
    have hid : (8 : ℝ) / ε * (ε / 8) = 1 := by field_simp
    rw [hid] at hmul
    linarith
  set M := max (max M₀ M₁) 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMM₀ : M₀ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMM₁ : M₁ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hγM : ∀ j, M ≤ j →
      |(cyc L d v j : ℝ) - c * (L j : ℝ)| + (v.length : ℝ) ≤ γ * (L j : ℝ) :=
    fun j hj => hM₀ j (le_trans hMM₀ hj)
  have hMrecip : 1 ≤ ((M : ℝ) + 1) * (ε / 8) := by
    have : ((M₁ : ℝ) + 1) ≤ ((M : ℝ) + 1) := by
      have : (M₁ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMM₁
      linarith
    nlinarith
  -- (c) a threshold beyond which the frozen constants are negligible
  have hdivbound : ∀ (a : ℝ) (K : ℕ), 8 * a / ε < (K : ℝ) → ∀ N : ℕ, K ≤ N →
      a ≤ (N : ℝ) * (ε / 8) := by
    intro a K hKa N hN
    have hNK : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlt : 8 * a / ε < (N : ℝ) := lt_of_lt_of_le hKa hNK
    have hmul := mul_lt_mul_of_pos_right hlt h8
    have hid : 8 * a / ε * (ε / 8) = a := by field_simp
    rw [hid] at hmul
    linarith
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt (8 * (Tacc L M : ℝ) / ε)
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (8 * (v.length : ℝ) / ε)
  refine ⟨max (max (Tacc L M) K₁) (max K₂ 1), fun N hN => ?_⟩
  have hNT : Tacc L M ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNK₁ : K₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNK₂ : K₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hTMb : (Tacc L M : ℝ) ≤ (N : ℝ) * (ε / 8) := hdivbound _ K₁ hK₁ N hNK₁
  have hlenb : (v.length : ℝ) ≤ (N : ℝ) * (ε / 8) := hdivbound _ K₂ hK₂ N hNK₂
  -- locate the group
  set m := grp L N with hm
  obtain ⟨hm1, hm2⟩ := grp_spec L hL N
  rw [← hm] at hm1 hm2
  have hMm : M ≤ m := by rw [hm]; exact le_grp L hL hNT
  have hm1' : 1 ≤ m := le_trans hM1 hMm
  -- the block at scale `m` is short compared with `N`
  have hLmN : ((M : ℝ) + 1) * (L m : ℝ) ≤ (N : ℝ) := by
    have h1 : (M + 1) * L m ≤ N := by
      refine le_trans (Nat.mul_le_mul_right _ (by omega)) (le_trans (L_le_Tacc L hL hm1') hm1)
    exact_mod_cast h1
  have hLmnn : (0 : ℝ) ≤ (L m : ℝ) := Nat.cast_nonneg _
  have hLmle : (L m : ℝ) ≤ (N : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hLmb : (L m : ℝ) ≤ (N : ℝ) * (ε / 8) := by nlinarith
  -- the deviation bound
  have hdevb := abs_dev_prefix L d hL v hc0 hc1 hγM hMm hm1 hm2
  have hTmN : (Tacc L m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm1
  have hγ0 : (0 : ℝ) ≤ γ := hγpos.le
  have hfinal : |dev L d v c N| ≤ (N : ℝ) * (5 * ε / 8) := by
    have hcL : c * (L m : ℝ) ≤ (N : ℝ) * (ε / 8) := by nlinarith
    have hstep : γ * ((N : ℝ) + (L m : ℝ)) ≤ 2 * γ * (N : ℝ) := by nlinarith
    have hγT : γ * (Tacc L m : ℝ) ≤ γ * (N : ℝ) := by nlinarith
    have hγval : γ = ε / 12 := hγdef
    nlinarith
  rw [Real.dist_eq]
  have hrw : (winCount (seq L d) v N : ℝ) / (N : ℝ) - c = dev L d v c N / (N : ℝ) := by
    unfold dev
    field_simp
  rw [hrw, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
  nlinarith

/-- **The concatenated sequence is normal.** -/
theorem isNormalSequence_seq {b : ℕ} (hb : 2 ≤ b) (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ)
    (hL : ∀ i, 0 < L i) (hd : ∀ i j, d i j < b)
    (hLinf : Tendsto (fun i => (L i : ℝ)) atTop atTop)
    (hcyc : ∀ v : List ℕ, v ≠ [] → (∀ x ∈ v, x < b) →
      Tendsto (fun i => (cyc L d v i : ℝ) / (L i : ℝ)) atTop (nhds (((b : ℝ) ^ v.length)⁻¹))) :
    IsNormalSequence b (seq L d) := by
  refine isNormalSequence_of_tendsto_winCount (fun v hv hvb => ?_)
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hpow : (1 : ℝ) ≤ (b : ℝ) ^ v.length := one_le_pow₀ hbR.le
  have hc0 : (0 : ℝ) ≤ ((b : ℝ) ^ v.length)⁻¹ := by positivity
  have hc1 : ((b : ℝ) ^ v.length)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]
    exact hpow
  exact tendsto_winCount_seq L d hL v hc0 hc1 (hcyc v hv hvb) hLinf

/-- **The concatenated sequence defines a normal real.**  This is rung 3's endpoint: a sequence
of finite blocks whose window frequencies converge produces ONE number that is normal. -/
theorem isNormal_realOfDigits_seq {b : ℕ} (hb : 2 ≤ b) (L : ℕ → ℕ) (d : ℕ → ℕ → ℕ)
    (hL : ∀ i, 0 < L i) (hd : ∀ i j, d i j < b)
    (hLinf : Tendsto (fun i => (L i : ℝ)) atTop atTop)
    (hcyc : ∀ v : List ℕ, v ≠ [] → (∀ x ∈ v, x < b) →
      Tendsto (fun i => (cyc L d v i : ℝ) / (L i : ℝ)) atTop (nhds (((b : ℝ) ^ v.length)⁻¹))) :
    IsNormal b (realOfDigits b (seq L d)) := by
  have hns := isNormalSequence_seq hb L d hL hd hLinf hcyc
  exact isNormal_realOfDigits b hb _ (fun j => seq_lt L d hd j)
    (properDigits_of_isNormalSequence hb hns) hns

end BlockConcat
end NormalNumbers
