/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBarrier

/-!
# Entropy expedition §6, positive branch: how large an averaging family must be

`G4EntropyBarrier.half_le_density_of_forces_normal` says any repair of the refuted transfer
must read a set of digit positions of upper density `≥ 1/2`.  The brief's first proposed repair
is to **average over a family of admissible samplers** (translated grids, varied frozen
residues).  This module names that property and proves the implication it supplies — a *lower
bound on the size of the family*, which is the obstruction the repair has to pay for.

* `card_family_ge` — pure counting: if a finite family of position sets covers at least half of
  `[0,L)` and each member meets the per-scale bound `c·⌊L/(2 d_min)⌋`, then `d_min ≤ |F|·c`.
* `card_grid_family_ge` — the same for families of `GridParams`, with `c = |Atom|·m` supplied by
  `card_sampledPos_lt_le'`.
* `Sched.card_family_ge_two_pow` — at the implemented schedule, `key_size` turns that into
  `2^(i+2) ≤ |F|`.

So **no fixed finite family of admissible grids can work**: the number of samplers needed to
see half the digit positions grows at least geometrically in the family index, hence beyond
every bound.  A repair must vary the frozen residue over a set that grows with `K` — it cannot
be a bounded translation average.  This is exactly why the lap-8 witness survives averaging over
any bounded family: its digits are free off a set of density `≤ 1/4 · |F|`.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4

/-! ### Counting: a union of sparse sets is sparse -/

variable {ι : Type*} [DecidableEq ι]

/-- A set covered by a finite family is counted by the family. -/
theorem card_filter_le_sum (F : Finset ι) (S : ι → Finset ℕ) (U : ℕ → Prop) [DecidablePred U]
    (L : ℕ) (hU : ∀ j < L, U j → ∃ ν ∈ F, j ∈ S ν) :
    ((Finset.range L).filter U).card ≤ ∑ ν ∈ F, ((S ν).filter (fun j => j < L)).card := by
  classical
  have hsub : (Finset.range L).filter U ⊆ F.biUnion (fun ν => (S ν).filter (fun j => j < L)) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨ν, hν, hjν⟩ := hU j hj.1 hj.2
    exact Finset.mem_biUnion.2 ⟨ν, hν, Finset.mem_filter.2 ⟨hjν, hj.1⟩⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

/-- **The family-size bound.**  If every member of `F` reads at most `c` positions per period
`2·dm` below `L`, and the family together covers at least half of `[0, L)`, then `dm ≤ |F|·c`. -/
theorem card_family_ge (F : Finset ι) (S : ι → Finset ℕ) (U : ℕ → Prop) [DecidablePred U]
    {L dm c : ℕ} (hdm : 0 < dm) (hL : 0 < L)
    (hbound : ∀ ν ∈ F, ((S ν).filter (fun j => j < L)).card ≤ c * (L / (2 * dm)))
    (hU : ∀ j < L, U j → ∃ ν ∈ F, j ∈ S ν)
    (hdense : L ≤ 2 * ((Finset.range L).filter U).card) :
    dm ≤ F.card * c := by
  classical
  set q := L / (2 * dm) with hq
  have hsum : ((Finset.range L).filter U).card ≤ F.card * (c * q) := by
    refine le_trans (card_filter_le_sum F S U L hU) ?_
    calc ∑ ν ∈ F, ((S ν).filter (fun j => j < L)).card ≤ ∑ _ν ∈ F, c * q :=
          Finset.sum_le_sum hbound
      _ = F.card * (c * q) := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : L ≤ 2 * (F.card * (c * q)) := le_trans hdense (by omega)
  have hqle : 2 * dm * q ≤ L := Nat.mul_div_le L (2 * dm)
  by_contra hcon
  push_neg at hcon
  have hq1 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h; · rw [h0] at h2; omega
    exact h
  have hlt : F.card * c * q < dm * q :=
    Nat.mul_lt_mul_of_lt_of_le hcon (le_refl q) hq1
  have : 2 * (F.card * (c * q)) = 2 * (F.card * c * q) := by ring
  have hdq : 2 * (dm * q) ≤ L := by rw [← mul_assoc]; exact hqle
  omega

/-! ### Families of grids -/

/-- **The family-size bound for grids.**  A family of admissible grids whose sampled positions
cover half of `[0, L)` must have at least `d_min / (|Atom|·m)` members. -/
theorem card_grid_family_ge (F : Finset ι) (G : ι → GridParams) (U : ℕ → Prop) [DecidablePred U]
    {X m dm A L : ℕ} (hdm : 0 < dm) (hL : 0 < L)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hd : ∀ ν ∈ F, ∀ α : (G ν).Atom, dm ≤ (G ν).d α)
    (hA : ∀ ν ∈ F, Fintype.card (G ν).Atom ≤ A)
    (hU : ∀ j < L, U j → ∃ ν ∈ F, j ∈ sampledPos (G ν) X m)
    (hdense : L ≤ 2 * ((Finset.range L).filter U).card) :
    dm ≤ F.card * (A * m) := by
  classical
  refine card_family_ge F (fun ν => sampledPos (G ν) X m) U hdm hL (fun ν hν => ?_) hU hdense
  refine le_trans (card_sampledPos_lt_le' (G ν) (hT ν hν) X m L hdm (hd ν hν)) ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hA ν hν))

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The named property** the §6 positive branch must supply at scale `i`: a finite family of
grids, each as sparse per period as the implemented one (same multiplier lower bound `dmin i`,
same atom count), whose sampled positions together cover at least half of some prefix `[0,L)`.

This is stated with no reference to normality: it is exactly the density-`≥ 1/2` input that
`G4EntropyBarrier.half_le_density_of_forces_normal` shows any repair needs. -/
structure ReadsHalf (i : ℕ) (F : Finset ι) (G : ι → GridParams) (U : ℕ → Prop)
    [DecidablePred U] (L : ℕ) : Prop where
  /-- the offsets are not constant, so `kIdx` is a positive multiple of `d` -/
  nonconstant : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β
  /-- every multiplier is at least the implemented grid's `d_min` -/
  dmin_le : ∀ ν ∈ F, ∀ α : (G ν).Atom, dmin i ≤ (G ν).d α
  /-- the atom count is the implemented one -/
  card_atom : ∀ ν ∈ F, Fintype.card (G ν).Atom ≤ (KK i ^ 2 + 1) ^ KK i
  /-- `U` is covered by the family's sampled positions -/
  covered : ∀ j < L, U j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (X (KK i)) (kk i)
  /-- `U` is at least half of `[0, L)` -/
  dense : L ≤ 2 * ((Finset.range L).filter U).card

lemma dmin_pos (i : ℕ) : 0 < dmin i := by unfold dmin; omega

/-- **The implication the positive branch supplies.**  An admissible family that reads half the
positions at scale `i` has at least `2^(i+2)` members.

So averaging over a *bounded* family of translated grids can never defeat the lap-8 witness:
the family must grow at least geometrically in the scale index.  Any repair has to vary the
frozen residue over a set whose size grows with `K`, not over a fixed set of translations. -/
theorem card_family_ge_two_pow (i : ℕ) (F : Finset ι) (G : ι → GridParams) (U : ℕ → Prop)
    [DecidablePred U] {L : ℕ} (hL : 0 < L) (h : ReadsHalf i F G U L) :
    2 ^ (i + 2) ≤ F.card := by
  have hbase := card_grid_family_ge (A := (KK i ^ 2 + 1) ^ KK i) (m := kk i)
    F G U (dmin_pos i) hL h.nonconstant h.dmin_le h.card_atom h.covered h.dense
  have hkey := key_size i
  have hHm : 0 < (KK i ^ 2 + 1) ^ KK i * kk i := by
    have h1 : 0 < (KK i ^ 2 + 1) ^ KK i := pow_pos (by omega) _
    have h2 : 0 < kk i := by unfold kk; omega
    exact Nat.mul_pos h1 h2
  -- `2^(i+3)·(H·m) ≤ 2·dmin ≤ 2·|F|·(H·m)`
  have hchain : 2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * kk i)
      ≤ 2 * (F.card * ((KK i ^ 2 + 1) ^ KK i * kk i)) := by
    refine le_trans hkey ?_
    exact Nat.mul_le_mul_left 2 hbase
  have hrw : 2 ^ (i + 3) * ((KK i ^ 2 + 1) ^ KK i * kk i)
      = 2 ^ (i + 2) * ((KK i ^ 2 + 1) ^ KK i * kk i) * 2 := by
    rw [pow_succ]; ring
  have hrw2 : 2 * (F.card * ((KK i ^ 2 + 1) ^ KK i * kk i))
      = F.card * ((KK i ^ 2 + 1) ^ KK i * kk i) * 2 := by ring
  rw [hrw, hrw2] at hchain
  have h3 : 2 ^ (i + 2) * ((KK i ^ 2 + 1) ^ KK i * kk i)
      ≤ F.card * ((KK i ^ 2 + 1) ^ KK i * kk i) := Nat.le_of_mul_le_mul_right hchain (by omega)
  exact Nat.le_of_mul_le_mul_right (by rw [mul_comm] at h3 ⊢; exact h3) hHm

end NormalNumbers.G4.Sched
