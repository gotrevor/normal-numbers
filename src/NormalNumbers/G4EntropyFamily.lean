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

/-! ### Families with common multipliers cannot help at all

The count above is indexed by the *family*; but the sampled positions of a grid depend on the
grid only through its multiplier map `α ↦ d_α`.  Translating the grid — varying the frozen
residue `b₀`, hence every offset `t_α` — moves the sample point `n`, and it moves `kIdx`, but
`d_α ∣ kIdx` holds for **every** admissible `n`, so every sampled position stays in
`2 d_α ℕ + [0,m)`.  A family of grids sharing one multiplier set therefore has a union of
sampled positions no denser than a single member's, no matter how many members it has. -/

/-- The positions `2·(d·c) + h` with `1 ≤ c ≤ L/(2d)` and `h < m` — everything a grid with
multiplier `d` can read below `L`. -/
noncomputable def periodCol (d m L : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (L / (2 * d))) ×ˢ Finset.range m).image (fun z => 2 * (d * z.1) + z.2)

lemma card_periodCol_le (d m L : ℕ) : (periodCol d m L).card ≤ (L / (2 * d)) * m := by
  refine le_trans Finset.card_image_le ?_
  simp [periodCol, Finset.card_product, Nat.card_Icc]

lemma mem_periodCol {d m L c h : ℕ} (hd : 0 < d) (hc : 1 ≤ c) (hh : h < m)
    (hL : 2 * (d * c) + h < L) : 2 * (d * c) + h ∈ periodCol d m L := by
  refine Finset.mem_image.2 ⟨(c, h), ?_, rfl⟩
  refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hc, ?_⟩, Finset.mem_range.2 hh⟩
  refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
  calc c * (2 * d) = 2 * (d * c) := by ring
    _ ≤ 2 * (d * c) + h := Nat.le_add_right _ _
    _ ≤ L := le_of_lt hL

/-- **The multiplier bound.**  Whatever the family, if every member's multipliers lie in one
finite set `D`, the positions the family reads below `L` number at most `Σ_{d ∈ D} m·L/(2d)` —
a quantity with no `|F|` in it. -/
theorem card_filter_le_of_multipliers (D : Finset ℕ) (F : Finset ι) (G : ι → GridParams)
    (U : ℕ → Prop) [DecidablePred U] {X m L : ℕ}
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hD : ∀ ν ∈ F, ∀ α : (G ν).Atom, (G ν).d α ∈ D)
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ F, j ∈ sampledPos (G ν) X m) :
    ((Finset.range L).filter U).card ≤ ∑ d ∈ D, (L / (2 * d)) * m := by
  classical
  have hsub : (Finset.range L).filter U ⊆ D.biUnion (fun d => periodCol d m L) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨ν, hν, hjν⟩ := hcov j hj.1 hj.2
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (G ν)).1 hjν
    obtain ⟨c, hc1, hc⟩ := exists_kIdx_eq (G ν) (hT ν hν) hn α
    refine Finset.mem_biUnion.2 ⟨(G ν).d α, hD ν hν α, ?_⟩
    rw [hc] at hj ⊢
    exact mem_periodCol ((G ν).d_pos α) hc1 hh hj.1
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun d _ => card_periodCol_le d m L

/-- The same with a uniform multiplier lower bound: `|F|` has disappeared. -/
theorem card_filter_le_of_multipliers' (D : Finset ℕ) (F : Finset ι) (G : ι → GridParams)
    (U : ℕ → Prop) [DecidablePred U] {X m L dm : ℕ} (hdm : 0 < dm)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hD : ∀ ν ∈ F, ∀ α : (G ν).Atom, (G ν).d α ∈ D)
    (hdmD : ∀ d ∈ D, dm ≤ d)
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ F, j ∈ sampledPos (G ν) X m) :
    ((Finset.range L).filter U).card ≤ D.card * ((L / (2 * dm)) * m) := by
  refine le_trans (card_filter_le_of_multipliers D F G U hT hD hcov) ?_
  calc ∑ d ∈ D, (L / (2 * d)) * m ≤ ∑ _d ∈ D, (L / (2 * dm)) * m := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact Nat.mul_le_mul_right _ (Nat.div_le_div_left
          (Nat.mul_le_mul_left 2 (hdmD d hd)) (by omega))
    _ = D.card * ((L / (2 * dm)) * m) := by rw [Finset.sum_const, smul_eq_mul]

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

/-! ### Translated grids are refuted as a repair -/

/-- The multipliers of the implemented grid at scale `i`. -/
noncomputable def multipliers (i : ℕ) : Finset ℕ :=
  Finset.image (gridAt i).d (Finset.univ : Finset (gridAt i).Atom)

lemma card_multipliers_le (i : ℕ) : (multipliers i).card ≤ (KK i ^ 2 + 1) ^ KK i := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, card_Atom_gridAt]

lemma dmin_le_of_mem_multipliers {i d : ℕ} (hd : d ∈ multipliers i) : dmin i ≤ d := by
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hd
  exact dmin_le_d i α

/-- **Translating the grid cannot help, at any family size.**

If every grid in the family `F` has the *same multipliers* as the implemented grid at scale `i`
— which is exactly what varying the frozen residue `b₀`, or translating the grid, produces —
then the family's sampled positions cover less than half of every prefix `[0,L)`, however many
members `F` has.

The reason is structural, not quantitative: `d_α ∣ kIdx` holds for every admissible sample
point, so each member reads only positions in `2 d_α ℕ + [0, m_K)`, and that set does not depend
on `b₀` at all.  A union of copies of one set is that set. -/
theorem not_dense_of_common_multipliers (i : ℕ) (F : Finset ι) (G : ι → GridParams)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ} (hL : 0 < L)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hD : ∀ ν ∈ F, ∀ α : (G ν).Atom, (G ν).d α ∈ multipliers i)
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (X (KK i)) (kk i)) :
    ¬ (L ≤ 2 * ((Finset.range L).filter U).card) := by
  intro hdense
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set m := kk i with hm
  set q := L / (2 * dmin i) with hq
  have hbase := card_filter_le_of_multipliers' (multipliers i) F G U (dmin_pos i) hT hD
    (fun d hd => dmin_le_of_mem_multipliers hd) hcov
  have hcard : ((Finset.range L).filter U).card ≤ H * m * q := by
    refine le_trans hbase ?_
    calc (multipliers i).card * (q * m) ≤ H * (q * m) :=
          Nat.mul_le_mul_right _ (card_multipliers_le i)
      _ = H * m * q := by ring
  -- `key_size`: `8·(H·m) ≤ 2^(i+3)·(H·m) ≤ 2·dmin`
  have hkey : 8 * (H * m) ≤ 2 * dmin i := by
    refine le_trans ?_ (key_size i)
    exact Nat.mul_le_mul_right _ (by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this)
  have hqle : 2 * dmin i * q = 2 * dmin i * (L / (2 * dmin i)) := rfl
  have hqL : 2 * dmin i * q ≤ L := Nat.mul_div_le L (2 * dmin i)
  have h8 : 8 * (H * m * q) ≤ L := by
    calc 8 * (H * m * q) = (8 * (H * m)) * q := by ring
      _ ≤ (2 * dmin i) * q := Nat.mul_le_mul_right _ hkey
      _ ≤ L := hqL
  omega

/-- The same conclusion phrased against the named property: an admissible family whose
multipliers are the implemented ones never `ReadsHalf`. -/
theorem not_readsHalf_of_common_multipliers (i : ℕ) (F : Finset ι) (G : ι → GridParams)
    (U : ℕ → Prop) [DecidablePred U] {L : ℕ} (hL : 0 < L)
    (hD : ∀ ν ∈ F, ∀ α : (G ν).Atom, (G ν).d α ∈ multipliers i) :
    ¬ ReadsHalf i F G U L := by
  intro h
  exact not_dense_of_common_multipliers i F G U hL h.nonconstant hD h.covered h.dense

end NormalNumbers.G4.Sched
