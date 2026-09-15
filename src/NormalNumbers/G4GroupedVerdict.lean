/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4RowVariance

/-!
# Objective R, the last escape: **giving up the single-`n` joint sample, at the schedule**

`DESIGN-2026-09-15-deformation.md` §0 lists three deformations the `T(K′)` verdict does not
test.  Two are closed: a non-coordinatewise ("row-balanced") cancellation
(`Sched.balanced_union_le`) and a different tensor matrix (`RowVariance.union_le_of_determining`).
The third — *let the atoms read from several sample points instead of one* — was reduced to a
size condition by `RowVariance.grouped_coeff_le` / `grouped_union_le'`, but that condition was
never checked **at the implemented schedule**.  This module checks it, and the answer corrects
the design's prose estimate.

The design (`G4BalancedRigidity`, `Grouped` docstring) read the criterion off
`grouped_union_card_le` as `w ≳ 2 log H / log dmin` — "a vanishing fraction of `H`", so
"the single-`n` sample is *not* essential".  That reading drops the family factor `|𝓕|`, which
at the schedule is `(2 dmax+1)^{2E}` with `E = K(K²+1)^{K−1}`, i.e. **already `dmin^{4E}`**.
Putting it back:

* `grouped_size_cond` — at the schedule the exact size condition of `grouped_coeff_le` holds as
  soon as the smallest group has `w ≥ 8E + 5` atoms, because
  `(2 dmax+1)^{2E} · m · H² · dmax ≤ dmin^{4E+3}` and `w − w/2 ≥ 4E + 3`;
* `grouped_balanced_union_le` — then a family of **grouped** samplers with two row-balanced
  layers reads, below `L`, at most `L / dmin^{w/2} + G · (2 dmax+1)^{2E} · H · m` positions:
  upper density `≤ dmin^{−w/2} ≤ dmin^{−(4E+2)}`;
* `grouped_block_count_le` — groups are disjoint, so `G · w ≤ H`; with `w ≥ 8E + 5` this is
  **`8 K G ≤ K² + 1`**, i.e. at most `(K²+1)/(8K) ≈ K/8` blocks.

So the joint sample *may* be broken up, but into at most about `K/8` blocks (`20000` at
`i = 0`), not into `H/w` blocks with `w` logarithmic.  The confinement rate survives: the
density stays below `dmin^{−(4E+2)}` and `4E + 2 > 10^{1660000}` at `i = 0`.

**Honest residue.**  Below `w = 8E + 5` the *counting* bound is vacuous — not the arithmetic.
Nothing here exhibits a sampler that escapes; what expires is the union bound, at exactly the
point where a block carries fewer atoms than the determining set `skel` needs
(`|skel| ≤ E`, and the threshold is `8E`).  Nothing in this module is a claim about the
normality of `G₄`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Confine NormalNumbers.G4.RowBalance
open NormalNumbers.G4.RowVariance

/-- **The grouped size condition, at the schedule.**  `grouped_coeff_le`'s hypothesis
`|𝓕| m H² dmax ≤ 2 dmin^{w−w/2}` holds for the full row-balanced family as soon as the smallest
group carries `8E + 5` atoms. -/
theorem grouped_size_cond (i : ℕ) {w : ℕ}
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w) :
    (2 * dmax i + 1) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
        * kk i * ((KK i ^ 2 + 1) ^ KK i) ^ 2 * dmax i
      ≤ 2 * dmin i ^ (w - w / 2) := by
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  set D := dmin i with hD
  set Dm := dmax i with hDm
  have h9 : 9 ≤ D := nine_le_dmin i
  have hDm2 : Dm ≤ 2 * D := dmax_le i
  have hkk1 : 1 ≤ kk i := by unfold kk; omega
  have hkey : 8 * (H * kk i) ≤ 2 * D := by
    have := key_size i
    have h8 : (8 : ℕ) ≤ 2 ^ (i + 3) := by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    calc 8 * (H * kk i) ≤ 2 ^ (i + 3) * (H * kk i) := Nat.mul_le_mul_right _ h8
      _ ≤ 2 * D := this
  -- `H ≤ D`, from `8 H m ≤ 2 D` and `m ≥ 1`
  have hHD : H ≤ D := by nlinarith
  -- `2 Dm + 1 ≤ D²`
  have ha : 2 * Dm + 1 ≤ D ^ 2 := by nlinarith
  -- `m H Dm ≤ D²`
  have hb : kk i * H * Dm ≤ D ^ 2 := by nlinarith
  -- the family factor
  have hF : (2 * Dm + 1) ^ (2 * E) ≤ D ^ (4 * E) := by
    calc (2 * Dm + 1) ^ (2 * E) ≤ (D ^ 2) ^ (2 * E) := Nat.pow_le_pow_left ha _
      _ = D ^ (4 * E) := by rw [← pow_mul]; congr 1; ring
  -- the remaining factor
  have hrest : kk i * H ^ 2 * Dm ≤ D ^ 3 := by
    calc kk i * H ^ 2 * Dm = (kk i * H * Dm) * H := by ring
      _ ≤ D ^ 2 * D := Nat.mul_le_mul hb hHD
      _ = D ^ 3 := by ring
  have hprod : (2 * Dm + 1) ^ (2 * E) * kk i * H ^ 2 * Dm ≤ D ^ (4 * E + 3) := by
    calc (2 * Dm + 1) ^ (2 * E) * kk i * H ^ 2 * Dm
        = (2 * Dm + 1) ^ (2 * E) * (kk i * H ^ 2 * Dm) := by ring
      _ ≤ D ^ (4 * E) * D ^ 3 := Nat.mul_le_mul hF hrest
      _ = D ^ (4 * E + 3) := by rw [← pow_add]
  have hexp : 4 * E + 3 ≤ w - w / 2 := by omega
  have hmono : D ^ (4 * E + 3) ≤ D ^ (w - w / 2) := Nat.pow_le_pow_right (by omega) hexp
  omega

/-- **Blocks are big.**  The groups are disjoint and cover the atoms, so `G · w ≤ H`. -/
theorem grouped_block_size (i : ℕ) {G w : ℕ} (grp : (gridAt i).Atom → Fin G)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g}) :
    G * w ≤ (KK i ^ 2 + 1) ^ KK i := by
  classical
  have hcard : (Finset.univ : Finset ((gridAt i).Atom)).card
      = ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (grp x))
  have hsub : ∀ g : Fin G,
      Fintype.card {α : (gridAt i).Atom // grp α = g}
        = (Finset.univ.filter (fun α => grp α = g)).card := by
    intro g; simp [Fintype.card_subtype]
  have hge : ∑ _g : Fin G, w ≤ ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card :=
    Finset.sum_le_sum fun g _ => by rw [← hsub g]; exact hwg g
  have hGw : G * w = ∑ _g : Fin G, w := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hGw]
  calc ∑ _g : Fin G, w ≤ ∑ g : Fin G, (Finset.univ.filter (fun α => grp α = g)).card := hge
    _ = (Finset.univ : Finset ((gridAt i).Atom)).card := hcard.symm
    _ = (KK i ^ 2 + 1) ^ KK i := by rw [Finset.card_univ, card_Atom_gridAt]

/-- **At most `(K²+1)/(8K) ≈ K/8` blocks.**  A grouping whose smallest block meets the size
condition `w ≥ 8E + 5` has `8 K G ≤ K² + 1`. -/
theorem grouped_block_count_le (i : ℕ) {G w : ℕ} (grp : (gridAt i).Atom → Fin G)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g})
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w) :
    8 * KK i * G ≤ KK i ^ 2 + 1 := by
  have hK := KK_ge i
  set E1 := (KK i ^ 2 + 1) ^ (KK i - 1) with hE1
  have hE1pos : 0 < E1 := Nat.one_le_pow _ _ (by positivity)
  have hH : (KK i ^ 2 + 1) ^ KK i = (KK i ^ 2 + 1) * E1 := by
    rw [hE1, ← pow_succ']; congr 1; omega
  have hGw := grouped_block_size i grp hwg
  rw [hH] at hGw
  -- `G * (8 * K * E1) ≤ G * w ≤ (K²+1) * E1`
  have hwE : 8 * (KK i * E1) ≤ w := by omega
  have hstep : G * (8 * (KK i * E1)) ≤ (KK i ^ 2 + 1) * E1 :=
    le_trans (Nat.mul_le_mul_left G hwE) hGw
  have hstep' : (8 * KK i * G) * E1 ≤ (KK i ^ 2 + 1) * E1 := by
    calc (8 * KK i * G) * E1 = G * (8 * (KK i * E1)) := by ring
      _ ≤ (KK i ^ 2 + 1) * E1 := hstep
  exact Nat.le_of_mul_le_mul_right hstep' hE1pos

/-- **The grouped verdict at the schedule.**  A family of samplers of the tensor shape whose
atoms are partitioned into `G` blocks, each block sharing one sample point, each member having
two distinct row-balanced layers, and each block carrying at least `w ≥ 8E + 5` atoms, reads
below `L` at most `L / dmin^{w/2} + G · (2 dmax+1)^{2E} · H · m` positions — upper density
`≤ dmin^{−w/2}`, the same shape as the single-`n` verdict `balanced_union_le`. -/
theorem grouped_balanced_union_le (i : ℕ) {G : ℕ} (grp : (gridAt i).Atom → Fin G)
    {κ : Type*} [DecidableEq κ] (𝓕 : Finset κ)
    (d t : κ → (gridAt i).Atom → ℕ) (P : κ → Fin G → Finset ℕ) {w L : ℕ}
    (hinj : Set.InjOn (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) 𝓕)
    (hbal : ∀ ν ∈ 𝓕, ∃ j j' : ℕ, j ≠ j' ∧
      RowBalance.Balanced (RowBalance.layer j (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))) ∧
      RowBalance.Balanced (RowBalance.layer j' (fun α => (d ν α : ℤ)) (fun α => (t ν α : ℤ))))
    (hd : ∀ ν ∈ 𝓕, ∀ α, dmin i ≤ d ν α ∧ d ν α ≤ dmax i)
    (ht : ∀ ν ∈ 𝓕, ∀ α, t ν α ≤ dmax i)
    (hcop : ∀ ν ∈ 𝓕, ∀ α β, α ≠ β → Nat.Coprime (d ν α) (d ν β))
    (hP : ∀ ν ∈ 𝓕, ∀ g, ∀ n ∈ P ν g, ∀ α, grp α = g → n % d ν α = t ν α)
    (hwg : ∀ g : Fin G, w ≤ Fintype.card {α : (gridAt i).Atom // grp α = g})
    (hGH : G ≤ (KK i ^ 2 + 1) ^ KK i)
    (hw : 8 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)) + 5 ≤ w)
    (U : ℕ → Prop) [DecidablePred U]
    (hcov : ∀ j, j < L → U j → ∃ ν ∈ 𝓕, ∃ g, ∃ n ∈ P ν g, ∃ α, grp α = g ∧ ∃ h < kk i,
      j = 2 * physIdx (d ν α) (t ν α) n + h) :
    (((Finset.range L).filter U).card : ℝ) ≤
      (L : ℝ) / (dmin i : ℝ) ^ (w / 2)
        + (G : ℝ) * (((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * (KK i * (KK i ^ 2 + 1) ^ (KK i - 1)))
            * (((KK i ^ 2 + 1) ^ KK i : ℕ) * kk i)) := by
  classical
  set E := KK i * (KK i ^ 2 + 1) ^ (KK i - 1) with hE
  set H := (KK i ^ 2 + 1) ^ KK i with hH
  -- the family count, exactly as in `balanced_union_le`
  have hcardF : 𝓕.card ≤ (2 * dmax i + 1) ^ (2 * E) := by
    set 𝓕' := 𝓕.image (fun ν => ((fun α => (d ν α : ℤ)), (fun α => (t ν α : ℤ)))) with h𝓕'
    have hc : 𝓕.card = 𝓕'.card := (Finset.card_image_of_injOn hinj).symm
    rw [hc]
    have h1 := card_mdf_pairs_le (K := KK i) (s := KK i ^ 2) (M := dmax i) 𝓕'
      (by
        intro p hp
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨j, j', hne, hj, hj'⟩ := hbal ν hν
        exact mdf_d_t_of_two_balanced_layers hne hj hj')
      (by
        intro p hp α
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        constructor
        · show |((d ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast (hd ν hν α).2
        · show |((t ν α : ℕ) : ℤ)| ≤ (dmax i : ℤ)
          rw [Nat.abs_cast]; exact_mod_cast ht ν hν α)
    refine le_trans h1 (Nat.pow_le_pow_right (by omega) ?_)
    have := card_skel_le (KK i) (KK i ^ 2)
    omega
  -- the size condition
  have hbig : 𝓕.card * kk i * Fintype.card ((gridAt i).Atom) ^ 2 * dmax i
      ≤ 2 * dmin i ^ (w - w / 2) := by
    rw [card_Atom_gridAt]
    refine le_trans ?_ (grouped_size_cond i hw)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ hcardF))
  have hGH' : G ≤ Fintype.card ((gridAt i).Atom) := by rw [card_Atom_gridAt]; exact hGH
  have hbase := grouped_union_le' (ι := (gridAt i).Atom) grp 𝓕 d t P
    (dmin := dmin i) (dmax := dmax i) (m := kk i) (L := L) (w := w)
    (dmin_pos i) hwg hGH' hbig (fun ν hν α => hd ν hν α) hcop hP U hcov
  rw [card_Atom_gridAt, ← hH] at hbase
  refine le_trans hbase (add_le_add le_rfl ?_)
  have hF' : (𝓕.card : ℝ) ≤ ((2 * dmax i + 1 : ℕ) : ℝ) ^ (2 * E) := by exact_mod_cast hcardF
  have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
  have hHm : (0 : ℝ) ≤ ((H : ℕ) : ℝ) * kk i := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF' hHm) hG0

end NormalNumbers.G4.Sched
