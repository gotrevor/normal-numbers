/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropySubsample

/-!
# Objective S, item 3: what a **block** of the joint sample retains

`Sched.grouped_balanced_union_le` lets the single-`n` joint sample be cut into `G` blocks, and
`Sched.grouped_block_count_le` caps `G` at `(K²+1)/(8K) ≈ K/8` — below the corresponding block
size `w = 8E + 5` the *counting* bound goes vacuous.  The directive's item 3 asks whether the
**certificate** side supplies the missing obstruction: is there a smallest block dimension at
which the E0 entropy saving still says anything?

The answer proved here is **no — blocking costs nothing in aggregate, at every block size**:

* `H₂_le_sum_blocks` — cutting the coordinates into blocks and keeping only each block's own
  marginal is subadditive: `H₂(L) ≤ Σ_g H₂(L|block g)`.  (Generalized subadditivity
  `FinLaw.H₂_le_sum_H₂_map` at the family of padded block restrictions, which is injective
  precisely because the blocks partition the coordinates.)
* `H₂_restrictCoords_le` — a block's marginal carries at most `m` bits per coordinate.
* `weight_of_good_blocks` — the pigeonhole those two make available: with per-block caps
  `H_g ≤ m·w_g` and a joint bound `Σ H_g ≥ c·m·Σ w_g`, the blocks that keep a `θ`-fraction of the
  maximal rate carry at least `(c−θ)/(1−θ)` of the total weight.
* `good_block_weight` — the two combined for a `FinLaw` on `A → Fin (2^m)`.

At E0's constant (`entropy_E0`: `(1/5)·m·H < H₂`) and `θ = 1/10` this says: **whatever the block
structure — including blocks of size one — at least a ninth of the atoms lie in blocks whose own
marginal still carries a tenth of the maximal rate.**  So the entropy saving is diluted at worst
proportionally by blocking and never destroyed, and it is *not* the thing that forbids small
blocks.

**Consequence for objective S, recorded honestly.**  Everything that currently forbids blocks
below `w = 8E + 5` is the counting bound, and that bound is essentially tight (lap 164's probe:
the `skel` count is loose only by a constant factor *in the exponent*).  So a sampler with blocks
smaller than `8E + 5` is not excluded by anything proved here — that, and not a certificate-side
dimension threshold, is the honest residue of objective S.  Nothing in this module mentions `G₄`.
-/

open Finset

namespace NormalNumbers.G4Entropy

namespace Blocks

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The coordinates lying in block `g`. -/
def atomsIn {G : ℕ} (grp : A → Fin G) (g : Fin G) : Finset A :=
  Finset.univ.filter (fun α => grp α = g)

lemma mem_atomsIn {G : ℕ} (grp : A → Fin G) (g : Fin G) (α : A) :
    α ∈ atomsIn grp g ↔ grp α = g := by
  simp [atomsIn]

/-- The block sizes sum to the number of coordinates. -/
lemma sum_card_atomsIn {G : ℕ} (grp : A → Fin G) :
    ∑ g : Fin G, (atomsIn grp g).card = Fintype.card A := by
  classical
  simp only [atomsIn]
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := grp) (s := (Finset.univ : Finset A))
    (t := (Finset.univ : Finset (Fin G))) (fun x _ => Finset.mem_univ (grp x))).symm

/-- **Blocking is subadditive.**  Keeping only each block's marginal costs nothing in aggregate.
Injectivity of the padded block restrictions is exactly the statement that the blocks partition
the coordinates. -/
theorem H₂_le_sum_blocks {G : ℕ} (grp : A → Fin G) (m : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) :
    L.H₂ ≤ ∑ g : Fin G, (L.map (FinLaw.restrictCoords (atomsIn grp g) m)).H₂ := by
  classical
  set f : Fin G → (A → Fin (2 ^ m)) → (A → Fin (2 ^ m)) := fun g z =>
    FinLaw.padG (atomsIn grp g) m (FinLaw.restrictCoords (atomsIn grp g) m z) with hf
  have hinj : Function.Injective (fun z : A → Fin (2 ^ m) => fun g => f g z) := by
    intro z z' h
    funext α
    have hα : α ∈ atomsIn grp (grp α) := (mem_atomsIn grp (grp α) α).2 rfl
    have := congrFun (congrFun h (grp α)) α
    simpa [hf, FinLaw.padG, FinLaw.restrictCoords, dif_pos hα] using this
  refine le_trans (L.H₂_le_sum_H₂_map f hinj) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun g _ => ?_
  exact L.H₂_map_congr_comp (FinLaw.restrictCoords (atomsIn grp g) m)
    (FinLaw.padG_injective (atomsIn grp g) m) (f g) (fun z => rfl)

/-- **A block's marginal carries at most `m` bits per coordinate.** -/
theorem H₂_restrictCoords_le (S : Finset A) (m : ℕ) (L : FinLaw (A → Fin (2 ^ m))) :
    (L.map (FinLaw.restrictCoords S m)).H₂ ≤ (S.card : ℝ) * m := by
  classical
  have hcard : Fintype.card (↥S → Fin (2 ^ m)) = 2 ^ (m * S.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, ← pow_mul]
  have hpos : 0 < Fintype.card (↥S → Fin (2 ^ m)) := by
    rw [hcard]; positivity
  refine le_trans ((L.map (FinLaw.restrictCoords S m)).H₂_le_logb_card hpos) (le_of_eq ?_)
  rw [hcard]
  have h2 : (((2 : ℕ) ^ (m * S.card) : ℕ) : ℝ) = (2 : ℝ) ^ (m * S.card) := by push_cast; ring
  have hl : Real.logb 2 (2 : ℝ) = 1 := by simp
  rw [h2, Real.logb_pow, hl]
  push_cast
  ring

/-- **The pigeonhole.**  With per-block caps `H_g ≤ m·w_g` and an aggregate bound
`c·m·Σ w ≤ Σ H`, the blocks keeping a `θ`-fraction of the maximal rate carry at least
`(c−θ)/(1−θ)` of the total weight — stated without division. -/
theorem weight_of_good_blocks {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (wt Hb : ι → ℝ) (m c θ : ℝ)
    (hcap : ∀ g ∈ B, Hb g ≤ m * wt g)
    (hH : c * (m * ∑ g ∈ B, wt g) ≤ ∑ g ∈ B, Hb g) :
    (c - θ) * (m * ∑ g ∈ B, wt g)
      ≤ (1 - θ) * (m * ∑ g ∈ B.filter (fun g => θ * (m * wt g) ≤ Hb g), wt g) := by
  classical
  set P : ι → Prop := fun g => θ * (m * wt g) ≤ Hb g with hP
  set Wg : ℝ := ∑ g ∈ B.filter P, wt g with hWg
  set Wb : ℝ := ∑ g ∈ B.filter (fun g => ¬ P g), wt g with hWb
  set Hg : ℝ := ∑ g ∈ B.filter P, Hb g with hHg
  set Hbb : ℝ := ∑ g ∈ B.filter (fun g => ¬ P g), Hb g with hHbb
  have hHsplit : Hg + Hbb = ∑ g ∈ B, Hb g := Finset.sum_filter_add_sum_filter_not B P Hb
  have hWsplit : Wg + Wb = ∑ g ∈ B, wt g := Finset.sum_filter_add_sum_filter_not B P wt
  have hgood : Hg ≤ m * Wg := by
    rw [hHg, hWg, Finset.mul_sum]
    exact Finset.sum_le_sum fun g hg => hcap g (Finset.mem_filter.1 hg).1
  have hbad : Hbb ≤ θ * (m * Wb) := by
    rw [hHbb, hWb, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun g hg => ?_
    have hg2 := (Finset.mem_filter.1 hg).2
    rw [hP] at hg2
    push_neg at hg2
    linarith
  have hkey : c * (m * (Wg + Wb)) ≤ m * Wg + θ * (m * Wb) := by
    calc c * (m * (Wg + Wb)) = c * (m * ∑ g ∈ B, wt g) := by rw [hWsplit]
      _ ≤ ∑ g ∈ B, Hb g := hH
      _ = Hg + Hbb := hHsplit.symm
      _ ≤ m * Wg + θ * (m * Wb) := add_le_add hgood hbad
  rw [← hWsplit]
  nlinarith [hkey]

/-- **The E0 saving survives blocking, at every block size.**  If the joint law of the
`|A|` windows carries `c·m·|A|` bits, then whatever the block structure, the blocks whose own
marginal still keeps a `θ`-fraction of the maximal rate carry at least `(c−θ)/(1−θ)` of all
coordinates. -/
theorem good_block_weight {G : ℕ} (grp : A → Fin G) (m : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) {c θ : ℝ}
    (hE : c * ((m : ℝ) * (Fintype.card A : ℝ)) ≤ L.H₂) :
    (c - θ) * ((m : ℝ) * (Fintype.card A : ℝ))
      ≤ (1 - θ) * ((m : ℝ) * ∑ g ∈ (Finset.univ : Finset (Fin G)).filter
          (fun g => θ * ((m : ℝ) * ((atomsIn grp g).card : ℝ))
            ≤ (L.map (FinLaw.restrictCoords (atomsIn grp g) m)).H₂),
          ((atomsIn grp g).card : ℝ)) := by
  classical
  set wt : Fin G → ℝ := fun g => ((atomsIn grp g).card : ℝ) with hwt
  set Hb : Fin G → ℝ := fun g => (L.map (FinLaw.restrictCoords (atomsIn grp g) m)).H₂ with hHb
  have hsum : ∑ g : Fin G, wt g = (Fintype.card A : ℝ) := by
    have h := sum_card_atomsIn grp
    simp only [hwt]
    exact_mod_cast h
  have hcap : ∀ g ∈ (Finset.univ : Finset (Fin G)), Hb g ≤ (m : ℝ) * wt g := by
    intro g _
    rw [hHb, hwt, mul_comm]
    exact H₂_restrictCoords_le (atomsIn grp g) m L
  have hH : c * ((m : ℝ) * ∑ g ∈ (Finset.univ : Finset (Fin G)), wt g)
      ≤ ∑ g ∈ (Finset.univ : Finset (Fin G)), Hb g := by
    rw [hsum]
    exact le_trans hE (H₂_le_sum_blocks grp m L)
  have := weight_of_good_blocks (Finset.univ : Finset (Fin G)) wt Hb (m : ℝ) c θ hcap hH
  rw [hsum] at this
  exact this

end Blocks

end NormalNumbers.G4Entropy
