/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPosition
import NormalNumbers.G4EntropyConcat

/-!
# Entropy expedition — rendering one scale as one block (rung 2)

Rung 3 (`G4EntropyConcat`) turns a family of finite blocks with converging window frequencies
into one normal real.  This module builds the family out of the base-four schedule: the scale-`i`
block is the concatenation, over all sample times `n ∈ P_i` and all atoms `α`, of the `m_i`-bit
window of `x` at digit position `2·kIdx(n,α)`.

* `nthP`/`nthA` — fixed enumerations of `P_i` and of the atoms (any enumeration works).
* `wpos i w` — the digit position opening the `w`-th window, `w < |P_i|·|Atom_i|`.
* `blen i = |P_i|·|Atom_i|·m_i` and `bdig x i j` — the block's length and digits.
* `goodCount` — the windows of `v` that fit inside a single sampled window; this is *literally*
  the numerator of `tendsto_occursCountP_primeLambertFour`.
* `cyc_bounds` — the cyclic count of the block differs from `goodCount` by at most one `|v|` per
  sampled window, i.e. by a `|v|/m_i` fraction of the block.

Nothing here claims anything about the normality of `G₄`: the digits are `G₄`'s, the number
built from them in rung 3 is not `G₄`.
-/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert
open NormalNumbers.BlockConcat Filter Finset

/-! ### Enumerations -/

lemma atom_card_pos (i : ℕ) : 0 < Fintype.card (gridAt i).Atom := by
  rw [card_Atom_gridAt i]
  positivity

lemma kk_pos (i : ℕ) : 0 < kk i := by unfold kk; omega

/-- The `a`-th sample time at scale `i`, under a fixed enumeration of `P_i`. -/
noncomputable def nthP (i a : ℕ) : ℕ :=
  ((PK i).equivFin.symm ⟨a % (PK i).card, Nat.mod_lt _ (PK_card_pos i)⟩ : ℕ)

/-- The `e`-th atom at scale `i`, under a fixed enumeration. -/
noncomputable def nthA (i e : ℕ) : (gridAt i).Atom :=
  (Fintype.equivFin (gridAt i).Atom).symm
    ⟨e % Fintype.card (gridAt i).Atom, Nat.mod_lt _ (atom_card_pos i)⟩

lemma sum_range_nthP {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (PK i).card, g (nthP i a) = ∑ n ∈ PK i, g n := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (nthP i a))]
  have hstep : ∀ a : Fin (PK i).card,
      g (nthP i (a : ℕ)) = g (((PK i).equivFin.symm a : ℕ)) := by
    intro a
    have hfin : (⟨(a : ℕ) % (PK i).card, Nat.mod_lt _ (PK_card_pos i)⟩ : Fin (PK i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [nthP, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [Equiv.sum_comp (PK i).equivFin.symm (fun x : (PK i : Finset ℕ) => g (x : ℕ))]
  exact Finset.sum_coe_sort (PK i) g

lemma sum_range_nthA {β : Type*} [AddCommMonoid β] (i : ℕ) (g : (gridAt i).Atom → β) :
    ∑ e ∈ Finset.range (Fintype.card (gridAt i).Atom), g (nthA i e) = ∑ α, g α := by
  rw [← Fin.sum_univ_eq_sum_range (fun e => g (nthA i e))]
  have hstep : ∀ e : Fin (Fintype.card (gridAt i).Atom),
      g (nthA i (e : ℕ)) = g ((Fintype.equivFin (gridAt i).Atom).symm e) := by
    intro e
    have hfin : (⟨(e : ℕ) % Fintype.card (gridAt i).Atom,
        Nat.mod_lt _ (atom_card_pos i)⟩ : Fin (Fintype.card (gridAt i).Atom)) = e := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt e.isLt
    rw [nthA, hfin]
  rw [Finset.sum_congr rfl fun e _ => hstep e]
  exact Equiv.sum_comp (Fintype.equivFin (gridAt i).Atom).symm g

/-! ### The block -/

/-- The number of sampled windows at scale `i`. -/
noncomputable def nwin (i : ℕ) : ℕ := (PK i).card * Fintype.card (gridAt i).Atom

lemma nwin_pos (i : ℕ) : 0 < nwin i := Nat.mul_pos (PK_card_pos i) (atom_card_pos i)

/-- The digit position opening the `w`-th sampled window. -/
noncomputable def wpos (i w : ℕ) : ℕ :=
  2 * kIdx (gridAt i) (nthP i (w / Fintype.card (gridAt i).Atom))
      (nthA i (w % Fintype.card (gridAt i).Atom))

lemma wpos_mk (i a e : ℕ) (he : e < Fintype.card (gridAt i).Atom) :
    wpos i (a * Fintype.card (gridAt i).Atom + e)
      = 2 * kIdx (gridAt i) (nthP i a) (nthA i e) := by
  have hA := atom_card_pos i
  have hcomm : a * Fintype.card (gridAt i).Atom + e
      = Fintype.card (gridAt i).Atom * a + e := by ring
  rw [wpos, hcomm, Nat.mul_add_div hA, Nat.div_eq_of_lt he, Nat.mul_add_mod,
    Nat.mod_eq_of_lt he]
  simp

/-- The length of the scale-`i` block. -/
noncomputable def blen (i : ℕ) : ℕ := nwin i * kk i

lemma blen_pos (i : ℕ) : 0 < blen i := Nat.mul_pos (nwin_pos i) (kk_pos i)

/-- The `j`-th digit of the scale-`i` block of `x`: `G₄`'s digit at the `j`-th sampled position. -/
noncomputable def samplePosIn (i j : ℕ) : ℕ := wpos i (j / kk i) + j % kk i

/-- The block's digits. -/
noncomputable def bdig (x : ℝ) (i j : ℕ) : ℕ := digitOf 2 (Int.fract x) (samplePosIn i j)

lemma bdig_lt (x : ℝ) (i j : ℕ) : bdig x i j < 2 := Nat.mod_lt _ (by omega)

end NormalNumbers.G4.Sched
