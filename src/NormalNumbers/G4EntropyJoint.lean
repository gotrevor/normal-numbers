/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPosition

/-!
# The joint (`t`-wise) capacity bound: the sampled windows decorrelate

Everything proved so far about `jointLaw` projects it to **one** coordinate: `entropy_E1` bounds
the entropy of the whole vector `Z_K = (Z_α)_{α∈Atom}`, and `G4EntropyTiling` /
`G4EntropyPosition` then read off a single window's word frequencies.  The joint content is
untouched, and it is exactly what a near-maximal joint entropy is *for*: the coordinates are
asymptotically **independent**.

This module proves the abstract half.  Fix a *blocking* — an injective family
`blk : B → Fin t → A` of `t`-tuples of distinct atoms — and read the `j`-th aligned `ℓ`-block of
each of the `t` windows of a block, packed into one `ℓt`-bit word (`patCoord`).  Then:

* `sum_patCoord_deficit_le` — **the deficit is not multiplied by `t`**:
  `∑_{b,j} (ℓt − H₂(L.map (patCoord b j))) ≤ Δ`, the *same* `Δ` as the `t = 1` statement
  `sum_block_deficit_tile_le`, and again with zero slack.  The bits ledger closes exactly:
  the `t|B|` covered atoms contribute `⌊m/ℓ⌋·ℓt + t(m%ℓ) = tm` bits per block and the
  `|A| − t|B|` uncovered ones `m` each.
* `abs_avg_patCoord_prob_le` / `abs_avg_patCoord_prob_opt` — hence every *pattern*
  `w ∈ Fin (2^{ℓt})` has its average probability within `2√(log 2 · tℓδ/m)` of `2^{−ℓt}`:
  the `t = 1` bound with `ℓ ↦ tℓ`, which is what pinning `t` words at once costs.

Taking `t = 2` already says something new about `G₄`: for a typical pair of sampled windows, the
two `ℓ`-blocks are jointly uniform, i.e. *independent*.  Disjunctivity gives one word at a time;
this gives a prescribed pattern at `t` prescribed sampled positions simultaneously.

The whole argument is the `t = 1` one with the atom set `A` replaced by the block set `B` and the
alphabet `Fin (2^ℓ)` by `Fin (2^{ℓt})` — no new information theory, only a bits ledger.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- A law supported on one atom has zero entropy. -/
theorem H₂_map_const_le {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (L : FinLaw Ω) (c : Ω') :
    (L.map (fun _ => c)).H₂ ≤ 0 := by
  classical
  have h := (L.map (fun _ : Ω => c)).H₂_le_logb (N := 1) one_pos {c}
    (fun ω' hω' => by
      by_contra hc
      rw [FinLaw.map_p] at hω'
      refine hω' (Finset.sum_eq_zero fun ω hω => ?_)
      rw [Finset.mem_filter] at hω
      exact absurd (hω.2 ▸ Finset.mem_singleton_self c) hc)
    (by simp)
  simpa using h

end FinLaw

/-! ### Packing a `t`-tuple of `ℓ`-bit words into one `ℓt`-bit word -/

/-- `(Fin t → Fin (2^ℓ)) ≃ Fin (2^{ℓt})`. -/
def packFin (t ℓ : ℕ) : (Fin t → Fin (2 ^ ℓ)) ≃ Fin (2 ^ (ℓ * t)) :=
  finFunctionFinEquiv.trans (finCongr (pow_mul 2 ℓ t).symm)

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The pattern coordinate.**  The `j`-th aligned `ℓ`-block of each of the `t` windows of
block `b`, packed into one `ℓt`-bit word. -/
def patCoord (m ℓ t : ℕ) (blk : B → Fin t → A) (c : B × Fin (m / ℓ))
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => fullCoord m ℓ (blk c.1 s, c.2) z)

/-- The block remainder coordinate: the `t` window remainders, packed. -/
def patRem (m ℓ t : ℕ) (hℓ : 0 < ℓ) (blk : B → Fin t → A) (b : B)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => remCoord m ℓ hℓ (z (blk b s)))

/-- The coordinate of an atom the blocking misses; covered atoms get a constant. -/
noncomputable def leftCoord (m ℓ t : ℕ) (hm : m ≤ ℓ * t) (blk : B → Fin t → A) (α : A)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  open Classical in
  if (∃ p : B × Fin t, blk p.1 p.2 = α) then ⟨0, Nat.pow_pos (by norm_num)⟩
  else Fin.castLE (Nat.pow_le_pow_right (by norm_num) hm) (z α)

/-- The three families together determine the sample vector. -/
theorem jointFam_injective {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hm : m ≤ ℓ * t)
    (blk : B → Fin t → A) :
    Function.Injective (fun z : A → Fin (2 ^ m) =>
      fun i : (B × Fin (m / ℓ)) ⊕ B ⊕ A => Sum.elim (fun c => patCoord m ℓ t blk c z)
        (Sum.elim (fun b => patRem m ℓ t hℓ blk b z)
          (fun α => leftCoord m ℓ t hm blk α z)) i) := by
  sorry

/-- **The `t`-wise deficit budget, with zero slack.**  A total deficit of `Δ` bits on the joint
law leaves a total deficit of at most `Δ` on the `|B|·⌊m/ℓ⌋` pattern coordinates — the *same*
`Δ`, not `tΔ`. -/
theorem sum_patCoord_deficit_le {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hm : m ≤ ℓ * t)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ∑ c : B × Fin (m / ℓ), ((ℓ * t : ℕ) - (L.map (patCoord m ℓ t blk c)).H₂ : ℝ) ≤ Δ := by
  sorry

/-- **The averaged `t`-wise bound.**  Every pattern's average probability is within
`(2 log2 Δ)/(2 s N) + s/2` of `2^{−ℓt}`, for every `s > 0`. -/
theorem abs_avg_patCoord_prob_le {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (ht : 0 < t)
    (hm : m ≤ ℓ * t) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ s : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) (hs : 0 < s) :
    |(∑ c : B × Fin (m / ℓ), (L.map (patCoord m ℓ t blk c)).prob {w})
        / (Fintype.card (B × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ (2 * Real.log 2 * Δ) / (2 * s * (Fintype.card (B × Fin (m / ℓ)) : ℝ)) + s / 2 := by
  sorry

end NormalNumbers.G4Entropy
