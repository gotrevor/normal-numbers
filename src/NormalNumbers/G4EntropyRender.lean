/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyFreq

/-!
# The faithfulness rendering of the sampled word frequency

`Sched.blockFreq` (`G4EntropyFreq`) is *defined* through `FinLaw.map` and `empirical`, so
`tendsto_blockFreq_primeLambertFour` reads as a frequency statement only after unfolding two
definitions.  The brief (§8) asks the final arithmetic statement to be tested against a
**literal** rendering of the sample law, and that is what this module supplies.

* `blockVal_div_mod` — the window-arithmetic core: the `ℓ` bits of an `(s+ℓ+t)`-window sitting
  `t` bits above its low end are the `ℓ`-window shifted by `s`.
* `blkAt_blockVal_min` — the dictionary for **every** block index, including the last,
  overlapping one: for `ℓ ≤ m`, the `j`-th block coordinate of the `m`-window of `y` at `p` is
  the `ℓ`-window of `y` at `p + min (jℓ) (m − ℓ)`.  (`blkAt_blockVal` covers only `(j+1)ℓ ≤ m`.)
* `blockFreq_eq_count` — `blockFreq` is a ratio of cardinalities: the number of pairs
  `(n, (α, j))` whose block coordinate equals `w`, over `|P_K| · |Atom_K| · (m_K/ℓ + 1)`.
* `blockFreq_eq_digits` — that condition **is** a statement about the binary digits of `x`:
  the `ℓ` digits of `x` at positions `2·kIdx(n,α) + min (jℓ) (m_K − ℓ)` spell `w`.
* `tendsto_wordCount_primeLambertFour` — the headline, restated entirely in terms of digit
  counts of `G₄`, with no `FinLaw` in the statement.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### Window arithmetic, in the form the last block needs -/

/-- **The `ℓ` bits of a window sitting `t` bits above its low end.**  Generalizes the
computation inside `blkAt_blockVal` away from the aligned case. -/
theorem blockVal_div_mod (y : ℝ) (p ℓ s t : ℕ) :
    blockVal y p (s + ℓ + t) / 2 ^ t % 2 ^ ℓ = blockVal y (p + s) ℓ := by
  have hsplit : blockVal y p (s + ℓ + t)
      = blockVal y (p + s + ℓ) t
        + (blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ) * 2 ^ t := by
    rw [show s + ℓ + t = s + (ℓ + t) by omega, blockVal_add y p s (ℓ + t),
      blockVal_add y (p + s) ℓ t, pow_add]
    ring
  have hlowlt : blockVal y (p + s + ℓ) t < 2 ^ t := blockVal_lt _ _ _
  have hdiv : blockVal y p (s + ℓ + t) / 2 ^ t
      = blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ := by
    rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ t),
      Nat.div_eq_of_lt hlowlt]
    omega
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (blockVal_lt _ _ _)]

/-- **The dictionary, for every block index.**  For `ℓ ≤ m` the `j`-th `ℓ`-block coordinate of
the `m`-bit window of `y` at `p` is the `ℓ`-bit window of `y` at `p + min (jℓ) (m − ℓ)`.

For `(j+1)ℓ ≤ m` the minimum is `jℓ` and this is `blkAt_blockVal`; for the final, overlapping
coordinate the block is the low `ℓ` bits, i.e. the window at `p + (m − ℓ)`. -/
theorem blkAt_blockVal_min (y : ℝ) (p m ℓ j : ℕ) (hℓm : ℓ ≤ m) :
    blkAt m ℓ j ⟨blockVal y p m, blockVal_lt y p m⟩
      = ⟨blockVal y (p + min (j * ℓ) (m - ℓ)) ℓ, blockVal_lt y (p + min (j * ℓ) (m - ℓ)) ℓ⟩ := by
  refine Fin.ext ?_
  rw [blkAt_val]
  set t := m - (j + 1) * ℓ with ht
  set s := min (j * ℓ) (m - ℓ) with hs
  have hjl : (j + 1) * ℓ = j * ℓ + ℓ := by ring
  have hm : m = s + ℓ + t := by omega
  show blockVal y p m / 2 ^ t % 2 ^ ℓ = blockVal y (p + s) ℓ
  rw [show blockVal y p m = blockVal y p (s + ℓ + t) by rw [← hm], blockVal_div_mod]

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- The scale-`i` arithmetic-progression sample `P_K` of times. -/
noncomputable def PK (i : ℕ) : Finset ℕ :=
  apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀

lemma PK_nonempty (i : ℕ) : (PK i).Nonempty :=
  apSample_nonempty (gridAt i) (b₀_lt_X_at i)

lemma PK_card_pos (i : ℕ) : 0 < (PK i).card := Finset.card_pos.2 (PK_nonempty i)

/-- The number of block positions inside one window. -/
abbrev rBlocks (i ℓ : ℕ) : ℕ := kk i / ℓ + 1

lemma card_index_pos (i ℓ : ℕ) :
    0 < Fintype.card ((gridAt i).Atom × Fin (rBlocks i ℓ)) := by
  rw [Fintype.card_prod, Fintype.card_fin, card_Atom_gridAt]
  have : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
  positivity

/-! ### `blockFreq` is a ratio of cardinalities -/

open Classical in
/-- **The count rendering.**  `blockFreq` is the density, among the
`|P_K| · |Atom_K| · (m_K/ℓ + 1)` triples `(n, α, j)`, of those whose `j`-th block coordinate of
the window read at `α` equals `w`.  No `FinLaw` left on the right-hand side except the
sampling map `ZVec` itself. -/
theorem blockFreq_eq_count (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    blockFreq i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
            (((PK i).filter fun n =>
              blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (rBlocks i ℓ)) : ℝ)) := by
  classical
  have hScard : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hcard : (0 : ℝ) < (Fintype.card ((gridAt i).Atom × Fin (rBlocks i ℓ)) : ℝ) := by
    exact_mod_cast card_index_pos i ℓ
  have hp : ∀ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
      ((jointLawAt i x).map (blkCoord (kk i) ℓ c)).prob {w}
        = (((PK i).filter fun n =>
              blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro c
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  have hsum : (∑ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
        ((jointLawAt i x).map (blkCoord (kk i) ℓ c)).prob {w})
      = (∑ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
          (((PK i).filter fun n =>
            blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / ((PK i).card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => hp c
  rw [blockFreq, hsum, div_div]

/-! ### The condition is about the binary digits of `x` -/

open Classical in
/-- **The digit rendering.**  The event counted by `blockFreq_eq_count` is exactly: the `ℓ`
binary digits of `x` beginning at position `2·kIdx(n,α) + min (jℓ) (m_K − ℓ)` spell `w`. -/
theorem blockFreq_eq_digits (i ℓ : ℕ) (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    blockFreq i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
            (((PK i).filter fun n =>
              blockVal (Int.fract x)
                  (2 * kIdx (gridAt i) n c.1 + min ((c.2 : ℕ) * ℓ) (kk i - ℓ)) ℓ
                = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (rBlocks i ℓ)) : ℝ)) := by
  classical
  rw [blockFreq_eq_count i ℓ x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n c.1
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1) (kk i),
          blockVal_lt _ _ _⟩ := fun n =>
    Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n c.1)
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, blkAt_blockVal_min _ _ _ _ _ hℓm]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-! ### The headline, with no `FinLaw` in the statement -/

open Classical in
/-- **The frequency theorem for `G₄`, rendered on the digits.**  For every fixed binary word
`w` of length `ℓ`, the proportion of triples `(n, α, j)` — `n` a sample time in `P_K`, `α` a
grid atom, `j` a block position inside the window — for which the `ℓ` binary digits of
`G₄ = ∑_p 1/(4^p − 1)` at positions `2·kIdx(n,α) + min (jℓ) (m_K − ℓ), …` spell `w` tends to
`2^{−ℓ}`.

Every quantity in the statement is a cardinality of an explicitly described finite set of
digit patterns of `G₄`; nothing is hidden inside an entropy or a pushforward law.

**Not** a normality claim: these positions have density zero. -/
theorem tendsto_wordCount_primeLambertFour (ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) :
    Tendsto (fun i =>
      (∑ c : (gridAt i).Atom × Fin (rBlocks i ℓ),
          (((PK i).filter fun n =>
            blockVal (Int.fract (primeLambertAtBase 4))
                (2 * kIdx (gridAt i) n c.1 + min ((c.2 : ℕ) * ℓ) (kk i - ℓ)) ℓ
              = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (rBlocks i ℓ)) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ ℓ)) := by
  have hmain := tendsto_blockFreq_primeLambertFour ℓ hℓ w
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop ℓ] with i hi
  have hℓm : ℓ ≤ kk i := by unfold kk; omega
  exact blockFreq_eq_digits i ℓ hℓm (primeLambertAtBase 4) w

end NormalNumbers.G4.Sched
