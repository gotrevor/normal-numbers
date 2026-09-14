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

/-! ### The word-list rendering: the counted event is `OccursAt`

`blockVal … = (w : ℕ)` still encodes the word as a *number*.  Here it is turned into the
literal digit predicate `OccursAt 2 x w` — the very predicate `isDisjunctive_two` uses — so the
comparison between this theorem and disjunctivity is mechanical rather than interpretive.
-/

namespace NormalNumbers.G4Entropy

/-- The value of a finite binary word, most significant digit first. -/
def seqVal (d : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, d i * 2 ^ (m - 1 - i)

lemma seqVal_succ (d : ℕ → ℕ) (m : ℕ) : seqVal d (m + 1) = 2 * seqVal d m + d m := by
  unfold seqVal
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  have he : m - i = (m - 1 - i) + 1 := by omega
  rw [he, pow_succ]
  ring

lemma blockVal_eq_seqVal (y : ℝ) (p m : ℕ) :
    blockVal y p m = seqVal (fun i => digitOf 2 y (p + i)) m := rfl

/-- A binary word of length `m` has value `< 2^m`. -/
lemma seqVal_lt {d : ℕ → ℕ} : ∀ {m : ℕ}, (∀ i < m, d i < 2) → seqVal d m < 2 ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [seqVal]
  | succ m ih =>
    intro h
    have hb := ih fun i hi => h i (by omega)
    have hd := h m (by omega)
    rw [seqVal_succ, pow_succ]
    omega

/-- **Uniqueness of the binary encoding.**  Two binary digit strings of the same length with
the same value agree digit by digit. -/
lemma seqVal_inj {d e : ℕ → ℕ} : ∀ {m : ℕ}, (∀ i < m, d i < 2) → (∀ i < m, e i < 2) →
    seqVal d m = seqVal e m → ∀ i < m, d i = e i := by
  intro m
  induction m with
  | zero => intro _ _ _ i hi; omega
  | succ m ih =>
    intro hd he h i hi
    rw [seqVal_succ, seqVal_succ] at h
    have hdm := hd m (by omega)
    have hem := he m (by omega)
    have hb : seqVal d m = seqVal e m := by omega
    have hlast : d m = e m := by omega
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact ih (fun j hj => hd j (by omega)) (fun j hj => he j (by omega)) hb i hlt
    · have : i = m := by omega
      subst this; exact hlast

/-- The numeric value of a word given as a list. -/
def wordVal (w : List ℕ) : ℕ := seqVal (fun i => w.getD i 0) w.length

lemma wordVal_lt {w : List ℕ} (hw : ∀ i, ∀ h : i < w.length, w[i] < 2) :
    wordVal w < 2 ^ w.length := by
  refine seqVal_lt fun i hi => ?_
  rw [List.getD_eq_getElem w 0 hi]
  exact hw i hi

/-- **The word-list dictionary.**  The length-`|w|` binary window of `y` at `p` has value
`wordVal w` exactly when the word `w` occurs at position `p`. -/
theorem blockVal_eq_wordVal_iff {y : ℝ} {p : ℕ} {w : List ℕ}
    (hw : ∀ i, ∀ h : i < w.length, w[i] < 2) :
    blockVal (Int.fract y) p w.length = wordVal w ↔ OccursAt 2 y w p := by
  have hdig : ∀ i, digitOf 2 (Int.fract y) (p + i) < 2 := fun i => Nat.mod_lt _ (by omega)
  constructor
  · intro h j hj
    have hkey := seqVal_inj (d := fun i => digitOf 2 (Int.fract y) (p + i))
      (e := fun i => w.getD i 0)
      (m := w.length) (fun i _ => hdig i)
      (fun i hi => by rw [List.getD_eq_getElem w 0 hi]; exact hw i hi)
      (by rw [← blockVal_eq_seqVal]; exact h) j hj
    rw [hkey, List.getD_eq_getElem w 0 hj]
  · intro h
    rw [blockVal_eq_seqVal, wordVal]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < w.length := Finset.mem_range.1 hi
    simp only
    rw [h i hi', List.getD_eq_getElem w 0 hi']

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

open Classical in
/-- **The headline over `OccursAt`.**  For every finite binary word `w`, the proportion of
triples `(n, α, j)` at which `w` **occurs** in the binary expansion of `G₄` — at digit position
`2·kIdx(n,α) + min (j|w|) (m_K − |w|)` — tends to `2^{−|w|}`.

`OccursAt 2 · w ·` is exactly the predicate behind `isDisjunctive_two`, so the comparison is
now mechanical: disjunctivity gives *some* occurrence, this gives the *correct frequency* of
occurrences on the sampled system.  It is still **not** a normality statement — the positions
counted here have density zero. -/
theorem tendsto_occursCount_primeLambertFour (w : List ℕ) (hlen : 0 < w.length)
    (hw : ∀ i, ∀ h : i < w.length, w[i] < 2) :
    Tendsto (fun i =>
      (∑ c : (gridAt i).Atom × Fin (rBlocks i w.length),
          (((PK i).filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) w
              (2 * kIdx (gridAt i) n c.1
                + min ((c.2 : ℕ) * w.length) (kk i - w.length))).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (rBlocks i w.length)) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ w.length)) := by
  classical
  have hmain := tendsto_wordCount_primeLambertFour w.length hlen ⟨wordVal w, wordVal_lt hw⟩
  refine hmain.congr fun i => ?_
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hw

end NormalNumbers.G4.Sched

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The quantitative edge: how fast may the word length grow?

`abs_blockFreq_sub_le` carries a free parameter `t`; optimizing it turns the bound into a
single closed form, and that form says exactly how long a word the sample controls.  With
`m_K/ℓ + 1 ≥ K/(4ℓ)` the bound is

    `|blockFreq − 2^{−ℓ}| ≤ √(8 log 2 · (ℓ²/K + 50ℓ/√K))`,

so the frequency statement survives **every** word length `ℓ = ℓ(K) = o(√K)`, uniformly in the
word.  This is the route-trigger E-T5 quantity, recorded rather than hidden: the sample sees
words of length up to `o(√K)` out of the `m_K = K/4` bits of a window.
-/

lemma rBlocks_lb (i ℓ : ℕ) (hℓ : 0 < ℓ) :
    (KK i : ℝ) / (4 * (ℓ : ℝ)) ≤ (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hnat : kk i < (kk i / ℓ + 1) * ℓ := by
    have h1 := Nat.div_add_mod (kk i) ℓ
    have h2 : kk i % ℓ < ℓ := Nat.mod_lt _ hℓ
    have h3 : (kk i / ℓ + 1) * ℓ = ℓ * (kk i / ℓ) + ℓ := by ring
    omega
  have hR : (kk i : ℝ) < (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) * (ℓ : ℝ) := by exact_mod_cast hnat
  have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
  rw [hkk4, div_le_iff₀ (by positivity)]
  linarith

/-- **The optimized bound.**  Choosing `t` optimally in `abs_blockFreq_sub_le`:

    `|blockFreq i ℓ G₄ w − 2^{−ℓ}| ≤ √(8 log 2 · (ℓ²/K + 50ℓ/√K))`,

uniformly in the word `w`. -/
theorem abs_blockFreq_sub_le_sqrt (i ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) :
    |blockFreq i ℓ (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ Real.sqrt (8 * Real.log 2
          * ((ℓ : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ : ℝ) / Real.sqrt (KK i))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  set S : ℝ := Real.sqrt ((KK i : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 hKpos
  have hKS : (KK i : ℝ) = S * S := (Real.mul_self_sqrt hKpos.le).symm
  set A : ℝ := 4 * Real.log 2 * (ℓ : ℝ) * ((ℓ : ℝ) + 50 * S) / (KK i : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set t : ℝ := Real.sqrt (2 * A) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t * t = 2 * A := Real.mul_self_sqrt (by linarith)
  have h1 := abs_blockFreq_sub_le i ℓ hℓ w ht
  rw [← hSdef] at h1
  -- the `t`-term
  have hnum : (0 : ℝ) ≤ Real.log 2 * ((ℓ : ℝ) + 50 * S) := by nlinarith
  have hDpos : (0 : ℝ) < (KK i : ℝ) / (4 * (ℓ : ℝ)) := by positivity
  have hstep : Real.log 2 * ((ℓ : ℝ) + 50 * S) / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))
      ≤ A / t := by
    have hmono : t * ((KK i : ℝ) / (4 * (ℓ : ℝ))) ≤ t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (rBlocks_lb i ℓ hℓ) ht.le
    calc Real.log 2 * ((ℓ : ℝ) + 50 * S) / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))
        ≤ Real.log 2 * ((ℓ : ℝ) + 50 * S) / (t * ((KK i : ℝ) / (4 * (ℓ : ℝ)))) :=
          div_le_div_of_nonneg_left hnum (by positivity) hmono
      _ = A / t := by rw [hA]; field_simp
  have hopt : A / t + t / 2 = t := by
    have hA2 : A = t * t / 2 := by linarith [ht2]
    rw [hA2]
    field_simp
    norm_num
  have harg : 8 * Real.log 2 * ((ℓ : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ : ℝ) / S) = 2 * A := by
    rw [hA]
    rw [show ((ℓ : ℝ) ^ 2 / (KK i : ℝ)) = (ℓ : ℝ) ^ 2 / (S * S) by rw [← hKS]]
    field_simp
    nlinarith [hKS, hS0]
  have hval : t = Real.sqrt (8 * Real.log 2
      * ((ℓ : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ : ℝ) / S)) := by
    rw [harg, htdef]
  have hfin : |blockFreq i ℓ (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ ℓ| ≤ t := by
    linarith [h1, hstep, hopt]
  rw [← hval]
  exact hfin

/-- **The frequency theorem with a growing word length.**  Any word length `ℓ(K) = o(√K)` —
the words themselves may change with `K` — still has its frequency pinned at `2^{−ℓ}`.

This is the sharp form of what the entropy of this sample controls: words up to length
`o(√K)` inside windows of length `m_K = K/4`. -/
theorem tendsto_blockFreq_growing (ℓ : ℕ → ℕ) (hpos : ∀ i, 0 < ℓ i)
    (hgrow : Tendsto (fun i => (ℓ i : ℝ) / Real.sqrt (KK i)) atTop (nhds 0))
    (w : ∀ i, Fin (2 ^ ℓ i)) :
    Tendsto (fun i => blockFreq i (ℓ i) (primeLambertAtBase 4) (w i) - 1 / (2 : ℝ) ^ (ℓ i))
      atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : ∀ i, (0 : ℝ) < (KK i : ℝ) := fun i => by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hratio : ∀ i, (ℓ i : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ i : ℝ) / Real.sqrt (KK i)
      = ((ℓ i : ℝ) / Real.sqrt (KK i)) ^ 2 + 50 * ((ℓ i : ℝ) / Real.sqrt (KK i)) := by
    intro i
    set S : ℝ := Real.sqrt ((KK i : ℕ) : ℝ) with hSdef
    have hS0 : 0 < S := Real.sqrt_pos.2 (hKpos i)
    have hKS : (KK i : ℝ) = S * S := (Real.mul_self_sqrt (hKpos i).le).symm
    rw [hKS]
    field_simp
  have hinner : Tendsto (fun i => 8 * Real.log 2
      * ((ℓ i : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ i : ℝ) / Real.sqrt (KK i))) atTop (nhds 0) := by
    have h := ((hgrow.pow 2).add (hgrow.const_mul 50)).const_mul (8 * Real.log 2)
    simp only [mul_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h
    refine h.congr fun i => ?_
    rw [hratio i]
  have hsq : Tendsto (fun i => Real.sqrt (8 * Real.log 2
      * ((ℓ i : ℝ) ^ 2 / (KK i : ℝ) + 50 * (ℓ i : ℝ) / Real.sqrt (KK i)))) atTop (nhds 0) := by
    simpa using hinner.sqrt
  refine squeeze_zero_norm (fun i => ?_) hsq
  simpa [Real.norm_eq_abs] using abs_blockFreq_sub_le_sqrt i (ℓ i) (hpos i) (w i)

end NormalNumbers.G4.Sched

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The general-`x` form: `E0` alone forces the sampled word frequencies

`abs_avg_block_prob_sub_le` is abstract; only the *supply* of the entropy deficit was
`G₄`-specific (`entropy_E1`).  Feeding it the deficit that the hypothesis `E0 x` provides —
`Δ_i = (1 − H₂/maxH)·m_K·H_K` — gives the frequency theorem for **every** `x` with an
asymptotically maximal sample entropy.  `G₄` is then one instance, via `E0_primeLambertFour`.
-/

/-- The relative entropy deficit of `x` at scale `i`. -/
noncomputable def defRatio (i : ℕ) (x : ℝ) : ℝ := 1 - (jointLawAt i x).H₂ / maxH i

lemma defRatio_nonneg (i : ℕ) (x : ℝ) : 0 ≤ defRatio i x := by
  have := ratio_le_one i x
  unfold defRatio
  linarith

/-- **The quantitative bound from the deficit alone.**  For every `t > 0`,

    `|blockFreq i ℓ x w − 2^{−ℓ}| ≤ log 2·ℓ/(t·(m_K/ℓ+1)) + log 2·ℓ·defRatio/t + t/2`. -/
theorem abs_blockFreq_sub_le_defRatio (i ℓ : ℕ) (hℓ : 0 < ℓ) (x : ℝ) (w : Fin (2 ^ ℓ))
    {t : ℝ} (ht : 0 < t) :
    |blockFreq i ℓ x w - 1 / (2 : ℝ) ^ ℓ|
      ≤ Real.log 2 * (ℓ : ℝ) / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))
        + Real.log 2 * (ℓ : ℝ) * defRatio i x / t + t / 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  set C : ℝ := (Fintype.card (gridAt i).Atom : ℝ) with hC
  have hC0 : 0 < C := by
    rw [hC, card_Atom_gridAt]
    have : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
    exact_mod_cast this
  set D : ℝ := (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hmax : maxH i = (kk i : ℝ) * C := by
    rw [maxH, hC, card_Atom_gridAt]
  set Δ : ℝ := (kk i : ℝ) * C - (jointLawAt i x).H₂ with hΔdef
  have hΔ : (kk i : ℝ) * C - Δ ≤ (jointLawAt i x).H₂ := by rw [hΔdef]; linarith
  have hmain := abs_avg_block_prob_sub_le (A := (gridAt i).Atom) (m := kk i) (ℓ := ℓ)
    hℓ (jointLawAt i x) w hΔ ht
  have hprod : (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ + 1)) : ℝ) = C * D := by
    rw [Fintype.card_prod, hC, hD]
    push_cast
    simp
  rw [hprod] at hmain
  have hbf : blockFreq i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (kk i / ℓ + 1),
          ((jointLawAt i x).map (blkCoord (kk i) ℓ c)).prob {w}) / (C * D) := by
    rw [blockFreq, hprod]
  rw [hbf]
  refine hmain.trans ?_
  -- rewrite the deficit through `defRatio` and bound `m/D` by `ℓ`
  have hk0 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hΔeq : Δ = defRatio i x * ((kk i : ℝ) * C) := by
    have hne : ((kk i : ℝ) * C) ≠ 0 := by positivity
    rw [defRatio, hmax, sub_mul, one_mul, div_mul_cancel₀ _ hne, hΔdef]
  have hmD : (kk i : ℝ) ≤ (ℓ : ℝ) * D := by
    have hnat : kk i < (kk i / ℓ + 1) * ℓ := by
      have h1 := Nat.div_add_mod (kk i) ℓ
      have h2 : kk i % ℓ < ℓ := Nat.mod_lt _ hℓ
      have h3 : (kk i / ℓ + 1) * ℓ = ℓ * (kk i / ℓ) + ℓ := by ring
      omega
    have : (kk i : ℝ) < D * (ℓ : ℝ) := by rw [hD]; exact_mod_cast hnat
    linarith
  have hsplit : 2 * Real.log 2 * (C * (ℓ : ℝ) + Δ) / (2 * t * (C * D))
      = Real.log 2 * (ℓ : ℝ) / (t * D) + Real.log 2 * Δ / (t * C * D) := by
    field_simp
  rw [hsplit]
  have hterm : Real.log 2 * Δ / (t * C * D) ≤ Real.log 2 * (ℓ : ℝ) * defRatio i x / t := by
    rw [hΔeq]
    rw [div_le_div_iff₀ (by positivity) ht]
    have hd0 := defRatio_nonneg i x
    have hsub : (0 : ℝ) ≤ (ℓ : ℝ) * D - (kk i : ℝ) := by linarith
    have key : (0 : ℝ) ≤ (Real.log 2 * defRatio i x * C * t) * ((ℓ : ℝ) * D - (kk i : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hlog2.le hd0) hC0.le) ht.le) hsub
    nlinarith [key]
  linarith

/-- **The frequency theorem for every `x` with maximal sample entropy.**  `E0 x` alone — the
sample entropy being asymptotically maximal — pins every fixed word's frequency among the
`ℓ`-aligned blocks of the sampled windows.  `G₄` is the instance supplied by
`E0_primeLambertFour`. -/
theorem tendsto_blockFreq_of_E0 {x : ℝ} (hx : E0 x) (ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) :
    Tendsto (fun i => blockFreq i ℓ x w) atTop (nhds (1 / (2 : ℝ) ^ ℓ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  rw [Metric.tendsto_atTop]
  intro η hη
  -- the two vanishing terms, at `t = η`
  have hDtop : Tendsto (fun i => η * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hη ?_
    refine tendsto_atTop_mono (fun i => rBlocks_lb i ℓ hℓ) ?_
    exact tendsto_KK_atTop.atTop_div_const (by positivity)
  have h1 : Tendsto (fun i => Real.log 2 * (ℓ : ℝ)
      / (η * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))) atTop (nhds 0) := hDtop.const_div_atTop _
  have h2 : Tendsto (fun i => Real.log 2 * (ℓ : ℝ) * defRatio i x / η) atTop (nhds 0) := by
    have hd : Tendsto (fun i => defRatio i x) atTop (nhds 0) := by
      unfold defRatio
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hx
    simpa using ((hd.const_mul (Real.log 2 * (ℓ : ℝ))).div_const η)
  have hsum := h1.add h2
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨N, hN⟩ := hsum (η / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  have hb := abs_blockFreq_sub_le_defRatio i ℓ hℓ x w hη
  have hs := hN i hi
  simp only [Real.dist_eq, add_zero, sub_zero] at hs
  have hs' := lt_of_abs_lt hs
  rw [Real.dist_eq]
  linarith

/-- `G₄` as an instance: the sampled word frequencies follow from `E0` alone. -/
theorem tendsto_blockFreq_primeLambertFour' (ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) :
    Tendsto (fun i => blockFreq i ℓ (primeLambertAtBase 4) w) atTop
      (nhds (1 / (2 : ℝ) ^ ℓ)) :=
  tendsto_blockFreq_of_E0 E0_primeLambertFour ℓ hℓ w

/-! ### The capacity of the sample: deficit against controllable word length

Laps 26–27 gave two special cases of one inequality.  Here it is in general: an entropy
deficit of `δ` bits per window (`H₂ ≥ (m_K − δ)·H_K`) controls every word of length `ℓ` to
within

    `√(2 log 2 · ℓ(ℓ + δ)/m_K)`.

Two regimes: with `δ ≤ ℓ` the cost is the *sampling* cost `√(ℓ²/m_K)`, and with `δ ≥ ℓ` the
*deficit* cost `√(ℓδ/m_K)`.  So improving `entropy_E1`'s deficit from `50√K` to `δ(K)` would
extend the controlled word length from `o(√K)` to `o(min(√m_K, m_K/δ))` — the `√K` ceiling of
lap 26 is exactly the point where the two regimes cross, **not** an artifact of the averaging.
-/

/-- **The capacity inequality.**  `δ` bits of entropy deficit per window control every word of
length `ℓ` to within `√(2 log 2 · ℓ(ℓ+δ)/m_K)`, uniformly in the word and in `x`. -/
theorem abs_blockFreq_sub_le_of_deficit (i ℓ : ℕ) (hℓ : 0 < ℓ) (x : ℝ) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |blockFreq i ℓ x w - 1 / (2 : ℝ) ^ ℓ|
      ≤ Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * ((ℓ : ℝ) + δ) / (kk i : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hk0 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hC0 : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    rw [card_Atom_gridAt]
    have : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
    exact_mod_cast this
  set D : ℝ := (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hmD : (kk i : ℝ) < (ℓ : ℝ) * D := by
    have hnat : kk i < (kk i / ℓ + 1) * ℓ := by
      have h1 := Nat.div_add_mod (kk i) ℓ
      have h2 : kk i % ℓ < ℓ := Nat.mod_lt _ hℓ
      have h3 : (kk i / ℓ + 1) * ℓ = ℓ * (kk i / ℓ) + ℓ := by ring
      omega
    have : (kk i : ℝ) < D * (ℓ : ℝ) := by rw [hD]; exact_mod_cast hnat
    linarith
  -- the deficit ratio
  have hratio : defRatio i x ≤ δ / (kk i : ℝ) := by
    have hmax : maxH i = (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
      rw [maxH, card_Atom_gridAt]
    have hkey : 1 - δ / (kk i : ℝ)
        ≤ (jointLawAt i x).H₂ / ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hexp : (1 - δ / (kk i : ℝ)) * ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ))
          = ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) := by
        field_simp
      rw [hexp]
      exact hdef
    rw [defRatio, hmax]
    linarith
  -- the optimized parameter
  set A : ℝ := Real.log 2 * (ℓ : ℝ) * ((ℓ : ℝ) + δ) / (kk i : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set t : ℝ := Real.sqrt (2 * A) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t * t = 2 * A := Real.mul_self_sqrt (by linarith)
  have hb := abs_blockFreq_sub_le_defRatio i ℓ hℓ x w ht
  rw [← hD] at hb
  -- both error terms against `A / t`
  have hterm1 : Real.log 2 * (ℓ : ℝ) / (t * D) ≤ Real.log 2 * (ℓ : ℝ) * (ℓ : ℝ)
      / ((kk i : ℝ) * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key1 : (0 : ℝ) ≤ (Real.log 2 * (ℓ : ℝ) * t) * ((ℓ : ℝ) * D - (kk i : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [key1]
  have hterm2 : Real.log 2 * (ℓ : ℝ) * defRatio i x / t
      ≤ Real.log 2 * (ℓ : ℝ) * δ / ((kk i : ℝ) * t) := by
    rw [div_le_div_iff₀ ht (by positivity)]
    have hmr : (kk i : ℝ) * defRatio i x ≤ δ := by
      have := mul_le_mul_of_nonneg_left hratio hk0.le
      rwa [mul_div_cancel₀ _ hk0.ne'] at this
    have key2 : (0 : ℝ) ≤ (Real.log 2 * (ℓ : ℝ) * t) * (δ - (kk i : ℝ) * defRatio i x) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [key2]
  have hsum : Real.log 2 * (ℓ : ℝ) * (ℓ : ℝ) / ((kk i : ℝ) * t)
      + Real.log 2 * (ℓ : ℝ) * δ / ((kk i : ℝ) * t) = A / t := by
    rw [hA]
    field_simp
  have hopt : A / t + t / 2 = t := by
    have hA2 : A = t * t / 2 := by linarith [ht2]
    rw [hA2]
    field_simp
    norm_num
  have hfin : |blockFreq i ℓ x w - 1 / (2 : ℝ) ^ ℓ| ≤ t := by linarith
  have hval : t = Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * ((ℓ : ℝ) + δ) / (kk i : ℝ)) := by
    rw [htdef, hA]
    congr 1
    field_simp
  rw [← hval]
  exact hfin

/-- **The capacity limit.**  Along any family of scales, word lengths `ℓ(K)` and deficits
`δ(K)` with `ℓ(ℓ+δ)/m_K → 0` have their word frequencies pinned — the words and the reals may
both vary with the scale. -/
theorem tendsto_blockFreq_of_capacity (x : ℕ → ℝ) (ℓ : ℕ → ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ i, 0 < ℓ i) (hδ : ∀ i, 0 ≤ δ i)
    (hdef : ∀ i, ((kk i : ℝ) - δ i) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (x i)).H₂)
    (hcap : Tendsto (fun i => (ℓ i : ℝ) * ((ℓ i : ℝ) + δ i) / (kk i : ℝ)) atTop (nhds 0))
    (w : ∀ i, Fin (2 ^ ℓ i)) :
    Tendsto (fun i => blockFreq i (ℓ i) (x i) (w i) - 1 / (2 : ℝ) ^ (ℓ i)) atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Tendsto (fun i => 2 * Real.log 2 * (ℓ i : ℝ) * ((ℓ i : ℝ) + δ i) / (kk i : ℝ))
      atTop (nhds 0) := by
    have h := hcap.const_mul (2 * Real.log 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    ring
  have hsq : Tendsto (fun i => Real.sqrt (2 * Real.log 2 * (ℓ i : ℝ) * ((ℓ i : ℝ) + δ i)
      / (kk i : ℝ))) atTop (nhds 0) := by simpa using hinner.sqrt
  refine squeeze_zero_norm (fun i => ?_) hsq
  simpa [Real.norm_eq_abs] using
    abs_blockFreq_sub_le_of_deficit i (ℓ i) (hpos i) (x i) (w i) (hδ i) (hdef i)

end NormalNumbers.G4.Sched
