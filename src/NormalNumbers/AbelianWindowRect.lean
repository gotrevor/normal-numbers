/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowGf
import NormalNumbers.PowerBaseReal

/-!
# The rectangle design: a block law with ONE excluded window length

See `DESIGN-2026-09-25-c4-rectangle.md`.  For `a ≥ 2` put `q = a + 2` and let the block law be the
pushforward of the uniform law on `2 ^ q` digits under the map that exchanges bits `a` and `a+1`
exactly when

    bit 0 ≠ bit 1  ∧  bit a = 1 − bit 0  ∧  bit (a+1) = bit 0.

The exchange preserves the one-count of the pair `{a, a+1}`, so every window segment containing
both or neither of `a, a+1` keeps its Binomial one-count; the segments containing exactly one of
them are handled by an explicit two-term cancellation, which fails for exactly one segment,
`[1, a+1)`.  Hence the block sequence is abelian at every window length except `a`.

This file builds the bit-level tools; the Fourier-free computation is a product over the `q` bit
positions, via `sum_prod_wordOf`.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-- Bit `i` of the `q`-bit word with numeric value `k` (most significant bit first). -/
def bitw (q k i : ℕ) : ℕ := (wordOf 2 q k).getD i 0

theorem bitw_lt_two (q k i : ℕ) : bitw q k i < 2 := by
  by_cases h : i < (wordOf 2 q k).length
  · rw [bitw, List.getD_eq_getElem _ _ h]
    exact wordOf_lt 2 q k (by norm_num) _ (List.getElem_mem h)
  · rw [bitw, List.getD_eq_default _ _ (by omega)]
    norm_num

/-- **The bit-level factorization.**  A sum over all `q`-bit words of a product of per-position
functions of that position's bit is the product of the per-position two-term sums. -/
theorem sum_prod_bits {R : Type*} [CommRing R] (q : ℕ) (F : ℕ → ℕ → R) :
    ∑ k ∈ range (2 ^ q), ∏ i ∈ range q, F i (bitw q k i)
      = ∏ i ∈ range q, (F i 0 + F i 1) := by
  have h := sum_prod_wordOf (R := R) 2 (by norm_num) F q
  refine h.trans (Finset.prod_congr rfl (fun i _ => ?_))
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-! ## The design -/

section Rect

variable (a : ℕ)

/-- The four coupled bit positions. -/
def spos : Finset ℕ := {0, 1, a, a + 1}

/-- The exchange is triggered when bits `0,1` differ and `(bit a, bit (a+1)) = (1 - bit 0, bit 0)`. -/
def rectP (d : ℕ) : Prop :=
  bitw (a + 2) d 0 ≠ bitw (a + 2) d 1 ∧ bitw (a + 2) d a = bitw (a + 2) d 1 ∧
    bitw (a + 2) d (a + 1) = bitw (a + 2) d 0

instance (d : ℕ) : Decidable (rectP a d) := by unfold rectP; infer_instance

/-- **The block table.**  Bit `r` of the digit `d`, with bits `a` and `a+1` exchanged when
`rectP` fires. -/
def rectG (r d : ℕ) : ℕ :=
  if rectP a d then
    (if r = a then bitw (a + 2) d (a + 1) else
      if r = a + 1 then bitw (a + 2) d a else bitw (a + 2) d r)
  else bitw (a + 2) d r

/-- A one-count over a segment, as a sum of bits. -/
theorem card_filter_eq_sum (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) (ob : ℕ → ℕ)
    (hob : ∀ u, ob u < 2) :
    (I.filter (fun u => ob u = 1)).card = ∑ i ∈ range q, (if i ∈ I then ob i else 0) := by
  classical
  have h1 : ∑ i ∈ range q, (if i ∈ I then ob i else 0) = ∑ i ∈ I, ob i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hI h, h⟩⟩
  rw [h1, Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := hob i
  interval_cases h : ob i <;> simp

/-- The generating-function summand as a product over bit positions. -/
theorem pow_card_filter (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) (ob : ℕ → ℕ)
    (hob : ∀ u, ob u < 2) :
    (X : ℝ[X]) ^ ((I.filter (fun u => ob u = 1)).card)
      = ∏ i ∈ range q, X ^ (if i ∈ I then ob i else 0) := by
  rw [Finset.prod_pow_eq_pow_sum, card_filter_eq_sum q I hI ob hob]

/-! ### The two forced patterns -/

/-- The forced bit values on `spos a` that trigger the exchange, indexed by `ε = bit 0`. -/
def vv (ε i : ℕ) : ℕ := if i = 0 then ε else if i = 1 then 1 - ε else if i = a then 1 - ε else ε

/-- The corresponding OUTPUT bit values after the exchange. -/
def ww (ε i : ℕ) : ℕ := if i = 0 then ε else if i = 1 then 1 - ε else if i = a then ε else 1 - ε

/-- The per-position factor: on the four coupled positions the bit is forced to `v i` and the
exponent uses the output value `o i`; elsewhere the bit is free. -/
noncomputable def rfac (I : Finset ℕ) (v o : ℕ → ℕ) (i b : ℕ) : ℝ[X] :=
  if i ∈ spos a then (if b = v i then X ^ (if i ∈ I then o i else 0) else 0)
  else X ^ (if i ∈ I then b else 0)

theorem spos_subset (ha : 2 ≤ a) : spos a ⊆ range (a + 2) := by
  intro i hi
  simp only [spos, Finset.mem_insert, Finset.mem_singleton] at hi
  rw [Finset.mem_range]
  rcases hi with rfl | rfl | rfl | rfl <;> omega

theorem rfac_sum (I : Finset ℕ) (v o : ℕ → ℕ) (hv : ∀ i, v i < 2) (i : ℕ) :
    rfac a I v o i 0 + rfac a I v o i 1
      = if i ∈ spos a then (X : ℝ[X]) ^ (if i ∈ I then o i else 0)
        else (if i ∈ I then 1 + X else 2) := by
  classical
  unfold rfac
  by_cases hs : i ∈ spos a
  · simp only [hs, if_true]
    have := hv i
    interval_cases h : v i <;> simp
  · simp only [hs, if_false]
    by_cases hI : i ∈ I <;> simp [hI]
    norm_num

/-- The forced sum, evaluated. -/
theorem rect_sum_forced (ha : 2 ≤ a) (I : Finset ℕ) (v o : ℕ → ℕ) (hv : ∀ i, v i < 2) :
    ∑ d ∈ range (2 ^ (a + 2)), ∏ i ∈ range (a + 2), rfac a I v o i (bitw (a + 2) d i)
      = (∏ i ∈ spos a, (X : ℝ[X]) ^ (if i ∈ I then o i else 0))
        * ∏ i ∈ (range (a + 2)) \ spos a, (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  classical
  rw [sum_prod_bits (a + 2) (fun i b => rfac a I v o i b),
    Finset.prod_congr rfl (fun i _ => rfac_sum a I v o hv i),
    ← Finset.prod_sdiff (spos_subset a ha), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl (fun i hi => by rw [if_pos hi])
  · exact Finset.prod_congr rfl (fun i hi => by
      rw [if_neg (Finset.mem_sdiff.mp hi).2])

theorem mem_spos {i : ℕ} : i ∈ spos a ↔ i = 0 ∨ i = 1 ∨ i = a ∨ i = a + 1 := by
  simp [spos]

/-- Under `rectP`, the four coupled bits are exactly the pattern `vv ε` and the table outputs
exactly `ww ε`. -/
theorem rect_pattern (ha : 2 ≤ a) (d : ℕ) (hP : rectP a d) {ε : ℕ} (h0 : bitw (a + 2) d 0 = ε) :
    (∀ i ∈ spos a, bitw (a + 2) d i = vv a ε i) ∧
      (∀ i, rectG a i d = if i ∈ spos a then ww a ε i else bitw (a + 2) d i) := by
  obtain ⟨hne, hA, hB⟩ := hP
  have hb0 := bitw_lt_two (a + 2) d 0
  have hb1 := bitw_lt_two (a + 2) d 1
  have h1 : bitw (a + 2) d 1 = 1 - ε := by omega
  constructor
  · intro i hi
    rw [mem_spos] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa [vv] using h0
    · simpa [vv, (by omega : ¬ (1 : ℕ) = 0)] using h1
    · rw [vv, if_neg (by omega), if_neg (by omega), if_pos rfl, hA, h1]
    · rw [vv, if_neg (by omega), if_neg (by omega), if_neg (by omega), hB, h0]
  · intro i
    by_cases hi : i ∈ spos a
    · rw [if_pos hi, rectG, if_pos ⟨hne, hA, hB⟩]
      rw [mem_spos] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · rw [if_neg (by omega), if_neg (by omega), ww, if_pos rfl, h0]
      · rw [if_neg (by omega), if_neg (by omega), ww, if_neg (by omega), if_pos rfl, h1]
      · rw [if_pos rfl, ww, if_neg (by omega), if_neg (by omega), if_pos rfl, hB, h0]
      · rw [if_neg (by omega), if_pos rfl, ww, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), hA, h1]
    · rw [if_neg hi, rectG, if_pos ⟨hne, hA, hB⟩]
      rw [mem_spos] at hi
      push_neg at hi
      obtain ⟨-, -, h3, h4⟩ := hi
      rw [if_neg h3, if_neg h4]

/-- Off `rectP`, no forced pattern can be matched. -/
theorem rect_not_pattern (ha : 2 ≤ a) (d : ℕ) (hP : ¬ rectP a d) {ε : ℕ} (hε : ε < 2) :
    ∃ i ∈ spos a, bitw (a + 2) d i ≠ vv a ε i := by
  by_contra hcon
  push_neg at hcon
  have e0 : bitw (a + 2) d 0 = ε := by
    simpa [vv] using hcon 0 (mem_spos a |>.mpr (Or.inl rfl))
  have e1 : bitw (a + 2) d 1 = 1 - ε := by
    simpa [vv, (by omega : ¬ (1 : ℕ) = 0)] using hcon 1 (mem_spos a |>.mpr (Or.inr (Or.inl rfl)))
  have e2 : bitw (a + 2) d a = 1 - ε := by
    have := hcon a (mem_spos a |>.mpr (Or.inr (Or.inr (Or.inl rfl))))
    rwa [vv, if_neg (by omega), if_neg (by omega), if_pos rfl] at this
  have e3 : bitw (a + 2) d (a + 1) = ε := by
    have := hcon (a + 1) (mem_spos a |>.mpr (Or.inr (Or.inr (Or.inr rfl))))
    rwa [vv, if_neg (by omega), if_neg (by omega), if_neg (by omega)] at this
  exact hP ⟨by omega, by omega, by omega⟩

/-- A matched forced product collapses to the plain product with the output bits substituted on
the four coupled positions. -/
theorem rfac_prod_matched (I : Finset ℕ) (v o : ℕ → ℕ) (d : ℕ)
    (hm : ∀ i ∈ spos a, bitw (a + 2) d i = v i) :
    ∏ i ∈ range (a + 2), rfac a I v o i (bitw (a + 2) d i)
      = ∏ i ∈ range (a + 2), (X : ℝ[X]) ^
          (if i ∈ I then (if i ∈ spos a then o i else bitw (a + 2) d i) else 0) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hs : i ∈ spos a
  · rw [rfac, if_pos hs, if_pos (hm i hs)]
    by_cases hI : i ∈ I <;> simp [hI, hs]
  · rw [rfac, if_neg hs]
    by_cases hI : i ∈ I <;> simp [hI, hs]

/-- An unmatched forced product vanishes. -/
theorem rfac_prod_unmatched (ha : 2 ≤ a) (I : Finset ℕ) (v o : ℕ → ℕ) (d : ℕ)
    (hm : ∃ i ∈ spos a, bitw (a + 2) d i ≠ v i) :
    ∏ i ∈ range (a + 2), rfac a I v o i (bitw (a + 2) d i) = 0 := by
  obtain ⟨i, hi, hne⟩ := hm
  refine Finset.prod_eq_zero (spos_subset a ha hi) ?_
  rw [rfac, if_pos hi, if_neg hne]

/-- **The pointwise identity.**  The table's window monomial is the plain one plus the two
forced corrections. -/
theorem rect_key (ha : 2 ≤ a) (I : Finset ℕ) (d : ℕ) :
    ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then rectG a i d else 0)
      = ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then bitw (a + 2) d i else 0)
        + ((∏ i ∈ range (a + 2), rfac a I (vv a 0) (ww a 0) i (bitw (a + 2) d i))
           - ∏ i ∈ range (a + 2), rfac a I (vv a 0) (vv a 0) i (bitw (a + 2) d i))
        + ((∏ i ∈ range (a + 2), rfac a I (vv a 1) (ww a 1) i (bitw (a + 2) d i))
           - ∏ i ∈ range (a + 2), rfac a I (vv a 1) (vv a 1) i (bitw (a + 2) d i)) := by
  classical
  by_cases hP : rectP a d
  · obtain ⟨hm, hout⟩ := rect_pattern a ha d hP (ε := bitw (a + 2) d 0) rfl
    have hb0 := bitw_lt_two (a + 2) d 0
    have hkey : ∀ ε : ℕ, (∀ i ∈ spos a, bitw (a + 2) d i = vv a ε i) →
        (∏ i ∈ range (a + 2), rfac a I (vv a ε) (ww a ε) i (bitw (a + 2) d i)
            = ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then rectG a i d else 0)) ∧
          (∏ i ∈ range (a + 2), rfac a I (vv a ε) (vv a ε) i (bitw (a + 2) d i)
            = ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then bitw (a + 2) d i else 0)) := by
      intro ε hmε
      have h0 : bitw (a + 2) d 0 = ε := by
        simpa [vv] using hmε 0 (mem_spos a |>.mpr (Or.inl rfl))
      obtain ⟨-, houtε⟩ := rect_pattern a ha d hP (ε := ε) h0
      refine ⟨?_, ?_⟩
      · rw [rfac_prod_matched a I _ _ d hmε]
        exact Finset.prod_congr rfl (fun i _ => by rw [houtε i])
      · rw [rfac_prod_matched a I _ _ d hmε]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        by_cases hs : i ∈ spos a
        · rw [if_pos hs, hmε i hs]
        · rw [if_neg hs]
    have hzero : ∀ ε : ℕ, ε < 2 → bitw (a + 2) d 0 ≠ ε →
        ∀ o : ℕ → ℕ, ∏ i ∈ range (a + 2), rfac a I (vv a ε) o i (bitw (a + 2) d i) = 0 := by
      intro ε hε hne o
      refine rfac_prod_unmatched a ha I _ o d ⟨0, mem_spos a |>.mpr (Or.inl rfl), ?_⟩
      simpa [vv] using hne
    rcases (by omega : bitw (a + 2) d 0 = 0 ∨ bitw (a + 2) d 0 = 1) with h | h
    · obtain ⟨e1, e2⟩ := hkey 0 (by rw [← h]; exact hm)
      rw [e1, e2, hzero 1 (by norm_num) (by omega) _, hzero 1 (by norm_num) (by omega) _]
      ring
    · obtain ⟨e1, e2⟩ := hkey 1 (by rw [← h]; exact hm)
      rw [e1, e2, hzero 0 (by norm_num) (by omega) _, hzero 0 (by norm_num) (by omega) _]
      ring
  · have hg : ∀ i, rectG a i d = bitw (a + 2) d i := fun i => by rw [rectG, if_neg hP]
    have hz : ∀ ε : ℕ, ε < 2 → ∀ o : ℕ → ℕ,
        ∏ i ∈ range (a + 2), rfac a I (vv a ε) o i (bitw (a + 2) d i) = 0 := by
      intro ε hε o
      exact rfac_prod_unmatched a ha I _ o d (rect_not_pattern a ha d hP hε)
    rw [hz 0 (by norm_num), hz 0 (by norm_num), hz 1 (by norm_num), hz 1 (by norm_num)]
    rw [Finset.prod_congr rfl (fun i _ => by rw [hg i] :
      ∀ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then rectG a i d else 0)
        = (X : ℝ[X]) ^ (if i ∈ I then bitw (a + 2) d i else 0))]
    ring

theorem rectG_lt_two (r d : ℕ) : rectG a r d < 2 := by
  rw [rectG]
  split
  · split
    · exact bitw_lt_two _ _ _
    · split <;> exact bitw_lt_two _ _ _
  · exact bitw_lt_two _ _ _

theorem prod_spos (ha : 2 ≤ a) (f : ℕ → ℝ[X]) :
    ∏ i ∈ spos a, f i = f 0 * (f 1 * (f a * f (a + 1))) := by
  rw [spos, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]

/-- The plain-bit window generating function. -/
theorem rect_sum_plain (I : Finset ℕ) :
    ∑ d ∈ range (2 ^ (a + 2)),
        ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then bitw (a + 2) d i else 0)
      = ∏ i ∈ range (a + 2), (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  rw [sum_prod_bits (a + 2) (fun i b => (X : ℝ[X]) ^ (if i ∈ I then b else 0))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hI : i ∈ I <;> simp [hI] <;> norm_num

/-- **The segment generating function of the rectangle design.**  The correction factors as a
product of two differences, one for the pair `{a, a+1}` and one for the pair `{0,1}`; it vanishes
unless the segment contains exactly one of each pair. -/
theorem vv_lt_two {ε : ℕ} (hε : ε < 2) (i : ℕ) : vv a ε i < 2 := by
  rw [vv]
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem rect_segGf (ha : 2 ≤ a) (I : Finset ℕ) (hI : I ⊆ range (a + 2)) :
    ∑ d ∈ range (2 ^ (a + 2)), (X : ℝ[X]) ^ ((I.filter (fun u => rectG a u d = 1)).card)
      = (∏ i ∈ range (a + 2), (if i ∈ I then (1 + X : ℝ[X]) else 2))
        + (∏ i ∈ (range (a + 2)) \ spos a, (if i ∈ I then (1 + X : ℝ[X]) else 2))
          * ((X ^ (if a ∈ I then 1 else 0) - X ^ (if a + 1 ∈ I then 1 else 0))
             * (X ^ (if 0 ∈ I then 1 else 0) - X ^ (if (1 : ℕ) ∈ I then 1 else 0))) := by
  classical
  have hpow : ∀ d, (X : ℝ[X]) ^ ((I.filter (fun u => rectG a u d = 1)).card)
      = ∏ i ∈ range (a + 2), (X : ℝ[X]) ^ (if i ∈ I then rectG a i d else 0) :=
    fun d => pow_card_filter (a + 2) I hI (fun u => rectG a u d) (fun u => rectG_lt_two a u d)
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ range (2 ^ (a + 2))) => (hpow d).trans
      (rect_key a ha I d)),
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, rect_sum_plain a I,
    rect_sum_forced a ha I _ _ (vv_lt_two a (by norm_num)),
    rect_sum_forced a ha I _ _ (vv_lt_two a (by norm_num)),
    rect_sum_forced a ha I _ _ (vv_lt_two a (by norm_num)),
    rect_sum_forced a ha I _ _ (vv_lt_two a (by norm_num))]
  have hv00 : vv a 0 0 = 0 := by simp [vv]
  have hv01 : vv a 0 1 = 1 := by simp [vv]
  have hv0a : vv a 0 a = 1 := by rw [vv, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hv0b : vv a 0 (a + 1) = 0 := by
    rw [vv, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hw00 : ww a 0 0 = 0 := by simp [ww]
  have hw01 : ww a 0 1 = 1 := by simp [ww]
  have hw0a : ww a 0 a = 0 := by rw [ww, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hw0b : ww a 0 (a + 1) = 1 := by
    rw [ww, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hv10 : vv a 1 0 = 1 := by simp [vv]
  have hv11 : vv a 1 1 = 0 := by simp [vv]
  have hv1a : vv a 1 a = 0 := by rw [vv, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hv1b : vv a 1 (a + 1) = 1 := by
    rw [vv, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hw10 : ww a 1 0 = 1 := by simp [ww]
  have hw11 : ww a 1 1 = 0 := by simp [ww]
  have hw1a : ww a 1 a = 1 := by rw [ww, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hw1b : ww a 1 (a + 1) = 0 := by
    rw [ww, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [prod_spos a ha, prod_spos a ha, prod_spos a ha, prod_spos a ha,
    hv00, hv01, hv0a, hv0b, hw00, hw01, hw0a, hw0b,
    hv10, hv11, hv1a, hv1b, hw10, hw11, hw1a, hw1b]
  simp only [ite_self, pow_zero, one_mul, mul_one]
  ring

/-- The base term is the exact Binomial generating function. -/
theorem rect_base_eq (I : Finset ℕ) (hI : I ⊆ range (a + 2)) :
    (∏ i ∈ range (a + 2), (if i ∈ I then (1 + X : ℝ[X]) else 2))
      = C ((2 : ℝ) ^ (a + 2) / 2 ^ I.card) * (1 + X) ^ I.card := by
  classical
  rw [← Finset.prod_sdiff hI]
  have h1 : ∏ i ∈ I, (if i ∈ I then (1 + X : ℝ[X]) else 2) = (1 + X) ^ I.card := by
    rw [Finset.prod_congr rfl (fun i hi => if_pos hi), Finset.prod_const]
  have h2 : ∏ i ∈ (range (a + 2)) \ I, (if i ∈ I then (1 + X : ℝ[X]) else 2)
      = 2 ^ ((range (a + 2)) \ I).card := by
    rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2), Finset.prod_const]
  have hcard : ((range (a + 2)) \ I).card = (a + 2) - I.card := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hI]
  have hle : I.card ≤ a + 2 := by
    simpa using Finset.card_le_card hI
  rw [h1, h2, hcard]
  have hsplit : ((2 : ℝ) ^ (a + 2) / 2 ^ I.card) = 2 ^ ((a + 2) - I.card) := by
    rw [div_eq_iff (by positivity), ← pow_add]
    congr 1
    omega
  rw [hsplit, Polynomial.C_pow, Polynomial.C_ofNat]

/-- **Every prefix and every suffix of the rectangle block law is Binomial.** -/
theorem rect_binomSeg (ha : 2 ≤ a) : BinomSeg (rectG a) (a + 2) (2 ^ (a + 2)) := by
  classical
  intro lo hi hhi hps
  have hI : Finset.Ico lo hi ⊆ range (a + 2) := by
    intro i hi'
    rw [Finset.mem_Ico] at hi'
    rw [Finset.mem_range]
    omega
  have hzero : ((X : ℝ[X]) ^ (if a ∈ Finset.Ico lo hi then 1 else 0)
      - X ^ (if a + 1 ∈ Finset.Ico lo hi then 1 else 0))
      * (X ^ (if 0 ∈ Finset.Ico lo hi then 1 else 0)
        - X ^ (if (1 : ℕ) ∈ Finset.Ico lo hi then 1 else 0)) = 0 := by
    simp only [Finset.mem_Ico]
    rcases hps with rfl | rfl
    · by_cases h1 : hi ≤ 1
      · have ha1 : ¬ (0 ≤ a ∧ a < hi) := by omega
        have ha2 : ¬ (0 ≤ a + 1 ∧ a + 1 < hi) := by omega
        rw [if_neg ha1, if_neg ha2, sub_self, zero_mul]
      · have hb1 : (0 ≤ 0 ∧ 0 < hi) := by omega
        have hb2 : (0 ≤ 1 ∧ (1 : ℕ) < hi) := by omega
        rw [if_pos hb1, if_pos hb2, sub_self, mul_zero]
    · by_cases h1 : lo ≤ a
      · have ha1 : (lo ≤ a ∧ a < a + 2) := by omega
        have ha2 : (lo ≤ a + 1 ∧ a + 1 < a + 2) := by omega
        rw [if_pos ha1, if_pos ha2, sub_self, zero_mul]
      · have hb1 : ¬ (lo ≤ 0 ∧ (0 : ℕ) < a + 2) := by omega
        have hb2 : ¬ (lo ≤ 1 ∧ (1 : ℕ) < a + 2) := by omega
        rw [if_neg hb1, if_neg hb2, sub_self, mul_zero]
  rw [rect_segGf a ha _ hI, hzero, mul_zero, add_zero, rect_base_eq a _ hI,
    Nat.card_Ico]
  norm_num

/-- **The rectangle sequence is abelian at every window length `L ≥ a + 2`.** -/
theorem rect_isAbelianAt_ge (ha : 2 ≤ a) (c : ℕ → ℕ) (hcB : ∀ m, c m < 2 ^ (a + 2))
    (hc : IsNormalSequence (2 ^ (a + 2)) c) (L : ℕ) (hL : a + 2 ≤ L) :
    IsAbelianAt (blockSeq (rectG a) c (a + 2)) L :=
  isAbelianAt_blockSeq_of_binomSeg (rectG a) c (by positivity) (by omega) hcB hc
    (rect_binomSeg a ha) L hL

/-! ### Which segments a window actually makes -/

theorem segSet_eq_Ico_gen (q L r b : ℕ) :
    segSet q L r b = Finset.Ico (r - b * q) (min q (r + L - b * q)) := by
  ext u
  simp only [segSet, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]
  omega

/-- The correction of `rect_segGf` vanishes on every segment except `Ico 1 (a+1)`. -/
theorem rect_corr_eq_zero (ha : 2 ≤ a) (lo hi : ℕ) (hhi : hi ≤ a + 2)
    (hne : ¬ (lo = 1 ∧ hi = a + 1)) :
    ((X : ℝ[X]) ^ (if a ∈ Finset.Ico lo hi then 1 else 0)
        - X ^ (if a + 1 ∈ Finset.Ico lo hi then 1 else 0))
      * (X ^ (if 0 ∈ Finset.Ico lo hi then 1 else 0)
        - X ^ (if (1 : ℕ) ∈ Finset.Ico lo hi then 1 else 0)) = 0 := by
  simp only [Finset.mem_Ico]
  have key : ((lo ≤ a ∧ a < hi) ↔ (lo ≤ a + 1 ∧ a + 1 < hi)) ∨
      ((lo ≤ 0 ∧ 0 < hi) ↔ (lo ≤ 1 ∧ (1 : ℕ) < hi)) := by omega
  rcases key with k | k
  · by_cases hc : lo ≤ a ∧ a < hi
    · rw [if_pos hc, if_pos (k.mp hc), sub_self, zero_mul]
    · rw [if_neg hc, if_neg (fun h => hc (k.mpr h)), sub_self, zero_mul]
  · by_cases hc : lo ≤ 0 ∧ 0 < hi
    · rw [if_pos hc, if_pos (k.mp hc), sub_self, mul_zero]
    · rw [if_neg hc, if_neg (fun h => hc (k.mpr h)), sub_self, mul_zero]

/-- **The rectangle sequence is abelian at every window length except `a`.** -/
theorem rect_isAbelianAt_of_ne (ha : 2 ≤ a) (c : ℕ → ℕ) (hcB : ∀ m, c m < 2 ^ (a + 2))
    (hc : IsNormalSequence (2 ^ (a + 2)) c) (L : ℕ) (hne : L ≠ a) :
    IsAbelianAt (blockSeq (rectG a) c (a + 2)) L := by
  classical
  set q := a + 2 with hq
  set S := q + L with hSdef
  have hq0 : 0 < q := by omega
  have hB0 : 0 < 2 ^ q := by positivity
  have hSle : q + L ≤ q * S + 1 := by
    have : S ≤ q * S := Nat.le_mul_of_pos_left S hq0
    omega
  have hfib : ∀ r < q, ∀ t < L, (r + t) / q < S := by
    intro r hr t ht
    have := Nat.div_le_self (r + t) q
    omega
  refine (isAbelianAt_blockSeq_iff (rectG a) c hB0 hq0 hcB hc L S hSle).mpr (fun j _ => ?_)
  refine blockFreq_eq_binomial_of_seg (rectG a) hB0 hq0 S L hfib (fun r hr b hb => ?_) j
  have hsub : segSet q L r b ⊆ range q := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have hshape := segSet_eq_Ico_gen q L r b
  have hnotdef : ¬ (r - b * q = 1 ∧ min q (r + L - b * q) = a + 1) := by
    rcases Nat.eq_zero_or_pos b with rfl | hb1
    · simp only [Nat.zero_mul, Nat.sub_zero]
      omega
    · have hbq : q ≤ b * q := Nat.le_mul_of_pos_left q hb1
      omega
  have hcard : segLen q L r b = (segSet q L r b).card := segLen_eq_card q L r b hq0
  have hgf : ∀ d, segOnes (rectG a) q L r b d
      = ((segSet q L r b).filter (fun u => rectG a u d = 1)).card :=
    fun d => segOnes_eq_card (rectG a) hq0 L r b d
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ range (2 ^ q)) => by rw [hgf d]),
    hshape, rect_segGf a ha _ (by rw [← hshape]; exact hsub),
    rect_corr_eq_zero a ha _ _ (min_le_left _ _) hnotdef, mul_zero, add_zero,
    rect_base_eq a _ (by rw [← hshape]; exact hsub), hcard, hshape]
  push_cast
  rfl

/-- The segment generating function in `blockFreq` coordinates. -/
theorem rect_segOnes_gf (ha : 2 ≤ a) (L r b : ℕ) :
    (∑ d ∈ range (2 ^ (a + 2)), (X : ℝ[X]) ^ segOnes (rectG a) (a + 2) L r b d)
      = C ((2 : ℝ) ^ (a + 2) / 2 ^ (segLen (a + 2) L r b)) * (1 + X) ^ (segLen (a + 2) L r b)
        + (∏ i ∈ (range (a + 2)) \ spos a,
            (if i ∈ segSet (a + 2) L r b then (1 + X : ℝ[X]) else 2))
          * ((X ^ (if a ∈ segSet (a + 2) L r b then 1 else 0)
              - X ^ (if a + 1 ∈ segSet (a + 2) L r b then 1 else 0))
             * (X ^ (if 0 ∈ segSet (a + 2) L r b then 1 else 0)
               - X ^ (if (1 : ℕ) ∈ segSet (a + 2) L r b then 1 else 0))) := by
  classical
  have hq0 : 0 < a + 2 := by omega
  have hsub : segSet (a + 2) L r b ⊆ range (a + 2) := fun u hu => (Finset.mem_filter.mp hu).1
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ range (2 ^ (a + 2))) => by
      rw [segOnes_eq_card (rectG a) hq0 L r b d]),
    rect_segGf a ha _ hsub, rect_base_eq a _ hsub, ← segLen_eq_card (a + 2) L r b hq0]

/-! ### The defective length -/

theorem segSet_one_zero (ha : 2 ≤ a) : segSet (a + 2) a 1 0 = Finset.Ico 1 (a + 1) := by
  rw [segSet_eq_Ico_gen]
  simp only [Nat.zero_mul, Nat.sub_zero]
  congr 1
  omega

theorem segSet_one_pos (b : ℕ) (hb : 1 ≤ b) : segSet (a + 2) a 1 b = ∅ := by
  rw [segSet_eq_Ico_gen]
  have hbq : a + 2 ≤ b * (a + 2) := Nat.le_mul_of_pos_left (a + 2) (by omega)
  have h1 : 1 - b * (a + 2) = 0 := by omega
  have h2 : min (a + 2) (1 + a - b * (a + 2)) = 0 := by omega
  rw [h1, h2]
  rfl

theorem sdiff_spos (ha : 2 ≤ a) : (range (a + 2)) \ spos a = Finset.Ico 2 a := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_range, mem_spos, Finset.mem_Ico]
  omega

theorem rect_defect_factor (ha : 2 ≤ a) :
    (∑ d ∈ range (2 ^ (a + 2)), (X : ℝ[X]) ^ segOnes (rectG a) (a + 2) a 1 0 d)
      = C ((2 : ℝ) ^ (a + 2) / 2 ^ a) * (1 + X) ^ a + (1 + X) ^ (a - 2) * ((X - 1) * (1 - X)) := by
  classical
  have hq0 : 0 < a + 2 := by omega
  have hset := segSet_one_zero a ha
  have hlen : segLen (a + 2) a 1 0 = a := by
    rw [segLen_eq_card _ _ _ _ hq0, hset, Nat.card_Ico]
    omega
  have hcf : (∏ i ∈ (range (a + 2)) \ spos a,
      (if i ∈ segSet (a + 2) a 1 0 then (1 + X : ℝ[X]) else 2)) = (1 + X) ^ (a - 2) := by
    rw [sdiff_spos a ha, hset,
      Finset.prod_congr rfl (fun i hi => if_pos (by
        rw [Finset.mem_Ico] at hi ⊢; omega)), Finset.prod_const, Nat.card_Ico]
  rw [rect_segOnes_gf a ha, hlen, hcf, hset]
  congr 2
  rw [if_pos (by rw [Finset.mem_Ico]; omega), if_neg (by rw [Finset.mem_Ico]; omega),
    if_neg (by rw [Finset.mem_Ico]; omega), if_pos (by rw [Finset.mem_Ico]; omega)]
  norm_num

theorem rect_empty_factor (ha : 2 ≤ a) (b : ℕ) (hb : 1 ≤ b) :
    (∑ d ∈ range (2 ^ (a + 2)), (X : ℝ[X]) ^ segOnes (rectG a) (a + 2) a 1 b d)
      = C ((2 : ℝ) ^ (a + 2)) := by
  classical
  have hq0 : 0 < a + 2 := by omega
  have hset := segSet_one_pos a b hb
  have hlen : segLen (a + 2) a 1 b = 0 := by
    rw [segLen_eq_card _ _ _ _ hq0, hset]
    rfl
  rw [rect_segOnes_gf a ha, hlen, hset]
  simp

/-- **The rectangle sequence is NOT abelian at the window length `a`.** -/
theorem rect_not_isAbelianAt (ha : 2 ≤ a) (c : ℕ → ℕ) (hcB : ∀ m, c m < 2 ^ (a + 2))
    (hc : IsNormalSequence (2 ^ (a + 2)) c) :
    ¬ IsAbelianAt (blockSeq (rectG a) c (a + 2)) a := by
  classical
  intro h
  have hq0 : 0 < a + 2 := by omega
  have hB0 : 0 < 2 ^ (a + 2) := by positivity
  set S := (a + 2) + a with hSdef
  have hS1 : 1 ≤ S := by omega
  have hSle : (a + 2) + a ≤ (a + 2) * S + 1 := by
    have : S ≤ (a + 2) * S := Nat.le_mul_of_pos_left S hq0
    omega
  have hfib : ∀ r < a + 2, ∀ t < a, (r + t) / (a + 2) < S := by
    intro r hr t ht
    have := Nat.div_le_self (r + t) (a + 2)
    omega
  have hbf := (isAbelianAt_blockSeq_iff (rectG a) c hB0 hq0 hcB hc a S hSle).mp h 0 (by omega)
  set m : ℝ := (2 : ℝ) ^ (a + 2) with hm
  have hmpos : 0 < m := by positivity
  have hcast : ((2 ^ (a + 2) : ℕ) : ℝ) = m := by push_cast [hm]; ring
  -- every residue other than `1` gives the exact Binomial window
  have hother : ∀ r, r < a + 2 → r ≠ 1 →
      (winGf (rectG a) (a + 2) (2 ^ (a + 2)) S a r).coeff 0 = m ^ S / 2 ^ a := by
    intro r hr hr1
    have hw : winGf (rectG a) (a + 2) (2 ^ (a + 2)) S a r
        = C (((2 ^ (a + 2) : ℕ) : ℝ) ^ S / 2 ^ a) * (1 + X) ^ a := by
      refine winGf_eq_binomial (rectG a) hB0 S a r (hfib r hr) (fun b hb => ?_)
      have hshape : segSet (a + 2) a r b
          = Finset.Ico (r - b * (a + 2)) (min (a + 2) (r + a - b * (a + 2))) :=
        segSet_eq_Ico_gen _ _ _ _
      have hnd : ¬ (r - b * (a + 2) = 1 ∧ min (a + 2) (r + a - b * (a + 2)) = a + 1) := by
        rcases Nat.eq_zero_or_pos b with rfl | hb1
        · simp only [Nat.zero_mul, Nat.sub_zero]
          omega
        · have hbq : a + 2 ≤ b * (a + 2) := Nat.le_mul_of_pos_left _ hb1
          omega
      rw [rect_segOnes_gf a ha, hshape,
        rect_corr_eq_zero a ha _ _ (min_le_left _ _) hnd, mul_zero, add_zero, hcast]
    rw [hw, Polynomial.coeff_C_mul, add_comm (1 : ℝ[X]) X, Polynomial.coeff_X_add_one_pow,
      hcast]
    simp
  -- the residue `1` sees the defective segment
  have hone : (winGf (rectG a) (a + 2) (2 ^ (a + 2)) S a 1).coeff 0
      = m ^ S / 2 ^ a - m ^ (S - 1) := by
    have hw : winGf (rectG a) (a + 2) (2 ^ (a + 2)) S a 1
        = (C (m / 2 ^ a) * (1 + X) ^ a + (1 + X) ^ (a - 2) * ((X - 1) * (1 - X)))
          * (C m) ^ (S - 1) := by
      rw [winGf_eq_prod (rectG a) hB0 (a + 2) S a 1 (hfib 1 (by omega)), Finset.range_eq_Ico,
        Finset.prod_eq_prod_Ico_succ_bot (by omega : (0 : ℕ) < S)]
      congr 1
      · exact rect_defect_factor a ha
      · rw [Finset.prod_congr rfl (fun b hb => rect_empty_factor a ha b
          (by rw [Finset.mem_Ico] at hb; omega)), Finset.prod_const, Nat.card_Ico]
    have cpow : ∀ k : ℕ, ((1 + X : ℝ[X]) ^ k).coeff 0 = 1 := fun k => by
      rw [add_comm, Polynomial.coeff_X_add_one_pow]
      simp
    have c2 : ((X - 1 : ℝ[X]) * (1 - X)).coeff 0 = -1 := by
      rw [Polynomial.mul_coeff_zero]
      simp
    have c3 : ((C m : ℝ[X]) ^ (S - 1)).coeff 0 = m ^ (S - 1) := by
      rw [← map_pow, Polynomial.coeff_C_zero]
    rw [hw, Polynomial.mul_coeff_zero, c3, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.mul_coeff_zero, cpow a, cpow (a - 2), c2]
    have hpow : m ^ S = m * m ^ (S - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    field_simp
    rw [hpow]
    ring
  -- assemble
  rw [blockFreq_eq_coeff, ← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega : 1 < a + 2)),
    Finset.sum_congr rfl (fun r hr => hother r
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr)),
    hone, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
    Finset.card_range, nsmul_eq_mul, hcast] at hbf
  have hmS : (0 : ℝ) < m ^ S := by positivity
  have hmS1 : (0 : ℝ) < m ^ (S - 1) := by positivity
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hqR : ((a + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.choose_zero_right, Nat.cast_one] at hbf
  have hden : (((a + 2 : ℕ) : ℝ) * m ^ S) ≠ 0 := by positivity
  rw [div_eq_iff hden, show (a + 2 - 1 : ℕ) = a + 1 from by omega] at hbf
  push_cast at hbf
  have h1 : ((a : ℝ) + 1) * (m ^ S / 2 ^ a) + (m ^ S / 2 ^ a)
      - 1 / 2 ^ a * (((a : ℝ) + 2) * m ^ S) = 0 := by
    field_simp
    ring
  have hzero : m ^ (S - 1) = 0 := by linarith
  linarith

theorem blockSeq_rectG_lt_two (c : ℕ → ℕ) (n : ℕ) : blockSeq (rectG a) c (a + 2) n < 2 :=
  rectG_lt_two a _ _

end Rect

/-- **C4, the single-exclusion case.**  For every `a ≥ 2` some binary sequence is abelian at
exactly the window lengths `≠ a`.  This is the first witness whose exact window set has a FINITE
nonempty complement, and the engine (`rect_segGf`) is linear in the design, so superposing
rectangles on disjoint coordinate groups gives every finite complement. -/
theorem c4_realizable_compl_singleton (a : ℕ) (ha : 2 ≤ a) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ≠ a) := by
  set c := digitOf (2 ^ (a + 2)) (Int.fract NormalNumbers.G4.Sched.fullRealW) with hcdef
  have hb2 : 2 ≤ 2 ^ (a + 2) := by
    have : 2 ^ 1 ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hcB : ∀ m, c m < 2 ^ (a + 2) := fun m => digitOf_lt (2 ^ (a + 2)) hb2 _ m
  have hc : IsNormalSequence (2 ^ (a + 2)) c := by
    have h := NormalNumbers.G4.Sched.isNormal_two_pow_fullRealW (a + 2) (by omega)
    rw [IsNormal] at h
    exact h
  refine ⟨blockSeq (rectG a) c (a + 2), blockSeq_rectG_lt_two a c, fun L hL => ?_⟩
  constructor
  · intro h hLa
    subst hLa
    exact rect_not_isAbelianAt L ha c hcB hc h
  · intro hne
    exact rect_isAbelianAt_of_ne a ha c hcB hc L hne

end NormalNumbers.Abelian
