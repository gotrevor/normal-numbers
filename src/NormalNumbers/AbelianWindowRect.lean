/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowGf

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

end Rect

end NormalNumbers.Abelian
