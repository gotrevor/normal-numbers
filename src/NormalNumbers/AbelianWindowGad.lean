/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowRect

/-!
# The gadget at an arbitrary position, and gadget REMOVAL by an involution

`AbelianWindowRect` builds the rectangle design as a table on a block of width exactly `a + 2`.
Read as a map on words it only ever touches the FOUR bit positions `{0, 1, a, a+1}`, so it is a
*gadget* that can be placed anywhere in a wider block, and several disjoint gadgets can be placed
in the same block.  This file sets that up:

* `gadBit q p a r d` — bit `r` of the digit `d`, with bits `p+a` and `p+a+1` exchanged exactly
  when `bit p ≠ bit (p+1) ∧ bit (p+a) = bit (p+1) ∧ bit (p+a+1) = bit p` (`gadTrig`);
* `multiG q gs` — the table carrying a whole list `gs` of gadgets on pairwise disjoint quadruples;
* **the removal lemmas**, which are the point of the file.  For a trace `I`:
  - `blockGf_cons_of_high` — if `I` holds both or neither of the HIGH pair `{p+a, p+a+1}` the
    gadget changes no one-count at all, pointwise in `d`;
  - `blockGf_cons_of_low` — if `I` holds both or neither of the LOW pair `{p, p+1}` the gadget
    still drops out, now by re-indexing the digit sum along the involution
    `d ↦ gadSwap` (exchange `p ↔ p+1` and `p+a ↔ p+a+1`) on the trigger set: the swap preserves
    the trigger, and it moves the one-count by exactly the amount the gadget does.

Since an interval trace can fully separate at most one gadget (that forces `lo = p+1` and
`hi = p+a+1`, so the gadget is determined), these two lemmas reduce the law of a block carrying
MANY gadgets to the law of a block carrying ONE — with no polynomial algebra, which is what makes
the multi-scale construction affordable.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-! ## Bit surgery -/

theorem getD_map_range (q r : ℕ) (f : ℕ → ℕ) (hr : r < q) :
    (((List.range q).map f).getD r 0) = f r := by
  have hlen : ((List.range q).map f).length = q := by simp
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hr)]
  simp

theorem bitw_eq_getD (q d r : ℕ) : bitw q d r = (wordOf 2 q d).getD r 0 := rfl

/-- Two `q`-bit digits with the same bits are equal. -/
theorem bitw_ext {q d e : ℕ} (hd : d < 2 ^ q) (he : e < 2 ^ q)
    (h : ∀ r, r < q → bitw q d r = bitw q e r) : d = e := by
  have hw : wordOf 2 q d = wordOf 2 q e := by
    refine List.ext_getElem (by simp) (fun r h1 h2 => ?_)
    have hr : r < q := by simpa using h1
    have := h r hr
    rw [bitw, bitw, List.getD_eq_getElem _ _ (by simpa using hr),
      List.getD_eq_getElem _ _ (by simpa using hr)] at this
    exact this
  calc d = valOf 2 (wordOf 2 q d) := (valOf_wordOf (by norm_num) q d hd).symm
    _ = valOf 2 (wordOf 2 q e) := by rw [hw]
    _ = e := valOf_wordOf (by norm_num) q e he

/-- The digit whose `q`-bit word is `d`'s with the bits at `i` and `j` interchanged. -/
def swapBits (q i j d : ℕ) : ℕ :=
  valOf 2 ((List.range q).map (fun r => bitw q d (if r = i then j else if r = j then i else r)))

theorem swapBits_lt (q i j d : ℕ) : swapBits q i j d < 2 ^ q := by
  have hlen : ((List.range q).map
      (fun r => bitw q d (if r = i then j else if r = j then i else r))).length = q := by simp
  have := valOf_lt (B := 2) (by norm_num)
    ((List.range q).map (fun r => bitw q d (if r = i then j else if r = j then i else r)))
    (fun e he => by
      rw [List.mem_map] at he
      obtain ⟨r, -, rfl⟩ := he
      exact bitw_lt_two _ _ _)
  rwa [hlen] at this

theorem bitw_swapBits (q i j d r : ℕ) (hr : r < q) :
    bitw q (swapBits q i j d) r = bitw q d (if r = i then j else if r = j then i else r) := by
  set w := (List.range q).map (fun r => bitw q d (if r = i then j else if r = j then i else r))
    with hwdef
  have hlen : w.length = q := by rw [hwdef]; simp
  have hlt : ∀ e ∈ w, e < 2 := by
    intro e he
    rw [hwdef, List.mem_map] at he
    obtain ⟨t, -, rfl⟩ := he
    exact bitw_lt_two _ _ _
  have hword : wordOf 2 q (valOf 2 w) = w := by
    have := wordOf_valOf (B := 2) (by norm_num) w hlt
    rwa [hlen] at this
  rw [swapBits, ← hwdef, bitw, hword, hwdef, getD_map_range q r _ hr]

/-! ## The gadget -/

/-- The four bit positions the gadget at `(p, a)` couples. -/
def quadSet (p a : ℕ) : Finset ℕ := {p, p + 1, p + a, p + a + 1}

theorem mem_quadSet {p a i : ℕ} : i ∈ quadSet p a ↔ i = p ∨ i = p + 1 ∨ i = p + a ∨ i = p + a + 1 := by
  simp [quadSet]

theorem quadSet_subset {p a q : ℕ} (hq : p + a + 1 < q) : quadSet p a ⊆ range q := by
  intro i hi
  rw [mem_quadSet] at hi
  rw [Finset.mem_range]
  rcases hi with rfl | rfl | rfl | rfl <;> omega

/-- The gadget trigger at `(p, a)`. -/
def gadTrig (q p a d : ℕ) : Prop :=
  bitw q d p ≠ bitw q d (p + 1) ∧ bitw q d (p + a) = bitw q d (p + 1) ∧
    bitw q d (p + a + 1) = bitw q d p

instance (q p a d : ℕ) : Decidable (gadTrig q p a d) := by unfold gadTrig; infer_instance

/-- **The gadget table.**  Bit `r` of the digit `d`, with the high pair exchanged on triggers. -/
def gadBit (q p a r d : ℕ) : ℕ :=
  if gadTrig q p a d then
    (if r = p + a then bitw q d (p + a + 1) else
      if r = p + a + 1 then bitw q d (p + a) else bitw q d r)
  else bitw q d r

theorem gadBit_lt_two (q p a r d : ℕ) : gadBit q p a r d < 2 := by
  unfold gadBit
  split
  · split
    · exact bitw_lt_two _ _ _
    · split <;> exact bitw_lt_two _ _ _
  · exact bitw_lt_two _ _ _

theorem gadBit_low (q p a d : ℕ) (ha : 2 ≤ a) :
    gadBit q p a p d = bitw q d p ∧ gadBit q p a (p + 1) d = bitw q d (p + 1) := by
  refine ⟨?_, ?_⟩
  · unfold gadBit
    by_cases h : gadTrig q p a d
    · rw [if_pos h, if_neg (by omega : ¬ p = p + a), if_neg (by omega : ¬ p = p + a + 1)]
    · rw [if_neg h]
  · unfold gadBit
    by_cases h : gadTrig q p a d
    · rw [if_pos h, if_neg (by omega : ¬ p + 1 = p + a), if_neg (by omega : ¬ p + 1 = p + a + 1)]
    · rw [if_neg h]

/-- The table carrying a whole list of gadgets. -/
def multiG (q : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], r, d => bitw q d r
  | (p, a) :: gs, r, d => if r ∈ quadSet p a then gadBit q p a r d else multiG q gs r d

@[simp] theorem multiG_nil (q r d : ℕ) : multiG q [] r d = bitw q d r := rfl

theorem multiG_cons (q p a : ℕ) (gs : List (ℕ × ℕ)) (r d : ℕ) :
    multiG q ((p, a) :: gs) r d
      = if r ∈ quadSet p a then gadBit q p a r d else multiG q gs r d := rfl

theorem multiG_lt_two (q : ℕ) (gs : List (ℕ × ℕ)) (r d : ℕ) : multiG q gs r d < 2 := by
  induction gs with
  | nil => exact bitw_lt_two _ _ _
  | cons pa gs ih =>
      obtain ⟨p, a⟩ := pa
      rw [multiG_cons]
      split
      · exact gadBit_lt_two _ _ _ _ _
      · exact ih

/-- Off every gadget's quadruple the table is the plain bit. -/
theorem multiG_of_notMem (q : ℕ) (gs : List (ℕ × ℕ)) (r d : ℕ)
    (h : ∀ pa ∈ gs, r ∉ quadSet pa.1 pa.2) : multiG q gs r d = bitw q d r := by
  induction gs with
  | nil => rfl
  | cons pa gs ih =>
      obtain ⟨p, a⟩ := pa
      rw [multiG_cons, if_neg (h (p, a) (by simp))]
      exact ih (fun qa hqa => h qa (by simp [hqa]))

/-- The gadget reads only the bits on its own quadruple. -/
theorem gadBit_congr (q p a : ℕ) (d e : ℕ) (h : ∀ u ∈ quadSet p a, bitw q e u = bitw q d u)
    (r : ℕ) (hr : r ∈ quadSet p a) : gadBit q p a r e = gadBit q p a r d := by
  have h0 := h p (mem_quadSet.mpr (Or.inl rfl))
  have h1 := h (p + 1) (mem_quadSet.mpr (Or.inr (Or.inl rfl)))
  have h2 := h (p + a) (mem_quadSet.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 := h (p + a + 1) (mem_quadSet.mpr (Or.inr (Or.inr (Or.inr rfl))))
  have htrig : gadTrig q p a e ↔ gadTrig q p a d := by
    unfold gadTrig
    rw [h0, h1, h2, h3]
  unfold gadBit
  by_cases hT : gadTrig q p a d
  · rw [if_pos (htrig.mpr hT), if_pos hT, h2, h3, h r hr]
  · rw [if_neg (fun hc => hT (htrig.mp hc)), if_neg hT, h r hr]

/-- Changing the digit only inside one quadruple leaves the other gadgets' output alone. -/
theorem multiG_congr_off (q : ℕ) (gs : List (ℕ × ℕ)) (p a : ℕ) (d e : ℕ)
    (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (hbits : ∀ u, u ∉ quadSet p a → bitw q e u = bitw q d u)
    (r : ℕ) (hr : r ∉ quadSet p a) : multiG q gs r e = multiG q gs r d := by
  induction gs with
  | nil => exact hbits r hr
  | cons pa gs ih =>
      obtain ⟨p', a'⟩ := pa
      rw [multiG_cons, multiG_cons]
      by_cases hmem : r ∈ quadSet p' a'
      · rw [if_pos hmem, if_pos hmem]
        exact gadBit_congr q p' a' d e
          (fun u hu => hbits u (hdisj (p', a') (by simp) u hu)) r hmem
      · rw [if_neg hmem, if_neg hmem]
        exact ih (fun qa hqa => hdisj qa (by simp [hqa]))

/-! ## The removal involution -/

theorem bitw_of_ge (q x u : ℕ) (h : q ≤ u) : bitw q x u = 0 := by
  rw [bitw, List.getD_eq_default _ _ (by simpa using h)]

/-- Exchange the gadget's low pair and its high pair simultaneously. -/
def gadSwap (q p a d : ℕ) : ℕ := swapBits q (p + a) (p + a + 1) (swapBits q p (p + 1) d)

theorem gadSwap_lt (q p a d : ℕ) : gadSwap q p a d < 2 ^ q := swapBits_lt _ _ _ _

theorem bitw_gadSwap_low (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    bitw q (gadSwap q p a d) p = bitw q d (p + 1) := by
  rw [gadSwap, bitw_swapBits q (p + a) (p + a + 1) _ p (by omega),
    if_neg (by omega : ¬ p = p + a), if_neg (by omega : ¬ p = p + a + 1),
    bitw_swapBits q p (p + 1) d p (by omega), if_pos rfl]

theorem bitw_gadSwap_low' (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    bitw q (gadSwap q p a d) (p + 1) = bitw q d p := by
  rw [gadSwap, bitw_swapBits q (p + a) (p + a + 1) _ (p + 1) (by omega),
    if_neg (by omega : ¬ p + 1 = p + a), if_neg (by omega : ¬ p + 1 = p + a + 1),
    bitw_swapBits q p (p + 1) d (p + 1) (by omega), if_neg (by omega : ¬ p + 1 = p),
    if_pos rfl]

theorem bitw_gadSwap_high (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    bitw q (gadSwap q p a d) (p + a) = bitw q d (p + a + 1) := by
  rw [gadSwap, bitw_swapBits q (p + a) (p + a + 1) _ (p + a) (by omega), if_pos rfl,
    bitw_swapBits q p (p + 1) d (p + a + 1) (by omega),
    if_neg (by omega : ¬ p + a + 1 = p), if_neg (by omega : ¬ p + a + 1 = p + 1)]

theorem bitw_gadSwap_high' (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    bitw q (gadSwap q p a d) (p + a + 1) = bitw q d (p + a) := by
  rw [gadSwap, bitw_swapBits q (p + a) (p + a + 1) _ (p + a + 1) (by omega),
    if_neg (by omega : ¬ p + a + 1 = p + a), if_pos rfl,
    bitw_swapBits q p (p + 1) d (p + a) (by omega),
    if_neg (by omega : ¬ p + a = p), if_neg (by omega : ¬ p + a = p + 1)]

theorem bitw_gadSwap_other (q p a d r : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q)
    (hmem : r ∉ quadSet p a) : bitw q (gadSwap q p a d) r = bitw q d r := by
  rw [mem_quadSet] at hmem
  push_neg at hmem
  obtain ⟨h0, h1, h2, h3⟩ := hmem
  rcases Nat.lt_or_ge r q with hr | hr
  · rw [gadSwap, bitw_swapBits q (p + a) (p + a + 1) _ r hr, if_neg h2, if_neg h3,
      bitw_swapBits q p (p + 1) d r hr, if_neg h0, if_neg h1]
  · rw [bitw_of_ge _ _ _ hr, bitw_of_ge _ _ _ hr]

/-- **The involution preserves the trigger.** -/
theorem gadTrig_gadSwap (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    gadTrig q p a (gadSwap q p a d) ↔ gadTrig q p a d := by
  unfold gadTrig
  rw [bitw_gadSwap_low q p a d ha hq, bitw_gadSwap_low' q p a d ha hq,
    bitw_gadSwap_high q p a d ha hq, bitw_gadSwap_high' q p a d ha hq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Ne.symm h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Ne.symm h1, h3, h2⟩

theorem gadSwap_involutive (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) (hd : d < 2 ^ q) :
    gadSwap q p a (gadSwap q p a d) = d := by
  refine bitw_ext (gadSwap_lt q p a (gadSwap q p a d)) hd (fun r hr => ?_)
  by_cases h0 : r ∈ quadSet p a
  · rw [mem_quadSet] at h0
    rcases h0 with h | h | h | h <;> rw [h]
    · rw [bitw_gadSwap_low q p a _ ha hq, bitw_gadSwap_low' q p a d ha hq]
    · rw [bitw_gadSwap_low' q p a _ ha hq, bitw_gadSwap_low q p a d ha hq]
    · rw [bitw_gadSwap_high q p a _ ha hq, bitw_gadSwap_high' q p a d ha hq]
    · rw [bitw_gadSwap_high' q p a _ ha hq, bitw_gadSwap_high q p a d ha hq]
  · rw [bitw_gadSwap_other q p a _ r ha hq h0, bitw_gadSwap_other q p a d r ha hq h0]

/-- The digit map used to delete a gadget: the involution on the trigger set, the identity off
it. -/
def gadPhi (q p a d : ℕ) : ℕ := if gadTrig q p a d then gadSwap q p a d else d

theorem gadPhi_lt (q p a d : ℕ) (hd : d < 2 ^ q) : gadPhi q p a d < 2 ^ q := by
  rw [gadPhi]
  split
  · exact gadSwap_lt _ _ _ _
  · exact hd

theorem gadPhi_involutive (q p a d : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) (hd : d < 2 ^ q) :
    gadPhi q p a (gadPhi q p a d) = d := by
  by_cases hT : gadTrig q p a d
  · have h1 : gadPhi q p a d = gadSwap q p a d := by rw [gadPhi, if_pos hT]
    rw [h1, gadPhi, if_pos ((gadTrig_gadSwap q p a d ha hq).mpr hT),
      gadSwap_involutive q p a d ha hq hd]
  · have h1 : gadPhi q p a d = d := by rw [gadPhi, if_neg hT]
    rw [h1, h1]

theorem bitw_gadPhi_off (q p a d u : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q)
    (hmem : u ∉ quadSet p a) : bitw q (gadPhi q p a d) u = bitw q d u := by
  rw [gadPhi]
  split
  · exact bitw_gadSwap_other q p a d u ha hq hmem
  · rfl

/-! ## Removal -/

/-- The one-count of a trace, as a sum of bits. -/
theorem onesTr_eq_sum (I : Finset ℕ) (T : ℕ → ℕ) (hT : ∀ u, T u < 2) :
    (I.filter (fun u => T u = 1)).card = ∑ r ∈ I, T r := by
  classical
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : T i = 0 ∨ T i = 1 := by have := hT i; omega
  rcases h with h | h <;> simp [h]

theorem sum_quadSet {M : Type*} [AddCommMonoid M] (p a : ℕ) (ha : 2 ≤ a) (f : ℕ → M) :
    ∑ r ∈ quadSet p a, f r = (f p + f (p + 1)) + (f (p + a) + f (p + a + 1)) := by
  have h1 : p ∉ ({p + 1, p + a, p + a + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2 : p + 1 ∉ ({p + a, p + a + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h3 : p + a ∉ ({p + a + 1} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [quadSet, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  abel

/-- Splitting a trace sum at the gadget's quadruple. -/
theorem sum_split_quad (I : Finset ℕ) (p a : ℕ) (ha : 2 ≤ a) (f : ℕ → ℕ) :
    ∑ r ∈ I, f r = (∑ r ∈ I.filter (fun r => r ∉ quadSet p a), f r)
      + (((if p ∈ I then f p else 0) + (if p + 1 ∈ I then f (p + 1) else 0))
        + ((if p + a ∈ I then f (p + a) else 0)
          + (if p + a + 1 ∈ I then f (p + a + 1) else 0))) := by
  classical
  have hset : I.filter (fun r => ¬ (r ∉ quadSet p a)) = (quadSet p a).filter (fun r => r ∈ I) := by
    ext r
    simp only [Finset.mem_filter, not_not]
    tauto
  have h2 : ∑ r ∈ I.filter (fun r => ¬ (r ∉ quadSet p a)), f r
      = ((if p ∈ I then f p else 0) + (if p + 1 ∈ I then f (p + 1) else 0))
        + ((if p + a ∈ I then f (p + a) else 0)
          + (if p + a + 1 ∈ I then f (p + a + 1) else 0)) := by
    rw [hset, Finset.sum_filter]
    exact sum_quadSet p a ha _
  rw [← Finset.sum_filter_add_sum_filter_not I (fun r => r ∉ quadSet p a) f, h2]

/-- Exchanging the two values of a pair that the trace holds both-or-neither of. -/
theorem pair_swap_eq {I : Finset ℕ} {i j : ℕ} (h : i ∈ I ↔ j ∈ I) (x y : ℕ) :
    (if i ∈ I then x else 0) + (if j ∈ I then y else 0)
      = (if i ∈ I then y else 0) + (if j ∈ I then x else 0) := by
  by_cases hi : i ∈ I
  · rw [if_pos hi, if_pos hi, if_pos (h.mp hi), if_pos (h.mp hi)]
    omega
  · have hj : j ∉ I := fun hc => hi (h.mpr hc)
    rw [if_neg hi, if_neg hi, if_neg hj, if_neg hj]

section Removal

variable (q p a : ℕ) (gs : List (ℕ × ℕ))

/-- Off the head gadget's quadruple the two tables agree. -/
theorem multiG_cons_off (r d : ℕ) (hr : r ∉ quadSet p a) :
    multiG q ((p, a) :: gs) r d = multiG q gs r d := by
  rw [multiG_cons, if_neg hr]

/-- On the head gadget's quadruple the tail table is the plain bit. -/
theorem multiG_tail_on (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (r d : ℕ) (hr : r ∈ quadSet p a) : multiG q gs r d = bitw q d r :=
  multiG_of_notMem q gs r d (fun pa hpa hmem => hdisj pa hpa r hmem hr)

/-- **Removal, high case.**  If the trace holds both or neither of the high pair `{p+a, p+a+1}`,
the head gadget changes no one-count at all — pointwise in the digit. -/
theorem multiG_cons_sum_of_high (ha : 2 ≤ a)
    (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (I : Finset ℕ) (hhigh : (p + a ∈ I ↔ p + a + 1 ∈ I)) (d : ℕ) :
    ∑ r ∈ I, multiG q ((p, a) :: gs) r d = ∑ r ∈ I, multiG q gs r d := by
  classical
  have hL : ∀ r ∈ quadSet p a, multiG q ((p, a) :: gs) r d = gadBit q p a r d := fun r hr => by
    rw [multiG_cons, if_pos hr]
  have hR : ∀ r ∈ quadSet p a, multiG q gs r d = bitw q d r :=
    fun r hr => multiG_tail_on q p a gs hdisj r d hr
  have hmp : p ∈ quadSet p a := mem_quadSet.mpr (Or.inl rfl)
  have hmp1 : p + 1 ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inl rfl))
  have hmh : p + a ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hmh1 : p + a + 1 ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hb := gadBit_low q p a d ha
  rw [sum_split_quad I p a ha (fun r => multiG q ((p, a) :: gs) r d),
    sum_split_quad I p a ha (fun r => multiG q gs r d)]
  congr 1
  · refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.mem_filter] at hr
    exact multiG_cons_off q p a gs r d hr.2
  refine congr_arg₂ (· + ·) ?_ ?_
  · rw [hL p hmp, hL (p + 1) hmp1, hR p hmp, hR (p + 1) hmp1, hb.1, hb.2]
  · rw [hL (p + a) hmh, hL (p + a + 1) hmh1, hR (p + a) hmh, hR (p + a + 1) hmh1]
    by_cases hT : gadTrig q p a d
    · have hhi : gadBit q p a (p + a) d = bitw q d (p + a + 1) := by
        rw [gadBit, if_pos hT, if_pos rfl]
      have hhi' : gadBit q p a (p + a + 1) d = bitw q d (p + a) := by
        rw [gadBit, if_pos hT, if_neg (by omega : ¬ p + a + 1 = p + a), if_pos rfl]
      rw [hhi, hhi']
      exact pair_swap_eq hhigh _ _
    · have hhi : gadBit q p a (p + a) d = bitw q d (p + a) := by rw [gadBit, if_neg hT]
      have hhi' : gadBit q p a (p + a + 1) d = bitw q d (p + a + 1) := by rw [gadBit, if_neg hT]
      rw [hhi, hhi']

/-- **Removal, low case.**  If the trace holds both or neither of the low pair `{p, p+1}`, the
head gadget's effect is undone by the involution `gadPhi` on the digit. -/
theorem multiG_cons_sum_of_low (ha : 2 ≤ a) (hq : p + a + 1 < q)
    (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (I : Finset ℕ) (hlow : (p ∈ I ↔ p + 1 ∈ I)) (d : ℕ) :
    ∑ r ∈ I, multiG q ((p, a) :: gs) r d = ∑ r ∈ I, multiG q gs r (gadPhi q p a d) := by
  classical
  have hL : ∀ r ∈ quadSet p a, multiG q ((p, a) :: gs) r d = gadBit q p a r d := fun r hr => by
    rw [multiG_cons, if_pos hr]
  have hR : ∀ r ∈ quadSet p a, multiG q gs r (gadPhi q p a d) = bitw q (gadPhi q p a d) r :=
    fun r hr => multiG_tail_on q p a gs hdisj r (gadPhi q p a d) hr
  have hmp : p ∈ quadSet p a := mem_quadSet.mpr (Or.inl rfl)
  have hmp1 : p + 1 ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inl rfl))
  have hmh : p + a ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hmh1 : p + a + 1 ∈ quadSet p a := mem_quadSet.mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hb := gadBit_low q p a d ha
  rw [sum_split_quad I p a ha (fun r => multiG q ((p, a) :: gs) r d),
    sum_split_quad I p a ha (fun r => multiG q gs r (gadPhi q p a d))]
  congr 1
  · refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.mem_filter] at hr
    rw [multiG_cons_off q p a gs r d hr.2]
    exact (multiG_congr_off q gs p a d (gadPhi q p a d) hdisj
      (fun u hu => bitw_gadPhi_off q p a d u ha hq hu) r hr.2).symm
  refine congr_arg₂ (· + ·) ?_ ?_
  · rw [hL p hmp, hL (p + 1) hmp1, hR p hmp, hR (p + 1) hmp1, hb.1, hb.2]
    by_cases hT : gadTrig q p a d
    · have e0 : bitw q (gadPhi q p a d) p = bitw q d (p + 1) := by
        rw [gadPhi, if_pos hT]; exact bitw_gadSwap_low q p a d ha hq
      have e1 : bitw q (gadPhi q p a d) (p + 1) = bitw q d p := by
        rw [gadPhi, if_pos hT]; exact bitw_gadSwap_low' q p a d ha hq
      rw [e0, e1]
      exact pair_swap_eq hlow _ _
    · have e0 : bitw q (gadPhi q p a d) p = bitw q d p := by rw [gadPhi, if_neg hT]
      have e1 : bitw q (gadPhi q p a d) (p + 1) = bitw q d (p + 1) := by rw [gadPhi, if_neg hT]
      rw [e0, e1]
  · rw [hL (p + a) hmh, hL (p + a + 1) hmh1, hR (p + a) hmh, hR (p + a + 1) hmh1]
    by_cases hT : gadTrig q p a d
    · have hhi : gadBit q p a (p + a) d = bitw q d (p + a + 1) := by
        rw [gadBit, if_pos hT, if_pos rfl]
      have hhi' : gadBit q p a (p + a + 1) d = bitw q d (p + a) := by
        rw [gadBit, if_pos hT, if_neg (by omega : ¬ p + a + 1 = p + a), if_pos rfl]
      have e2 : bitw q (gadPhi q p a d) (p + a) = bitw q d (p + a + 1) := by
        rw [gadPhi, if_pos hT]; exact bitw_gadSwap_high q p a d ha hq
      have e3 : bitw q (gadPhi q p a d) (p + a + 1) = bitw q d (p + a) := by
        rw [gadPhi, if_pos hT]; exact bitw_gadSwap_high' q p a d ha hq
      rw [hhi, hhi', e2, e3]
    · have hhi : gadBit q p a (p + a) d = bitw q d (p + a) := by rw [gadBit, if_neg hT]
      have hhi' : gadBit q p a (p + a + 1) d = bitw q d (p + a + 1) := by rw [gadBit, if_neg hT]
      have e2 : bitw q (gadPhi q p a d) (p + a) = bitw q d (p + a) := by rw [gadPhi, if_neg hT]
      have e3 : bitw q (gadPhi q p a d) (p + a + 1) = bitw q d (p + a + 1) := by
        rw [gadPhi, if_neg hT]
      rw [hhi, hhi', e2, e3]

/-! ### The removal lemmas, at the level of the digit generating function -/

/-- The generating function of the trace `I` over all `q`-bit digits, for a table `T`. -/
noncomputable def blockGf (q : ℕ) (T : ℕ → ℕ → ℕ) (I : Finset ℕ) : ℝ[X] :=
  ∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ ((I.filter (fun u => T u d = 1)).card)

/-- **A gadget whose high pair the trace does not separate is invisible.** -/
theorem blockGf_cons_of_high (ha : 2 ≤ a)
    (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (I : Finset ℕ) (hhigh : (p + a ∈ I ↔ p + a + 1 ∈ I)) :
    blockGf q (multiG q ((p, a) :: gs)) I = blockGf q (multiG q gs) I := by
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [onesTr_eq_sum I _ (fun u => multiG_lt_two q ((p, a) :: gs) u d),
    onesTr_eq_sum I _ (fun u => multiG_lt_two q gs u d),
    multiG_cons_sum_of_high q p a gs ha hdisj I hhigh d]

/-- **A gadget whose low pair the trace does not separate is invisible** — by re-indexing the
digit sum along the involution `gadPhi`. -/
theorem blockGf_cons_of_low (ha : 2 ≤ a) (hq : p + a + 1 < q)
    (hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a)
    (I : Finset ℕ) (hlow : (p ∈ I ↔ p + 1 ∈ I)) :
    blockGf q (multiG q ((p, a) :: gs)) I = blockGf q (multiG q gs) I := by
  rw [blockGf, blockGf]
  refine Finset.sum_nbij' (i := gadPhi q p a) (j := gadPhi q p a) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_range.mpr (gadPhi_lt q p a d (Finset.mem_range.mp hd))
  · intro d hd
    exact Finset.mem_range.mpr (gadPhi_lt q p a d (Finset.mem_range.mp hd))
  · intro d hd
    exact gadPhi_involutive q p a d ha hq (Finset.mem_range.mp hd)
  · intro d hd
    exact gadPhi_involutive q p a d ha hq (Finset.mem_range.mp hd)
  · intro d _
    rw [onesTr_eq_sum I _ (fun u => multiG_lt_two q ((p, a) :: gs) u d),
      onesTr_eq_sum I _ (fun u => multiG_lt_two q gs u (gadPhi q p a d)),
      multiG_cons_sum_of_low q p a gs ha hq hdisj I hlow d]

end Removal

end NormalNumbers.Abelian

