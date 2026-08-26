/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Counting
import NormalNumbers.DigitInterval
import NormalNumbers.Sandwich

/-!
# Wall's theorem

D. D. Wall (1949): a real number is normal in base `b` iff its
multiply-by-`b` orbit `n ↦ b^n·x mod 1` is equidistributed mod 1.

The dictionary: an occurrence of the digit block `w` at position `i` is
exactly a visit of the orbit to the b-adic cell
`[blockNatVal w / b^k, (blockNatVal w + 1) / b^k)` (`digits_prefix_iff` +
the shift lemma `digitOf_orbit`), up to at most `w.length` boundary
windows (`card_filter_matchesAt_le`).  Equidistribution ⟹ normality is
then a direct transfer; normality ⟹ equidistribution feeds every cell's
frequency (every cell is `padWord`-named by a block) into the b-adic
sandwich (`equidistributed_of_badic`).
-/

namespace NormalNumbers

open Filter

/-- The orbit only sees the fractional part. -/
theorem orbit_fract (b : ℕ) (x : ℝ) (n : ℕ) :
    orbit b (Int.fract x) n = orbit b x n := by
  unfold orbit
  have h : Int.fract x * (b : ℝ) ^ n
      = x * (b : ℝ) ^ n - ((⌊x⌋ * (b ^ n : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

/-- Companion to `tendsto_div_of_bounded_diff`, transferring the limit
from the larger count down to the smaller one. -/
private theorem tendsto_div_of_bounded_diff' {A B : ℕ → ℕ} {C : ℕ} {L : ℝ}
    (hAB : ∀ n, A n ≤ B n) (hBA : ∀ n, B n ≤ A n + C)
    (h : Tendsto (fun n => (B n : ℝ) / n) atTop (nhds L)) :
    Tendsto (fun n => (A n : ℝ) / n) atTop (nhds L) := by
  have hlower : Tendsto (fun n : ℕ => (B n : ℝ) / n - C / n) atTop (nhds L) := by
    have hC : Tendsto (fun n : ℕ => (C : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
    simpa using h.sub hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower h ?_ ?_
  · intro n
    dsimp only
    rw [div_sub_div_same]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    have h' : (B n : ℝ) ≤ (A n : ℝ) + C := by exact_mod_cast hBA n
    linarith
  · intro n
    dsimp only
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    exact_mod_cast hAB n

/-- Window matches of the digit sequence are orbit visits to the block's
b-adic cell. -/
private theorem matchesAt_iff_orbit_mem (b : ℕ) (hb : 2 ≤ b) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (w : List ℕ) (hw : ∀ d ∈ w, d < b) (i : ℕ) :
    MatchesAt (digitOf b x) w i ↔ orbit b x i ∈
      Set.Ico ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length) := by
  have horb : orbit b x i ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [← digits_prefix_iff b hb _ horb w hw]
  constructor
  · intro h j hj
    rw [digitOf_orbit b hb x hx.1 i j]
    rw [h j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  · intro h j hj
    rw [← digitOf_orbit b hb x hx.1 i j, h j hj,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

/-- Orbit visits to a block's cell, as a count of window matches. -/
private theorem visitCount_eq_card_matchesAt (b : ℕ) (hb : 2 ≤ b) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (w : List ℕ) (hw : ∀ d ∈ w, d < b) (n : ℕ) :
    visitCount (orbit b x) ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length) n
      = ((Finset.range n).filter (MatchesAt (digitOf b x) w)).card := by
  classical
  unfold visitCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (matchesAt_iff_orbit_mem b hb hx w hw i).symm

/-! ### Wall's theorem -/

/-- **Wall's theorem** (1949): a real number is normal in base `b` iff its
multiply-by-`b` orbit is equidistributed mod 1. -/
theorem isNormal_iff_equidistributed_orbit (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    IsNormal b x ↔ Equidistributed (orbit b x) := by
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hx'mem : Int.fract x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have horb : orbit b (Int.fract x) = orbit b x := funext (orbit_fract b x)
  rw [← horb]
  show IsNormalSequence b (digitOf b (Int.fract x))
    ↔ Equidistributed (orbit b (Int.fract x))
  set x' := Int.fract x with hx'def
  constructor
  · -- normal ⟹ equidistributed, via the b-adic sandwich
    intro hn
    apply equidistributed_of_badic b hb
    intro k hk m hm
    set w := padWord b k m with hwdef
    have hlen : w.length = k := length_padWord hb hm
    have hwlt : ∀ d ∈ w, d < b := padWord_digits_lt hb k m
    have hwne : w ≠ [] := by
      intro hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    have hval : blockNatVal b w = m := blockNatVal_padWord hb k m
    have hcount := hn w hwne hwlt
    have hle := fun n => card_filter_matchesAt_le (digitOf b x') w hwne n
    have htrans := tendsto_div_of_bounded_diff
      (fun n => (hle n).1) (fun n => (hle n).2) hcount
    have heq : ∀ n, ((Finset.range n).filter
        (MatchesAt (digitOf b x') w)).card
        = visitCount (orbit b x') ((m : ℝ) / (b : ℝ) ^ k)
            ((m + 1 : ℝ) / (b : ℝ) ^ k) n := by
      intro n
      rw [← hval, ← hlen]
      exact (visitCount_eq_card_matchesAt b hb hx'mem w hwlt n).symm
    have hlim : ((b : ℝ) ^ w.length)⁻¹ = 1 / (b : ℝ) ^ k := by
      rw [hlen, one_div]
    rw [← hlim]
    refine htrans.congr fun n => ?_
    rw [heq n]
  · -- equidistributed ⟹ normal
    intro he w hwne hwlt
    have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hwne
    have hval_lt : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hwlt
    have hpow : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
    have ha : (0 : ℝ) ≤ (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
      positivity
    have hac : (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length
        ≤ ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length := by
      gcongr
      linarith
    have hc1 : ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length ≤ 1 := by
      rw [div_le_one hpow]
      have : (blockNatVal b w : ℝ) + 1 ≤ ((b : ℝ) ^ w.length) := by
        exact_mod_cast Nat.succ_le_of_lt hval_lt
      linarith
    have hcell := he _ _ ha hac hc1
    have hdiff : ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length
        - (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length
        = ((b : ℝ) ^ w.length)⁻¹ := by
      rw [div_sub_div_same]
      ring_nf
    rw [hdiff] at hcell
    have hle := fun n => card_filter_matchesAt_le (digitOf b x') w hwne n
    refine tendsto_div_of_bounded_diff'
      (fun n => (hle n).1) (fun n => (hle n).2) ?_
    refine hcell.congr fun n => ?_
    rw [visitCount_eq_card_matchesAt b hb hx'mem w hwlt n]

end NormalNumbers
