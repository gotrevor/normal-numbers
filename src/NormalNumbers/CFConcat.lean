/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Counting

/-!
# W4 CF side — Becher–Yuhjtman Lemma 7 (CF-discrepancy concatenation)

Window-count concatenation calculus for CF digit blocks.  For a pattern `w`
of length `k ≥ 1`, occurrences (`countOccurrences`, fitting windows) obey

* superadditivity: `count x + count u ≤ count (x ++ u)`;
* subadditivity up to straddle: `count (x ++ u) ≤ count x + count u + (k−1)`
  (at most `k−1` windows straddle the seam);

and Lemma 7 follows in *deviation form*: `CFDiscLt w a m ε` says the count
of `w` in `a` is within `ε·|a|` of `m·|a|` (with `m` standing for `γ(I_w)`;
the lemma is pure counting, so `m` is an abstract real in `[0,1]`).

* `CFDiscLt.append` (part 1): good `x` and good-with-margin `u`
  (`ε|u| − (k−1)` deviation) concatenate at the same `ε`.
* `cfDiscLt_append_take` (part 2a): every partial extension of a good block
  by a short block stays within `2ε`.
* `cfDiscLt_short_append` (part 2b): a short foreign prefix stays within
  `2ε`.

Parts 2a/2b use the hypothesis `|u| + (k−1) < ε·|x|` — marginally stronger
than the paper's `|u|/|x| < ε` and exactly what absorbs the straddle
windows; the W5 schedule satisfies it trivially (`k` is fixed while `|x|`
grows).  The paper's `ε < 1` is not needed.
-/

namespace NormalNumbers

open Finset

/-- `countOccurrences` on `[]` counts only the empty pattern. -/
theorem countOccurrences_nil (w : List ℕ) :
    countOccurrences w [] = if w = [] then 1 else 0 := by
  rw [countOccurrences]
  by_cases h : w = [] <;>
    simp [h, List.isPrefixOf_iff_prefix, List.prefix_nil]

/-- Cons recursion for the window count. -/
theorem countOccurrences_cons (w : List ℕ) (a : ℕ) (l : List ℕ) :
    countOccurrences w (a :: l)
      = countOccurrences w l + (if w.isPrefixOf (a :: l) then 1 else 0) := by
  rw [countOccurrences, countOccurrences, List.tails_cons, List.countP_cons]


/-- A nonempty pattern has at most `|l|` occurrences. -/
theorem countOccurrences_le_length {w : List ℕ} (hw : w ≠ []) (l : List ℕ) :
    countOccurrences w l ≤ l.length := by
  induction l with
  | nil => simp [countOccurrences_nil, hw]
  | cons a l ih =>
    rw [countOccurrences_cons]
    by_cases h : w.isPrefixOf (a :: l) <;> simp [h] <;> omega

/-- Superadditivity: windows fully inside either factor survive
concatenation. -/
theorem add_countOccurrences_le_append {w : List ℕ} (hw : w ≠ [])
    (x u : List ℕ) :
    countOccurrences w x + countOccurrences w u
      ≤ countOccurrences w (x ++ u) := by
  induction x with
  | nil => simp [countOccurrences_nil, hw]
  | cons a x ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hpre : w.isPrefixOf (a :: x) → w.isPrefixOf (a :: (x ++ u)) := by
      rw [List.isPrefixOf_iff_prefix, List.isPrefixOf_iff_prefix,
        ← List.cons_append]
      exact fun h => h.trans (List.prefix_append _ _)
    by_cases h : w.isPrefixOf (a :: x)
    · simp only [h, if_true, hpre h, if_true]; omega
    · simp only [h, if_false]
      by_cases h' : w.isPrefixOf (a :: (x ++ u)) <;> simp [h'] <;> omega

/-- Windows of `x` survive under a *left* factor as well. -/
theorem countOccurrences_le_append_left (w : List ℕ) (u x : List ℕ) :
    countOccurrences w x ≤ countOccurrences w (u ++ x) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, countOccurrences_cons]
    by_cases h : w.isPrefixOf (a :: (u ++ x)) <;> simp [h] <;> omega

/-- Subadditivity up to the seam: at most `k−1` windows straddle the
boundary of `x ++ u`. -/
theorem countOccurrences_append_le {w : List ℕ} (hw : w ≠ [])
    (x u : List ℕ) :
    countOccurrences w (x ++ u)
      ≤ countOccurrences w x + countOccurrences w u + (w.length - 1) := by
  have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  set n := x.length with hn
  set k := w.length with hkdef
  rw [countOccurrences_eq_card, countOccurrences_eq_card,
    countOccurrences_eq_card]
  simp only [← hn]
  have hsub : ((Finset.range ((x ++ u).length + 1)).filter
      (fun i => w.isPrefixOf ((x ++ u).drop i)))
      ⊆ ((Finset.range (n + 1)).filter (fun i => w.isPrefixOf (x.drop i)))
        ∪ (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n))
        ∪ Finset.Ico (n + 1 - k) n := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, List.length_append] at hi
    obtain ⟨hilt, hipre⟩ := hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image, Finset.mem_Ico]
    by_cases hge : n ≤ i
    · -- window starts inside `u`
      refine Or.inl (Or.inr ⟨i - n, ⟨by omega, ?_⟩, by omega⟩)
      have hdrop : (x ++ u).drop i = u.drop (i - n) := by
        rw [List.drop_append]
        have : x.drop i = [] := List.drop_eq_nil_of_le (by omega)
        simp [this, hn]
      rwa [hdrop] at hipre
    · push Not at hge
      by_cases hfit : i + k ≤ n
      · -- window fits inside `x`
        refine Or.inl (Or.inl ⟨by omega, ?_⟩)
        rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take] at hipre ⊢
        have htake : List.take w.length (List.drop i (x ++ u))
            = List.take w.length (List.drop i x) := by
          rw [List.drop_append, List.take_append]
          have h2 : w.length - (x.drop i).length = 0 := by
            rw [List.length_drop]; omega
          simp [h2]
          omega
        rw [← htake]
        exact hipre
      · -- straddling window
        exact Or.inr ⟨by omega, hge⟩
  calc ((Finset.range ((x ++ u).length + 1)).filter
      (fun i => w.isPrefixOf ((x ++ u).drop i))).card
      ≤ (((Finset.range (n + 1)).filter (fun i => w.isPrefixOf (x.drop i)))
        ∪ (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n))
        ∪ Finset.Ico (n + 1 - k) n).card := Finset.card_le_card hsub
    _ ≤ (((Finset.range (n + 1)).filter (fun i => w.isPrefixOf (x.drop i)))
        ∪ (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n))).card
        + (Finset.Ico (n + 1 - k) n).card := Finset.card_union_le _ _
    _ ≤ ((Finset.range (n + 1)).filter
          (fun i => w.isPrefixOf (x.drop i))).card
        + (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n)).card
        + (Finset.Ico (n + 1 - k) n).card := by
        have := Finset.card_union_le
          ((Finset.range (n + 1)).filter (fun i => w.isPrefixOf (x.drop i)))
          (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n))
        omega
    _ ≤ _ := by
        have himg : (((Finset.range (u.length + 1)).filter
            (fun j => w.isPrefixOf (u.drop j))).image (· + n)).card
            = ((Finset.range (u.length + 1)).filter
                (fun j => w.isPrefixOf (u.drop j))).card :=
          Finset.card_image_of_injective _ (add_left_injective n)
        have hico : (Finset.Ico (n + 1 - k) n).card ≤ k - 1 := by
          rw [Nat.card_Ico]; omega
        omega

/-- Deviation-form CF window-count discrepancy: the count of the pattern `w`
in the block `a` is within `ε·|a|` of `m·|a|` (strictly); `m` abstracts the
Gauss measure `γ(I_w)`. -/
def CFDiscLt (w a : List ℕ) (m ε : ℝ) : Prop :=
  |(countOccurrences w a : ℝ) - m * a.length| < ε * a.length

/-- **B–Y Lemma 7, part 1**: a good block extended by a good-with-margin
block (deviation `< ε|u| − (k−1)`) stays within `ε`. -/
theorem CFDiscLt.append {w : List ℕ} (hw : w ≠ []) {x u : List ℕ} {m ε : ℝ}
    (hx : CFDiscLt w x m ε)
    (hu : |(countOccurrences w u : ℝ) - m * u.length|
      < ε * u.length - ((w.length : ℝ) - 1)) :
    CFDiscLt w (x ++ u) m ε := by
  have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  have hlo := add_countOccurrences_le_append hw x u
  have hhi := countOccurrences_append_le hw x u
  have hloR : (countOccurrences w x : ℝ) + countOccurrences w u
      ≤ countOccurrences w (x ++ u) := by exact_mod_cast hlo
  have hhiR : (countOccurrences w (x ++ u) : ℝ)
      ≤ countOccurrences w x + countOccurrences w u
        + ((w.length : ℝ) - 1) := by
    have : ((w.length - 1 : ℕ) : ℝ) = (w.length : ℝ) - 1 := by
      have : 1 ≤ w.length := hk
      push_cast [Nat.cast_sub this]
      ring
    calc (countOccurrences w (x ++ u) : ℝ)
        ≤ ((countOccurrences w x + countOccurrences w u
            + (w.length - 1) : ℕ) : ℝ) := by exact_mod_cast hhi
      _ = _ := by push_cast [Nat.cast_sub hk]; ring
  have hlen : ((x ++ u).length : ℝ) = (x.length : ℝ) + u.length := by
    push_cast [List.length_append]; ring
  rw [CFDiscLt, hlen]
  rw [CFDiscLt, abs_lt] at hx
  rw [abs_lt] at hu
  rw [abs_lt]
  constructor <;> [nlinarith; nlinarith]

/-- **B–Y Lemma 7, part 2a**: every partial extension of a good block by a
short block (`|u| + (k−1) < ε|x|`) stays within `2ε`. -/
theorem cfDiscLt_append_take {w : List ℕ} (hw : w ≠ []) {x u : List ℕ}
    {m ε : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hx : CFDiscLt w x m ε)
    (hshort : (u.length : ℝ) + ((w.length : ℝ) - 1) < ε * x.length)
    (l : ℕ) :
    CFDiscLt w (x ++ u.take l) m (2 * ε) := by
  have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  set t := u.take l with ht
  have hL : (t.length : ℝ) ≤ u.length := by
    have h : t.length ≤ u.length := by
      rw [ht, List.length_take]; exact min_le_right _ _
    exact_mod_cast h
  have hL0 : (0 : ℝ) ≤ t.length := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (w.length : ℝ) - 1 := by
    have : (1 : ℝ) ≤ w.length := by exact_mod_cast hk
    linarith
  have hS0 : (0 : ℝ) ≤ u.length := Nat.cast_nonneg _
  have hεN : 0 < ε * x.length := lt_of_le_of_lt (by linarith) hshort
  have hε : 0 < ε := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hN0]
  have hlo := countOccurrences_le_append_left w x t
  -- windows of `x` survive on the left of `x ++ t` (they are a prefix):
  have hlo' : (countOccurrences w x : ℝ)
      ≤ countOccurrences w (x ++ t) := by
    have h := add_countOccurrences_le_append hw x t
    have : countOccurrences w x ≤ countOccurrences w (x ++ t) := by omega
    exact_mod_cast this
  have hhi := countOccurrences_append_le hw x t
  have hct := countOccurrences_le_length hw t
  have hhiR : (countOccurrences w (x ++ t) : ℝ)
      ≤ countOccurrences w x + t.length + ((w.length : ℝ) - 1) := by
    have h : countOccurrences w (x ++ t)
        ≤ countOccurrences w x + t.length + (w.length - 1) := by omega
    calc (countOccurrences w (x ++ t) : ℝ)
        ≤ ((countOccurrences w x + t.length + (w.length - 1) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = _ := by push_cast [Nat.cast_sub hk]; ring
  have hlen : ((x ++ t).length : ℝ) = (x.length : ℝ) + t.length := by
    push_cast [List.length_append]; ring
  have hmL : m * (t.length : ℝ) ≤ t.length := by nlinarith
  have hmL0 : 0 ≤ m * (t.length : ℝ) := by positivity
  rw [CFDiscLt, hlen]
  rw [CFDiscLt, abs_lt] at hx
  rw [abs_lt]
  constructor <;> nlinarith

/-- **B–Y Lemma 7, part 2b**: a short foreign prefix (`|u| + (k−1) < ε|x|`)
before a good block stays within `2ε`. -/
theorem cfDiscLt_short_append {w : List ℕ} (hw : w ≠ []) {x u : List ℕ}
    {m ε : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hx : CFDiscLt w x m ε)
    (hshort : (u.length : ℝ) + ((w.length : ℝ) - 1) < ε * x.length) :
    CFDiscLt w (u ++ x) m (2 * ε) := by
  have hk : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  have hN0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ u.length := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (w.length : ℝ) - 1 := by
    have : (1 : ℝ) ≤ w.length := by exact_mod_cast hk
    linarith
  have hεN : 0 < ε * x.length := lt_of_le_of_lt (by linarith) hshort
  have hε : 0 < ε := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hN0]
  have hlo : (countOccurrences w x : ℝ)
      ≤ countOccurrences w (u ++ x) := by
    exact_mod_cast countOccurrences_le_append_left w u x
  have hcu := countOccurrences_le_length hw u
  have hhi := countOccurrences_append_le hw u x
  have hhiR : (countOccurrences w (u ++ x) : ℝ)
      ≤ (u.length : ℝ) + countOccurrences w x + ((w.length : ℝ) - 1) := by
    have h : countOccurrences w (u ++ x)
        ≤ u.length + countOccurrences w x + (w.length - 1) := by omega
    calc (countOccurrences w (u ++ x) : ℝ)
        ≤ ((u.length + countOccurrences w x + (w.length - 1) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = _ := by push_cast [Nat.cast_sub hk]; ring
  have hlen : ((u ++ x).length : ℝ) = (u.length : ℝ) + x.length := by
    push_cast [List.length_append]; ring
  have hmS : m * (u.length : ℝ) ≤ u.length := by nlinarith
  have hmS0 : 0 ≤ m * (u.length : ℝ) := by positivity
  rw [CFDiscLt, hlen]
  rw [CFDiscLt, abs_lt] at hx
  rw [abs_lt]
  constructor <;> nlinarith

end NormalNumbers
