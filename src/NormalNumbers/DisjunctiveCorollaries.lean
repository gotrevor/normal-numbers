/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive
import Mathlib.NumberTheory.Real.Irrational

/-!
# Two unconditional consequences of disjunctivity

Both are pure consequences of the definition `IsDisjunctive b x = ∀ a c, 0 ≤ a → a < c →
c ≤ 1 → ∃ n, orbit b x n ∈ Ico a c`; neither needs any arithmetic.

* **`IsDisjunctive.irrational`** — a rational `x = a/q` has `q · orbit b x n ∈ ℤ` for every
  `n`, so its orbit misses `[1/(2|q|), 1/|q|)`.  No hypothesis on the base.
* **`IsDisjunctive.exists_ge`** — every target interval is hit *arbitrarily late*.  Cutting
  `[a,c)` into `N+1` disjoint pieces produces `N+1` distinct hitting times, so one of them is
  at least `N`.  Consequently (`IsDisjunctive.exists_occursAt_ge`) every finite word occurs
  at arbitrarily late positions, hence infinitely often.
-/

open scoped BigOperators

namespace NormalNumbers

/-! ### Disjunctive ⟹ irrational -/

/-- Auxiliary form of `IsDisjunctive.irrational` with a positive denominator. -/
private theorem ne_div_of_isDisjunctive {b : ℕ} {x : ℝ} (h : IsDisjunctive b x)
    (a q : ℤ) (hq : 0 < q) : x ≠ (a : ℝ) / (q : ℝ) := by
  intro hx
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  -- every orbit point is a multiple of `1/q`
  have key : ∀ n : ℕ, ∃ k : ℤ, (q : ℝ) * orbit b x n = (k : ℝ) := by
    intro n
    refine ⟨a * (b : ℤ) ^ n - q * ⌊x * (b : ℝ) ^ n⌋, ?_⟩
    have hqx : (q : ℝ) * (x * (b : ℝ) ^ n) = (a : ℝ) * (b : ℝ) ^ n := by
      rw [hx]; field_simp
    rw [orbit, Int.fract, mul_sub, hqx]
    push_cast
    ring
  obtain ⟨n, hn⟩ := h (1 / (2 * q)) (1 / q) (by positivity)
    (div_lt_div_of_pos_left one_pos hq0 (by linarith)) ((div_le_one hq0).2 hq1)
  obtain ⟨k, hk⟩ := key n
  rw [Set.mem_Ico] at hn
  have e1 : (q : ℝ) * (1 / (2 * q)) = 1 / 2 := by field_simp
  have e2 : (q : ℝ) * (1 / q) = 1 := by field_simp
  have hlo : (1 : ℝ) / 2 ≤ (k : ℝ) := by
    rw [← hk, ← e1]; exact mul_le_mul_of_nonneg_left hn.1 hq0.le
  have hhi : (k : ℝ) < 1 := by
    rw [← hk, ← e2]; exact mul_lt_mul_of_pos_left hn.2 hq0
  have hk1 : (1 : ℤ) ≤ k := by
    have : (0 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  linarith

/-- **A disjunctive number is irrational.**  If `x = a/q` with `q ≠ 0` then `q · orbit b x n`
is an integer for every `n`, so no orbit point lies in `[1/(2|q|), 1/|q|)` — an interval that
disjunctivity is obliged to hit.  No hypothesis on the base. -/
theorem IsDisjunctive.irrational {b : ℕ} {x : ℝ} (h : IsDisjunctive b x) : Irrational x := by
  rw [irrational_iff_ne_rational]
  intro a q hq hx
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · exact ne_div_of_isDisjunctive h (-a) (-q) (by omega)
      (by rw [hx]; push_cast; rw [neg_div_neg_eq])
  · exact ne_div_of_isDisjunctive h a q hpos hx

/-! ### Every interval is hit arbitrarily late -/

/-- **Disjunctivity is automatically recurrent.**  For every `N`, some orbit time `n ≥ N`
lands in `[a, c)`: cut `[a,c)` into the `N+1` disjoint pieces `[a+i·d, a+(i+1)·d)`,
`d = (c−a)/(N+1)`; each is hit, the hitting times are distinct, so they cannot all be `< N`. -/
theorem IsDisjunctive.exists_ge {b : ℕ} {x : ℝ} (h : IsDisjunctive b x) (N : ℕ)
    {a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    ∃ n, N ≤ n ∧ orbit b x n ∈ Set.Ico a c := by
  classical
  by_contra hcon0
  rw [not_exists] at hcon0
  have hcon : ∀ n, N ≤ n → orbit b x n ∉ Set.Ico a c := fun n hn hmem => hcon0 n ⟨hn, hmem⟩
  set d : ℝ := (c - a) / ((N : ℝ) + 1) with hd
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hdpos : 0 < d := div_pos (by linarith) hNpos
  have hdN : ((N : ℝ) + 1) * d = c - a := by
    rw [hd]; field_simp
  -- the `i`-th piece is inside `[a, c)` for `i ≤ N`
  have hpiece : ∀ i : ℕ, i ≤ N → a + ((i : ℝ) + 1) * d ≤ c := by
    intro i hi
    have hile : (i : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      have : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      linarith
    have := mul_le_mul_of_nonneg_right hile hdpos.le
    linarith [hdN]
  have key : ∀ i : ℕ, i ≤ N →
      ∃ m, orbit b x m ∈ Set.Ico (a + (i : ℝ) * d) (a + ((i : ℝ) + 1) * d) := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * d := by positivity
    refine h _ _ (by linarith) (by nlinarith) ?_
    have := hpiece i hi
    linarith
  choose! m hm using key
  -- each piece sits inside `[a, c)`
  have hmem : ∀ i, i ≤ N → orbit b x (m i) ∈ Set.Ico a c := by
    intro i hi
    obtain ⟨h1, h2⟩ := hm i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * d := by positivity
    exact ⟨by linarith, lt_of_lt_of_le h2 (hpiece i hi)⟩
  -- so every hitting time is `< N`
  have hlt : ∀ i, i ≤ N → m i < N := by
    intro i hi
    by_contra hge
    exact hcon (m i) (by omega) (hmem i hi)
  -- and the hitting times are distinct
  have hinj : Set.InjOn m (Finset.range (N + 1)) := by
    have hmono : ∀ i j : ℕ, i < j → j ≤ N → orbit b x (m i) < orbit b x (m j) := by
      intro i j hij hj
      obtain ⟨-, h2⟩ := hm i (by omega)
      obtain ⟨h1, -⟩ := hm j hj
      have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
      have := mul_le_mul_of_nonneg_right this hdpos.le
      linarith
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with h' | h'
    · exact absurd (hij ▸ hmono i j h' (by omega)) (lt_irrefl _)
    · have h'' : j < i := by omega
      exact absurd (hij ▸ hmono j i h'' (by omega)) (lt_irrefl _)
  have hmaps : ∀ i ∈ Finset.range (N + 1), m i ∈ Finset.range N := by
    intro i hi
    exact Finset.mem_range.2 (hlt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
  have hcard := Finset.card_le_card_of_injOn m hmaps hinj
  simp only [Finset.card_range] at hcard
  omega

/-- **Every finite word occurs arbitrarily late**, hence infinitely often. -/
theorem IsDisjunctive.exists_occursAt_ge {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (h : IsDisjunctive b x)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (N : ℕ) : ∃ n, N ≤ n ∧ OccursAt b x w n := by
  have hval : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hw
  have hpow : (0 : ℝ) < (b : ℝ) ^ w.length := by
    have : (0 : ℝ) < (b : ℝ) := by positivity
    positivity
  have ha : (0 : ℝ) ≤ (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by positivity
  have hac : (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length <
      ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length := by
    rw [div_lt_div_iff₀ hpow hpow]; nlinarith
  have hc : ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length ≤ 1 := by
    rw [div_le_one hpow]
    exact_mod_cast Nat.succ_le_of_lt hval
  obtain ⟨n, hn, hmem⟩ := h.exists_ge N ha hac hc
  exact ⟨n, hn, (occursAt_iff_orbit_mem b hb x w hw n).2 hmem⟩

end NormalNumbers
