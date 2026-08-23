/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# Visit-count algebra

Elementary bricks about `visitCount`: adjacent intervals add, larger
intervals see more visits, and a `[p/b^k, q/b^k)` window is the sum of its
depth-`k` b-adic cells.  Wall's theorem sandwiches an arbitrary interval
between two such windows.
-/

namespace NormalNumbers

open Filter

theorem visitCount_le (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) : visitCount u a c n ≤ n := by
  classical
  calc visitCount u a c n
      ≤ (Finset.range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

theorem visitCount_mono (u : ℕ → ℝ) {a a' c c' : ℝ} (ha : a' ≤ a) (hc : c ≤ c')
    (n : ℕ) : visitCount u a c n ≤ visitCount u a' c' n := by
  classical
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Set.mem_Ico] at hk ⊢
  exact ⟨hk.1, le_trans ha hk.2.1, lt_of_lt_of_le hk.2.2 hc⟩

theorem visitCount_add (u : ℕ → ℝ) {a c c' : ℝ} (h1 : a ≤ c) (h2 : c ≤ c')
    (n : ℕ) :
    visitCount u a c n + visitCount u c c' n = visitCount u a c' n := by
  classical
  simp only [visitCount]
  rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · congr 1
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans_le h2⟩
      · exact ⟨h1.trans h.1, h.2⟩
    · intro h
      by_cases hc : u k < c
      · exact Or.inl ⟨h.1, hc⟩
      · exact Or.inr ⟨not_lt.mp hc, h.2⟩
  · rw [Finset.disjoint_filter]
    intro x _ hx1 hx2
    exact absurd (Set.mem_Ico.mp hx2).1
      (not_le.mpr (Set.mem_Ico.mp hx1).2)

/-- A `[p/b^k, q/b^k)` window is the sum of its depth-`k` b-adic cells. -/
theorem sum_visitCount_cells (b : ℕ) (hb : 2 ≤ b) (u : ℕ → ℝ) (k : ℕ)
    {p q : ℕ} (hpq : p ≤ q) (n : ℕ) :
    ∑ m ∈ Finset.Ico p q,
        visitCount u ((m : ℝ) / (b : ℝ) ^ k) ((m + 1 : ℝ) / (b : ℝ) ^ k) n
      = visitCount u ((p : ℝ) / (b : ℝ) ^ k) ((q : ℝ) / (b : ℝ) ^ k) n := by
  classical
  induction q, hpq using Nat.le_induction with
  | base => simp [visitCount]
  | succ q hpq ih =>
      rw [Finset.sum_Ico_succ_top hpq, ih]
      have hb0 : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      have hle : (p : ℝ) / (b : ℝ) ^ k ≤ (q : ℝ) / (b : ℝ) ^ k := by
        gcongr
      have hle2 : (q : ℝ) / (b : ℝ) ^ k ≤ ((q : ℝ) + 1) / (b : ℝ) ^ k := by
        gcongr
        linarith
      rw [visitCount_add u hle hle2 n]
      norm_cast

end NormalNumbers
