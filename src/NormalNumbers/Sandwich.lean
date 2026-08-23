/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Visits

/-!
# The b-adic sandwich theorem

The analytic core of Wall's theorem: if every depth-`k` b-adic cell
`[m/b^k, (m+1)/b^k)` is visited with limiting frequency `1/b^k` (for every
`k ≥ 1`), then the sequence is equidistributed.

`tendsto_window` sums the cell frequencies into the frequency of a window
`[p/b^k, q/b^k)`.  `equidistributed_of_badic` then sandwiches an arbitrary
interval `[a, c)` between an inner and an outer such window whose lengths
differ from `c - a` by less than `2/b^k`, and lets `k → ∞`.
-/

namespace NormalNumbers

open Filter

/-- Summing the depth-`k` cell frequencies: if every b-adic cell of depth `k`
has limiting visit frequency `1/b^k`, then the window `[p/b^k, q/b^k)` has
limiting visit frequency `(q - p)/b^k`. -/
theorem tendsto_window (b : ℕ) (hb : 2 ≤ b) (u : ℕ → ℝ) (k : ℕ)
    (h : ∀ m, m < b ^ k → Filter.Tendsto
      (fun n => (visitCount u ((m : ℝ) / (b : ℝ) ^ k) ((m + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n)
      Filter.atTop (nhds (1 / (b : ℝ) ^ k)))
    {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ b ^ k) :
    Filter.Tendsto
      (fun n => (visitCount u ((p : ℝ) / (b : ℝ) ^ k) ((q : ℝ) / (b : ℝ) ^ k) n : ℝ) / n)
      Filter.atTop (nhds (((q : ℝ) - p) / (b : ℝ) ^ k)) := by
  have hsum : Filter.Tendsto
      (fun n => ∑ m ∈ Finset.Ico p q,
        (visitCount u ((m : ℝ) / (b : ℝ) ^ k) ((m + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n)
      Filter.atTop (nhds (∑ _m ∈ Finset.Ico p q, 1 / (b : ℝ) ^ k)) :=
    tendsto_finsetSum _ fun m hm => h m ((Finset.mem_Ico.mp hm).2.trans_le hq)
  have hval : ∑ _m ∈ Finset.Ico p q, 1 / (b : ℝ) ^ k = ((q : ℝ) - p) / (b : ℝ) ^ k := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hpq]
    ring
  rw [hval] at hsum
  refine hsum.congr fun n => ?_
  rw [← sum_visitCount_cells b hb u k hpq n, Nat.cast_sum, Finset.sum_div]

/-- **The b-adic sandwich theorem**: a sequence all of whose b-adic cell visit
frequencies (at every depth `k ≥ 1`) converge to the cell length `1/b^k` is
equidistributed. -/
theorem equidistributed_of_badic (b : ℕ) (hb : 2 ≤ b) (u : ℕ → ℝ)
    (h : ∀ k, 1 ≤ k → ∀ m, m < b ^ k → Filter.Tendsto
      (fun n => (visitCount u ((m : ℝ) / (b : ℝ) ^ k) ((m + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n)
      Filter.atTop (nhds (1 / (b : ℝ) ^ k))) :
    Equidistributed u := by
  intro a c ha hac hc1
  have hb1 : (1 : ℝ) < b := by
    have h1 : 1 < b := by omega
    exact_mod_cast h1
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the depth `k ≥ 1` with `4/b^k < ε`
  obtain ⟨k, hk1, hK_lt⟩ : ∃ k : ℕ, 1 ≤ k ∧ 4 / ε < (b : ℝ) ^ k := by
    obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (4 / ε) hb1
    exact ⟨max k₀ 1, le_max_right _ _,
      hk₀.trans_le (pow_le_pow_right₀ hb1.le (le_max_left _ _))⟩
  have hbk0 : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have h4K : 4 < ε * (b : ℝ) ^ k := by
    have h' := (div_lt_iff₀ hε).mp hK_lt
    linarith
  have haK : 0 ≤ a * (b : ℝ) ^ k := mul_nonneg ha hbk0.le
  have hcK : 0 ≤ c * (b : ℝ) ^ k := mul_nonneg (ha.trans hac) hbk0.le
  have hcK_le : c * (b : ℝ) ^ k ≤ (b : ℝ) ^ k := mul_le_of_le_one_left hbk0.le hc1
  have hacK : a * (b : ℝ) ^ k ≤ c * (b : ℝ) ^ k := mul_le_mul_of_nonneg_right hac hbk0.le
  -- the four b-adic grid points around `a` and `c`:
  -- inner window `[m₁/b^k, m₂/b^k) ⊆ [a, c) ⊆ [p/b^k, q/b^k)` outer window
  obtain ⟨m₁, hm₁_ge, hm₁_lt⟩ :
      ∃ m : ℕ, a * (b : ℝ) ^ k ≤ m ∧ (m : ℝ) < a * (b : ℝ) ^ k + 1 :=
    ⟨⌈a * (b : ℝ) ^ k⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one haK⟩
  obtain ⟨m₂, hm₂_le, hm₂_gt⟩ :
      ∃ m : ℕ, (m : ℝ) ≤ c * (b : ℝ) ^ k ∧ c * (b : ℝ) ^ k < m + 1 :=
    ⟨⌊c * (b : ℝ) ^ k⌋₊, Nat.floor_le hcK, Nat.lt_floor_add_one _⟩
  obtain ⟨p, hp_le, hp_gt⟩ :
      ∃ m : ℕ, (m : ℝ) ≤ a * (b : ℝ) ^ k ∧ a * (b : ℝ) ^ k < m + 1 :=
    ⟨⌊a * (b : ℝ) ^ k⌋₊, Nat.floor_le haK, Nat.lt_floor_add_one _⟩
  obtain ⟨q, hq_ge, hq_lt⟩ :
      ∃ m : ℕ, c * (b : ℝ) ^ k ≤ m ∧ (m : ℝ) < c * (b : ℝ) ^ k + 1 :=
    ⟨⌈c * (b : ℝ) ^ k⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one hcK⟩
  -- ℕ-level bookkeeping for the outer window
  have hpq : p ≤ q := by
    have hpq' : (p : ℝ) ≤ (q : ℝ) := by linarith
    exact_mod_cast hpq'
  have hq_le_bk : q ≤ b ^ k := by
    have h1 : (q : ℝ) < ((b ^ k : ℕ) : ℝ) + 1 := by push_cast; linarith
    have h2 : q < b ^ k + 1 := by exact_mod_cast h1
    omega
  -- the outer window covers `[a, c)`
  have hp_le_a : (p : ℝ) / (b : ℝ) ^ k ≤ a := by
    rw [div_le_iff₀ hbk0]; exact hp_le
  have hc_le_q : c ≤ (q : ℝ) / (b : ℝ) ^ k := by
    rw [le_div_iff₀ hbk0]; exact hq_ge
  -- upper side: the outer window frequency stays below `(c - a) + ε`
  have hout := tendsto_window b hb u k (h k hk1) hpq hq_le_bk
  have hout_lt : ((q : ℝ) - p) / (b : ℝ) ^ k < c - a + ε := by
    rw [div_lt_iff₀ hbk0]
    nlinarith
  have hev_up : ∀ᶠ n in Filter.atTop, (visitCount u a c n : ℝ) / n < c - a + ε := by
    filter_upwards [hout.eventually_lt_const hout_lt] with n hn
    refine lt_of_le_of_lt ?_ hn
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (visitCount_mono u hp_le_a hc_le_q n)) (Nat.cast_nonneg n)
  -- lower side: the frequency stays above `(c - a) - ε`
  have hev_lo : ∀ᶠ n in Filter.atTop, c - a - ε < (visitCount u a c n : ℝ) / n := by
    by_cases h12 : m₁ ≤ m₂
    · -- the inner window is nonempty and sits inside `[a, c)`
      have hm₂_le_bk : m₂ ≤ b ^ k := by
        have h1 : (m₂ : ℝ) ≤ ((b ^ k : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast h1
      have ha_le_m₁ : a ≤ (m₁ : ℝ) / (b : ℝ) ^ k := by
        rw [le_div_iff₀ hbk0]; exact hm₁_ge
      have hm₂_le_c : (m₂ : ℝ) / (b : ℝ) ^ k ≤ c := by
        rw [div_le_iff₀ hbk0]; exact hm₂_le
      have hin := tendsto_window b hb u k (h k hk1) h12 hm₂_le_bk
      have hin_gt : c - a - ε < ((m₂ : ℝ) - m₁) / (b : ℝ) ^ k := by
        rw [lt_div_iff₀ hbk0]
        nlinarith
      filter_upwards [hin.eventually_const_lt hin_gt] with n hn
      refine lt_of_lt_of_le hn ?_
      exact div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (visitCount_mono u ha_le_m₁ hm₂_le_c n)) (Nat.cast_nonneg n)
    · -- degenerate case: `[a, c)` is shorter than `ε`, and frequencies are `≥ 0`
      have h' : m₂ + 1 ≤ m₁ := by omega
      have hcast : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast h'
      have hlt1 : c - a < 1 / (b : ℝ) ^ k := by
        rw [lt_div_iff₀ hbk0]
        nlinarith
      have hlt2 : 1 / (b : ℝ) ^ k < ε := by
        rw [div_lt_iff₀ hbk0]
        linarith
      refine Filter.Eventually.of_forall fun n => ?_
      have h0 : (0 : ℝ) ≤ (visitCount u a c n : ℝ) / n :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
  -- combine the two eventual bounds
  have hev : ∀ᶠ n in Filter.atTop,
      dist ((visitCount u a c n : ℝ) / n) (c - a) < ε := by
    filter_upwards [hev_up, hev_lo] with n h1 h2
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩
  exact Filter.eventually_atTop.mp hev

end NormalNumbers
