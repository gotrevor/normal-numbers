import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic means to prefix means (obligation W4 of DESIGN-2026-09-19-bcr-wiring.md)

If a bounded sequence has vanishing dyadic block means `(1/N) ∑_{N ≤ n < 2N} F n → 0`
along **all** `N → ∞` (not just powers of two), then its prefix means
`(1/n) ∑_{k < n} F k → 0`.

Route (halving chain): put `n_i = n / 2^i`.  Each step `∑_{k < n_i} − ∑_{k < n_{i+1}}` is a
dyadic block at scale `N = n_{i+1}` up to at most one extra endpoint term (cost `≤ C`), so it is
`≤ ε' n_{i+1} + C`.  Telescoping `m` steps costs `≤ ε' n + C m`, and the head is `≤ C n / 2^m`.
-/

open Filter Topology

namespace NormalNumbers

/-- Dyadic block mean `(1/N) ∑_{N ≤ n < 2N} F n`. -/
noncomputable def dyadicMean (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), F n) / N

/-- Prefix mean `(1/n) ∑_{k < n} F k`. -/
noncomputable def prefixMean (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range n, F k) / n

section Halving

variable {F : ℕ → ℂ} {C ε' : ℝ} {N₀ : ℕ}

/-- One halving step: the block `[n/2, n)` is the dyadic block at `N = n/2` plus at most one term. -/
theorem halving_step (hC : 0 ≤ C) (hF : ∀ n, ‖F n‖ ≤ C)
    (hbd : ∀ N, N₀ ≤ N → ‖dyadicMean F N‖ ≤ ε') (hN₀ : 1 ≤ N₀) (n : ℕ) (hn : N₀ ≤ n / 2) :
    ‖(∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2), F k‖
      ≤ ε' * ((n / 2 : ℕ) : ℝ) + C := by
  set N := n / 2 with hN
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hn
  have hle : N ≤ n := Nat.div_le_self _ _
  have hsub : (∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range N, F k
      = ∑ k ∈ Finset.Ico N n, F k := (Finset.sum_Ico_eq_sub _ hle).symm
  -- the dyadic block sum
  have hdy : ∑ k ∈ Finset.Ico N (2 * N), F k = dyadicMean F N * (N : ℂ) := by
    rw [dyadicMean, div_mul_cancel₀]
    exact_mod_cast Nat.cast_ne_zero.2 hNpos.ne'
  have hblock : ‖∑ k ∈ Finset.Ico N (2 * N), F k‖ ≤ ε' * (N : ℝ) := by
    rw [hdy, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (hbd N hn) (Nat.cast_nonneg _)
  have hcase : n = 2 * N ∨ n = 2 * N + 1 := by omega
  rw [hsub]
  rcases hcase with h | h
  · rw [h]
    refine le_trans hblock ?_
    linarith
  · have : ∑ k ∈ Finset.Ico N n, F k = (∑ k ∈ Finset.Ico N (2 * N), F k) + F (2 * N) := by
      rw [h, Finset.sum_Ico_succ_top (by omega)]
    rw [this]
    calc ‖(∑ k ∈ Finset.Ico N (2 * N), F k) + F (2 * N)‖
        ≤ ‖∑ k ∈ Finset.Ico N (2 * N), F k‖ + ‖F (2 * N)‖ := norm_add_le _ _
      _ ≤ ε' * (N : ℝ) + C := add_le_add hblock (hF _)

/-- Telescoping the halving chain `m` times. -/
theorem halving_chain (hC : 0 ≤ C) (hε : 0 ≤ ε') (hF : ∀ n, ‖F n‖ ≤ C)
    (hbd : ∀ N, N₀ ≤ N → ‖dyadicMean F N‖ ≤ ε') (hN₀ : 1 ≤ N₀) :
    ∀ (m n : ℕ), N₀ ≤ n / 2 ^ m →
      ‖(∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2 ^ m), F k‖
        ≤ ε' * (n : ℝ) + C * m := by
  intro m
  induction m with
  | zero =>
      intro n _
      simp only [pow_zero, Nat.div_one, sub_self, norm_zero, Nat.cast_zero, mul_zero, add_zero]
      positivity
  | succ m ih =>
      intro n hn
      have hsplit : n / 2 ^ (m + 1) = (n / 2) / 2 ^ m := by
        rw [Nat.div_div_eq_div_mul]
        ring_nf
      have hn2 : N₀ ≤ n / 2 := by
        refine le_trans hn ?_
        rw [hsplit]
        exact Nat.div_le_self _ _
      have hnm : N₀ ≤ (n / 2) / 2 ^ m := by rw [← hsplit]; exact hn
      have h1 := halving_step hC hF hbd hN₀ n hn2
      have h2 := ih (n / 2) hnm
      have hkey : (∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2 ^ (m + 1)), F k
          = ((∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2), F k)
            + ((∑ k ∈ Finset.range (n / 2), F k)
                - ∑ k ∈ Finset.range ((n / 2) / 2 ^ m), F k) := by
        rw [hsplit]; ring
      have hhalf : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n / 2) + (n / 2) ≤ n := by omega
        exact_mod_cast this
      rw [hkey]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      calc ‖_ + _‖ ≤ (ε' * ((n / 2 : ℕ) : ℝ) + C) + (ε' * ((n / 2 : ℕ) : ℝ) + C * m) :=
            le_trans (norm_add_le _ _) (add_le_add h1 h2)
        _ ≤ ε' * (n : ℝ) + C * (m + 1) := by
            have hmul := mul_le_mul_of_nonneg_left hhalf hε
            nlinarith
      
end Halving

/-- **W4**: vanishing dyadic means at every scale give vanishing prefix means, for bounded `F`. -/
theorem prefixMean_tendsto_zero_of_dyadic (F : ℕ → ℂ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C)
    (hD : Tendsto (dyadicMean F) atTop (𝓝 0)) :
    Tendsto (prefixMean F) atTop (𝓝 0) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hF 0)
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set ε' := ε / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  -- threshold for the dyadic means
  have hD' : ∀ᶠ N : ℕ in atTop, ‖dyadicMean F N‖ < ε' :=
    (NormedAddGroup.tendsto_nhds_zero.1 hD) ε' hε'pos
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hD'
  set N₀ := max N₁ 1 with hN₀def
  have hN₀ : 1 ≤ N₀ := le_max_right _ _
  have hbd : ∀ N, N₀ ≤ N → ‖dyadicMean F N‖ ≤ ε' := fun N hN =>
    (hN₁ N (le_trans (le_max_left _ _) hN)).le
  -- depth m with C / 2^m < ε'
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((1:ℝ)/2) ^ m < ε' / (C + 1) :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have hm' : C * ((1:ℝ)/2) ^ m < ε' := by
    have hpos : (0:ℝ) < C + 1 := by linarith
    have h := (lt_div_iff₀ hpos).1 hm
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) m]
  -- threshold in n
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n → C * m / (n : ℝ) < ε' := by
    have : Tendsto (fun n : ℕ => C * m / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (this.eventually (gt_mem_nhds hε'pos))
    exact ⟨n₂, hn₂⟩
  refine eventually_atTop.2 ⟨max (2 ^ m * N₀) (max n₂ 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hdiv : N₀ ≤ n / 2 ^ m := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num : 0 < 2) m)]
    rw [mul_comm]
    exact le_trans (le_max_left (2 ^ m * N₀) _) hn
  have hchain := halving_chain hC hε'pos.le hF hbd hN₀ m n hdiv
  -- head term
  have hhead : ‖∑ k ∈ Finset.range (n / 2 ^ m), F k‖ ≤ C * ((n / 2 ^ m : ℕ) : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ k ∈ Finset.range (n / 2 ^ m), ‖F k‖ ≤ ∑ _k ∈ Finset.range (n / 2 ^ m), C :=
          Finset.sum_le_sum (fun k _ => hF k)
      _ = C * ((n / 2 ^ m : ℕ) : ℝ) := by rw [Finset.sum_const, Finset.card_range]; ring
  have hheadn : ((n / 2 ^ m : ℕ) : ℝ) ≤ (n : ℝ) * ((1:ℝ)/2) ^ m := by
    have h1 : ((n / 2 ^ m : ℕ) : ℝ) ≤ (n : ℝ) / ((2:ℝ) ^ m) := by
      have : ((n / 2 ^ m : ℕ) : ℝ) ≤ ((n : ℝ)) / ((2 ^ m : ℕ) : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self n (2 ^ m)
      simpa using this
    have h2 : (n : ℝ) * ((1:ℝ)/2) ^ m = (n : ℝ) / ((2:ℝ) ^ m) := by
      rw [div_pow, one_pow]; ring
    rw [h2]; exact h1
  have htotal : ‖∑ k ∈ Finset.range n, F k‖
      ≤ ε' * (n : ℝ) + C * m + C * ((n:ℝ) * ((1:ℝ)/2) ^ m) := by
    have hsp : ((∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2 ^ m), F k)
          + ∑ k ∈ Finset.range (n / 2 ^ m), F k = (∑ k ∈ Finset.range n, F k) := by ring
    calc ‖∑ k ∈ Finset.range n, F k‖
        = ‖((∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2 ^ m), F k)
          + ∑ k ∈ Finset.range (n / 2 ^ m), F k‖ := by rw [hsp]
      _ ≤ ‖(∑ k ∈ Finset.range n, F k) - ∑ k ∈ Finset.range (n / 2 ^ m), F k‖
          + ‖∑ k ∈ Finset.range (n / 2 ^ m), F k‖ := norm_add_le _ _
      _ ≤ (ε' * (n : ℝ) + C * m) + C * ((n:ℝ) * ((1:ℝ)/2) ^ m) :=
          add_le_add hchain (le_trans hhead (by nlinarith [hheadn]))
  rw [prefixMean, norm_div, Complex.norm_natCast]
  rw [div_lt_iff₀ hnpos]
  have hmn : C * m / (n:ℝ) < ε' := hn₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hmn' : C * m < ε' * n := by
    rw [div_lt_iff₀ hnpos] at hmn; linarith
  have : C * ((n:ℝ) * ((1:ℝ)/2) ^ m) < ε' * n := by
    have := mul_lt_mul_of_pos_left hm' hnpos
    nlinarith
  have : ‖∑ k ∈ Finset.range n, F k‖ < 3 * (ε' * n) := by linarith [htotal]
  have h4 : 3 * (ε' * (n:ℝ)) < ε * n := by
    rw [hε']; nlinarith
  linarith

end NormalNumbers
