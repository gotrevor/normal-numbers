/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Stoneham
import NormalNumbers.ReciprocalNormal
import NormalNumbers.StonehamSixFailure

/-!
# Sums of Stoneham constants

The pair `α₂,₃`, `α₄,₃` is arithmetically coupled: after putting the two series
over powers of four, the `k`-th coefficient is an integer because
`3^(k+1) ∣ 2^(3^k) + 1`.  Consequently the binary expansion of their sum has zero windows of
asymptotic relative length `1/3`, obstructing even simple normality.
-/

namespace NormalNumbers

open ReciprocalNormal
open Filter Topology

/-- The Stoneham constant `α_{B,c} = Σ_{m≥1} 1/(c^m · B^(c^m))`. -/
noncomputable def stonehamAlpha (B c : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))

theorem stonehamAlpha_two_three : stonehamAlpha 2 3 = stoneham23 := by
  rfl

/-- `α₂,₃ + α₄,₃ = Σ_k ((2^(3^k)+1)/3^k)·4^(−3^k)` is a sum of disjoint integer blocks
(`3^(k+1) ∣ 2^(3^k) + 1`, lifting the exponent), so its binary digits vanish on
`[2·3^k, 3^(k+1))` (0-indexed `digitOf`). -/
theorem digitOf_stoneham_sum_eq_zero (k i : ℕ) (h₁ : 2 * 3 ^ k ≤ i) (h₂ : i < 3 ^ (k + 1)) :
    digitOf 2 (Int.fract (stonehamAlpha 2 3 + stonehamAlpha 4 3)) i = 0 := by
  sorry

/-- Hence the zero frequency is pushed toward `2/3` at `n = 3^(k+1)`. -/
theorem not_isSimplyNormal_stoneham_sum :
    ¬ IsSimplyNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3) := by
  classical
  intro hnormal
  let x := stonehamAlpha 2 3 + stonehamAlpha 4 3
  let s : ℕ → ℕ := digitOf 2 (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / 2 : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / 100) (by norm_num)
  let k := max K 1
  let n₁ := 2 * 3 ^ k
  let n₂ := 3 ^ (k + 1)
  have hkK : K ≤ k := le_max_left _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hkpow : k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have hn₁K : K ≤ n₁ := by dsimp [n₁]; omega
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    rw [pow_succ]
    omega
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_sum_eq_zero k i hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hb
      omega
    have hsub : ((Finset.range n₁).filter fun i => s i = 0) ∪ Finset.Ico n₁ n₂
        ⊆ (Finset.range n₂).filter fun i => s i = 0 := by
      intro a ha
      rw [Finset.mem_union] at ha
      rw [Finset.mem_filter, Finset.mem_range]
      rcases ha with ha | ha
      · rw [Finset.mem_filter, Finset.mem_range] at ha
        exact ⟨ha.1.trans_le hn₁₂, ha.2⟩
      · rw [Finset.mem_Ico] at ha
        exact ⟨ha.2, hforced a (Finset.mem_Ico.mpr ha)⟩
    have hc := Finset.card_le_card hsub
    simpa [Z, Finset.card_union_of_disjoint hdisj, Nat.card_Ico] using hc
  have h₁ := hK n₁ hn₁K
  have h₂ := hK n₂ hn₂K
  rw [Real.dist_eq, abs_lt] at h₁ h₂
  have hn₁pos : (0 : ℝ) < n₁ := by positivity
  have hn₂pos : (0 : ℝ) < n₂ := by positivity
  have e₁ : (1 / 2 - 1 / 100) * (n₁ : ℝ) < Z n₁ := by
    have hx : (1 / 2 - 1 / 100 : ℝ) < (Z n₁ : ℝ) / n₁ := by linarith [h₁.1]
    rwa [lt_div_iff₀ hn₁pos] at hx
  have e₂ : (Z n₂ : ℝ) < (1 / 2 + 1 / 100) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ < (1 / 2 + 1 / 100 : ℝ) := by linarith [h₂.2]
    rwa [div_lt_iff₀ hn₂pos] at hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hn₁ : (n₁ : ℝ) = 2 * (3 : ℝ) ^ k := by simp [n₁]
  have hn₂ : (n₂ : ℝ) = 3 * (3 : ℝ) ^ k := by
    push_cast
    simp [n₂, pow_succ]
    ring
  have hkR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [hn₁] at e₁ e₃
  rw [hn₂] at e₂ e₃
  nlinarith

end NormalNumbers
