/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogScale
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion
import NormalNumbers.Disjunctive

/-!
# N10: from `R_n` to the orbit of `x_S`

`2^n x_S − R_n ∈ [0, 1/(n+1)]` (`two_pow_mul_xS_sub`), so the Weyl sums of the orbit of `x_S`
differ from those of `R_n` by `≤ 2M + N·4π|h|/M` for any cut `M`.  With `weyl_Rs` this gives
`isNormal_xS`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset Filter Topology NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4

/-- The orbit phase equals the phase of `2^n x_S`. -/
lemma ePhase_orbit (S : ℕ → Prop) (h : ℤ) (n : ℕ) :
    ePhase ((h : ℝ) * orbit 2 (xS S) n) = ePhase ((h : ℝ) * ((2 : ℝ) ^ n * xS S)) := by
  have e : (h : ℝ) * orbit 2 (xS S) n = (h : ℝ) * ((2 : ℝ) ^ n * xS S) +
      ((-(h * ⌊xS S * (2 : ℝ) ^ n⌋) : ℤ) : ℝ) := by
    rw [orbit, Int.fract]; push_cast; ring
  rw [e, ePhase_add_int]

/-- The orbit Weyl sum is within `2M + N·4π|h|/M` of the `R_n` Weyl sum. -/
lemma orbit_sum_close (S : ℕ → Prop) (hS : ∀ m, S m → 1 ≤ m) (h : ℤ) (N M : ℕ) (hM : 0 < M) :
    ‖∑ n ∈ range N, ePhase ((h : ℝ) * orbit 2 (xS S) n) -
        ∑ n ∈ range N, ePhase ((h : ℝ) * (Rs S n : ℝ))‖ ≤
      2 * M + N * (4 * Real.pi * |(h : ℝ)| / M) := by
  set C := 4 * Real.pi * |(h : ℝ)|
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpt : ∀ n, ‖ePhase ((h : ℝ) * orbit 2 (xS S) n) - ePhase ((h : ℝ) * (Rs S n : ℝ))‖ ≤
      2 * (if n < M then 1 else 0) + C / M := by
    intro n
    rw [ePhase_orbit]
    have hC : 0 ≤ C / M := by positivity
    split_ifs with hn
    · have := norm_sub_le (ePhase ((h : ℝ) * ((2 : ℝ) ^ n * xS S))) (ePhase ((h : ℝ) * (Rs S n : ℝ)))
      rw [norm_ePhase, norm_ePhase] at this; linarith
    · refine (norm_ePhase_sub _ _).trans ?_
      obtain ⟨h0, h1⟩ := two_pow_mul_xS_sub S hS n
      have hn' : (M : ℝ) ≤ n + 1 := by
        have : M ≤ n + 1 := by omega
        exact_mod_cast this
      have hd : |(2 : ℝ) ^ n * xS S - (Rs S n : ℝ)| ≤ 1 / M := by
        rw [abs_of_nonneg h0]
        exact h1.trans (one_div_le_one_div_of_le hMr hn')
      rw [← mul_sub, abs_mul, ← mul_assoc]
      calc 4 * Real.pi * |(h : ℝ)| * |(2 : ℝ) ^ n * xS S - (Rs S n : ℝ)| ≤ C * (1 / M) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 2 * 0 + C / M := by ring
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hpt n).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
  have : ∑ n ∈ range N, (if n < M then (1 : ℝ) else 0) ≤ M := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((range N).filter (· < M)).card ≤ M := by
      refine (Finset.card_le_card ?_).trans (card_range M).le
      intro n hn; simp only [Finset.mem_filter] at hn; exact Finset.mem_range.2 hn.2
    exact_mod_cast this
  linarith

/-- **N10.**  `x_S` is normal in base 2 under the hypotheses of `weyl_Rs`. -/
theorem isNormal_xS (hV : VandeheyThm51) {S : ℕ → Prop} {Z : ℕ → ℕ} (hmono : Monotone Z)
    (hZ3 : ∀ n, 3 ≤ Z n) (hS3 : ∀ K, S (3 ^ K) ∧ S (2 * 3 ^ K)) (hS : ∀ m, S m → 1 ≤ m)
    (hsupp : ∀ m p, S m → 1 ≤ m → p.Prime → p ∣ m → p ≤ Z m) {ε : ℝ} (hε : 0 < ε)
    (hY : ∀ᶠ n : ℕ in atTop,
      ((Z n).primeCounting : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.log n)) :
    IsNormal 2 (xS S) := by
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  refine equidistributed_of_weyl _ (orbit_mem_Ico 2 _) ?_
  intro h hh
  have heq : fourierMean (orbit 2 (xS S)) h =
      fun N => (∑ n ∈ range N, ePhase ((h : ℝ) * orbit 2 (xS S) n)) / N := by
    funext N
    rw [fourierMean]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ePhase]; congr 1; push_cast; ring
  rw [heq, Metric.tendsto_atTop]
  intro η hη
  set C := 4 * Real.pi * |(h : ℝ)|
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * C / η)
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  have hM0' : 0 < M := by exact_mod_cast hM0
  obtain ⟨N₀, hN₀⟩ := (weyl_Rs hV hmono hZ3 hS3 hsupp hε hY h hh (half_pos hη)).exists_forall_of_atTop
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 * M / η)
  refine ⟨max N₀ (N₁ + 1), fun N hN => ?_⟩
  have hNa : N₀ ≤ N := le_of_max_le_left hN
  have hNb : N₁ + 1 ≤ N := le_of_max_le_right hN
  have hNr : (N₁ : ℝ) + 1 ≤ N := by exact_mod_cast hNb
  have hN0 : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)]
  have h1 := hN₀ N hNa
  have h2 := orbit_sum_close S hS h N M hM0'
  rw [dist_zero_right, norm_div, Complex.norm_natCast, div_lt_iff₀ hN0]
  have hCM : C / M < η / 4 := by
    rw [div_lt_iff₀ hM0]; rw [div_lt_iff₀ hη] at hM; linarith
  have h2M : 2 * (M : ℝ) < η / 4 * N := by
    rw [div_lt_iff₀ hη] at hN₁; nlinarith
  have hsum := norm_sub_norm_le (∑ n ∈ range N, ePhase ((h : ℝ) * orbit 2 (xS S) n))
    (∑ n ∈ range N, ePhase ((h : ℝ) * (Rs S n : ℝ)))
  have : (N : ℝ) * (C / M) ≤ N * (η / 4) := mul_le_mul_of_nonneg_left hCM.le hN0.le
  nlinarith

end NormalNumbers.GrowingLocalizedLog
