/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2WeakSched

/-!
# Gap sets cannot feed the `HypE` frame (a size obstruction)

In the base-2 frame the cutoff exponent `e` must satisfy `HypE 3 K e`, which forces
`e ≤ 2^{8K²}` (`HypE.e_le`).  The demand `m₁(3,K)·log 2 − 21K² − 4 ≤ Σ_{p ∈ S, p ≤ 2^{2^e}} 1/p`
needs `F_S(e) ≳ 1000·K³`.  A set with a logarithmic rate `F_S(e) ≤ A·log(e+1) + C` (e.g.
`towerGapPrimes`) gets only `F_S(e) ≤ A(8K²+1) + C` inside the frame, so for large `K` no cutoff
works: `hypE_frame_excludes_logRate`.

So case (iii) cannot be closed by S-restricting the moment cap alone: the bound `e ≤ 2^{8K²}`
also enters through `four_mul_le_two_pow_NE'` (the far tail `farC ≈ log log X ≈ mE = e + 8K²`
against `2^N`, `N = 100K²`), which is an *all-primes* harmonic sum up to `X`.  The decoupling
needs both `term_b/term_c` and `farC` restricted to `S`-primes, or a grid with `N` growing like
`m₁`.  Reopen condition: `SRestrictedFrame` below.
-/

open Finset Real

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N T m₂)

/-- `HypE` caps the cutoff exponent by `2^{8K²}`. -/
lemma HypE.e_le {b K e : ℕ} (h : HypE b K e) : e ≤ 2 ^ m₂ K := by
  have hT1 : 1 ≤ T K := Sched.T_pos h.hK1
  have := h.hi
  unfold McE at this
  have : e ≤ 100000 * T K * e := Nat.le_mul_of_pos_left _ (by positivity)
  omega

lemma K_cube_le_m₁ (K : ℕ) : 1000 * K ^ 3 ≤ m₁ 3 K := by
  unfold m₁
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  have h1 : K ^ 3 ≤ K ^ (2 * K + 1) := Nat.pow_le_pow_right hK (by omega)
  have h2 : 1 ≤ 3 ^ (2 * K + 4) := Nat.one_le_pow _ _ (by norm_num)
  calc 1000 * K ^ 3 ≤ 1000 * 3 ^ (2 * K + 4) * K ^ (2 * K + 1) := by
        rw [mul_assoc]; gcongr
        exact h1.trans (Nat.le_mul_of_pos_left _ (by positivity))
    _ = _ := rfl

variable {S : ℕ → Prop} [DecidablePred S]

/-- **The size obstruction.**  A prime set whose reciprocal sum grows at most logarithmically in
the cutoff exponent cannot meet the schedule's demand at any cutoff the `HypE` frame admits,
once `K` is large.  Hence `isDisjunctive_subsetLambert_two_of_gapSet` (for `towerGapPrimes`-like
sets) needs a different frame, not only an `S`-restricted moment cap. -/
theorem hypE_frame_excludes_logRate {A C : ℝ}
    (hup : ∀ e : ℕ, MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e + 1) ≤ A * Real.log ((e : ℝ) + 1) + C) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∀ e, ∀ h : HypE 3 K e,
      ¬ ((m₁ 3 K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
        ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S, (p : ℝ)⁻¹) := by
  refine ⟨⌈max A 0 + |C|⌉₊ + 100, fun K hK e h hlow => ?_⟩
  have hl2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  -- the frame's sum is at most `F_S`
  have hsub : ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S, (p : ℝ)⁻¹
      ≤ MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e + 1) := by
    unfold MertensAP.sumInvPrimesIn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter, smallPrimes, RE] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  -- `log(e+1) ≤ 8K² + 1`
  have he := HypE.e_le h
  have hlog : Real.log ((e : ℝ) + 1) ≤ 8 * (K : ℝ) ^ 2 + 1 := by
    have hle : (e : ℝ) + 1 ≤ (2 : ℝ) ^ (m₂ K + 1) := by
      have : e + 1 ≤ 2 ^ (m₂ K + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := m₂ K); omega
      exact_mod_cast this
    calc Real.log ((e : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ (m₂ K + 1)) :=
          Real.log_le_log (by positivity) hle
      _ = ((m₂ K + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ ((m₂ K + 1 : ℕ) : ℝ) := by
          have : (0 : ℝ) ≤ ((m₂ K + 1 : ℕ) : ℝ) := by positivity
          nlinarith
      _ = 8 * (K : ℝ) ^ 2 + 1 := by unfold m₂; push_cast; ring
  have hm := K_cube_le_m₁ K
  have hmr : 1000 * (K : ℝ) ^ 3 ≤ (m₁ 3 K : ℝ) := by exact_mod_cast hm
  have hKr : (⌈max A 0 + |C|⌉₊ : ℝ) + 100 ≤ K := by exact_mod_cast hK
  have hc := Nat.le_ceil (max A 0 + |C|)
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hAA : A ≤ max A 0 := le_max_left _ _
  have hCC : C ≤ |C| := le_abs_self C
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hup' := hup e
  have hlog0 : 0 ≤ Real.log ((e : ℝ) + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) e; linarith)
  have hAl : A * Real.log ((e : ℝ) + 1) ≤ max A 0 * (8 * (K : ℝ) ^ 2 + 1) :=
    (mul_le_mul_of_nonneg_right hAA hlog0).trans (mul_le_mul_of_nonneg_left hlog hA0)
  -- combine: `690 K³ ≤ m₁ log 2 ≤ F + 21K² + 4 ≤ max A 0·(8K²+1) + |C| + 21K² + 4`
  have hK100 : (100 : ℝ) ≤ K := by linarith
  have hB : max A 0 + |C| ≤ K := by linarith
  have hm1 : 690 * (K : ℝ) ^ 3 ≤ (m₁ 3 K : ℝ) * Real.log 2 := by
    have : (0 : ℝ) ≤ (m₁ 3 K : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  have hfin : max A 0 * (8 * (K : ℝ) ^ 2 + 1) + |C| + 21 * (K : ℝ) ^ 2 + 4
      < 690 * (K : ℝ) ^ 3 := by
    have h1 : max A 0 * (8 * (K : ℝ) ^ 2 + 1) ≤ K * (8 * (K : ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  linarith

/-- **Reopen condition** for case (iii) in a base-2 frame (open, `def … : Prop` node): a schedule
witness frame in which the cutoff exponent may be as large as `2^{2^{m₁}}` (needed for
log-rate sets), i.e. both the moment order and the far tail are controlled by `S`-restricted
reciprocal sums.  Stated as: for every `ℓ, w` there is a covariance-form witness for every
divergent prime set.  This is exactly what `isDisjunctive_subsetLambert_two_of_gapSet` would
consume.  Realised in the `farCS` witness form (`ScheduleWitnessSCS`) by
`G4.SchedB.Dec.exists_scheduleWitnessSCS_two_of_divergent`. -/
def SRestrictedFrame : Prop :=
  ∀ (S : ℕ → Prop) [DecidablePred S], (∀ p, S p → p.Prime) →
    Filter.Tendsto (fun e : ℕ => MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e)) Filter.atTop Filter.atTop →
    ∀ ℓ w : ℕ, 1 ≤ ℓ → Nonempty (ScheduleWitnessSC S 2 ℓ w)

end SchedB

end NormalNumbers.G4
