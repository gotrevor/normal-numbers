/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal
import NormalNumbers.GrowingLocalizedLog
import NormalNumbers.VandeheyKorobovDivisors
import NormalNumbers.VandeheyKorobovCounting
import NormalNumbers.VandeheyKorobovRounded
import NormalNumbers.VandeheyKorobovOrders
import NormalNumbers.VandeheyKorobovGcd
import NormalNumbers.VandeheyKorobovBigM
import NormalNumbers.VandeheyKorobovReduction
import NormalNumbers.VandeheyKorobovAggregation
import NormalNumbers.VandeheyKorobovCorrelation
import NormalNumbers.VandeheyKorobovStep

/-!
# Vandehey's Korobov-sum bound, proved (no longer cited)

`Literature.VandeheyDiff.VandeheyThm51` (Vandehey, *Differencing methods for Korobov-type
exponential sums*, J. Anal. Math. 138 (2019), Theorem 5.1) enters the repo as a cited hypothesis.
This file proves it, which makes every theorem that takes it as a binder unconditional.  The two
headline consumers are restated below without the binder.
-/

namespace NormalNumbers.VandeheyProof

open Literature.VandeheyDiff
open Finset
open Erdos438.Fourier
open NormalNumbers.G4
open NormalNumbers.VandeheyKorobov

lemma alpha_lt_one (k : ℕ) : alpha k < 1 := by
  have ha := GrowingLocalizedLog.alpha_le k
  have hpow := GrowingLocalizedLog.two_pow_ge k
  have hden : (2 : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hhalf : 1 / (2 * (2 : ℝ) ^ k) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hden
  linarith

lemma alpha_succ (k : ℕ) :
    alpha (k + 1) = alpha k / (2 * (1 + alpha k)) := by
  have hpow := GrowingLocalizedLog.two_pow_ge k
  have hne : (4 : ℝ) * 2 ^ k - 2 ≠ 0 := by
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith
  simp only [GrowingLocalizedLog.alpha_eq, pow_succ]
  field_simp [hne]
  ring

lemma two_rpow_neg_succ (k : ℕ) :
    (2 : ℝ) ^ (-((k + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ (-(k : ℝ)) / 2 := by
  rw [show -((k + 1 : ℕ) : ℝ) = -(k : ℝ) - 1 by push_cast; ring]
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]

lemma expPair_bounds (k : ℕ) :
    0 ≤ (expPair k).1 ∧ (expPair k).1 ≤ 1 ∧
      1 ≤ (expPair k).2 ∧ (expPair k).2 ≤ 2 ∧
        (expPair k).2 ≤ 1 + (expPair k).1 := by
  induction k with
  | zero => norm_num [expPair]
  | succ k ih =>
      obtain ⟨hγ0, hγ1, hν1, hν2, hgap⟩ := ih
      have hα0 : 0 < alpha k := GrowingLocalizedLog.alpha_pos k
      have hα1 : alpha k < 1 := alpha_lt_one k
      have hden : 0 < 2 * (1 + alpha k) := by positivity
      have hgap0 : 0 ≤ 1 + (expPair k).1 - (expPair k).2 := by linarith
      have hgap1 : 1 + (expPair k).1 - (expPair k).2 ≤ 1 := by linarith
      have hmulν : alpha k * (expPair k).2 ≤ alpha k * 2 :=
        mul_le_mul_of_nonneg_left hν2 hα0.le
      have hmulGap :
          (1 + (expPair k).1 - (expPair k).2) * alpha k ≤ alpha k := by
        simpa using mul_le_mul_of_nonneg_right hgap1 hα0.le
      have hfrac0 : 0 ≤
          (1 + (expPair k).1 - (expPair k).2) * alpha k /
            (2 * (1 + alpha k)) := by positivity
      have hfracHalf :
          (1 + (expPair k).1 - (expPair k).2) * alpha k /
              (2 * (1 + alpha k)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hden]
        nlinarith
      have hprod :
          ((expPair k).2 - (expPair k).1) * (1 - alpha k) ≤ 2 := by
        have hdiff : (expPair k).2 - (expPair k).1 ≤ 2 := by linarith
        have hmul := mul_le_mul_of_nonneg_right hdiff (by linarith : 0 ≤ 1 - alpha k)
        nlinarith [hα0.le]
      rw [GrowingLocalizedLog.expPair_succ]
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · positivity
      · rw [div_le_one hden]
        nlinarith
      · linarith
      · linarith
      · have hdiff : 0 ≤
            1 + (1 + (expPair k).1 + alpha k * (expPair k).2) /
                (2 * (1 + alpha k)) -
              ((1 + (expPair k).2) / 2 +
                (1 + (expPair k).1 - (expPair k).2) * alpha k /
                  (2 * (1 + alpha k))) := by
          rw [show 1 + (1 + (expPair k).1 + alpha k * (expPair k).2) /
                  (2 * (1 + alpha k)) -
                ((1 + (expPair k).2) / 2 +
                  (1 + (expPair k).1 - (expPair k).2) * alpha k /
                    (2 * (1 + alpha k))) =
              (2 - ((expPair k).2 - (expPair k).1) * (1 - alpha k)) /
                (2 * (1 + alpha k)) by field_simp; ring]
          exact div_nonneg (by linarith) hden.le
        linarith

lemma constPair_second_one_le (b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b) (k : ℕ) :
    1 ≤ (constPair b P k).2 := by
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  induction k with
  | zero =>
      simpa [constPair] using one_le_bigM b P hP'
  | succ k ih =>
      have hA := (GrowingLocalizedLog.constPair_nonneg b P k).1
      have hα0 := GrowingLocalizedLog.alpha_pos k
      have hα1 := alpha_lt_one k
      have hsqrt := one_le_step_sqrt_constants b P hP'
        (constPair b P k).1 (constPair b P k).2 (alpha k) (alpha k)
        hA ih hα0 hα0 hα1
      simpa only [constPair] using hsqrt.2

lemma sum_Icc_ePhase_eq_sum_range_phase (b m N : ℕ) (a : ℤ) :
    (∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)) =
      ∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [phase_eq_ePhase]
  norm_num
  congr 2
  ring

/-- **Vandehey, Theorem 5.1**, proved. -/
theorem vandeheyThm51_holds : VandeheyThm51 := by
  intro b hb P hP m hm hsupp a ha k
  induction k generalizing m a with
  | zero =>
      intro N _hN
      exact vandeheyThm51_k_zero b hb P hP m hm hsupp a ha N
  | succ k ih =>
      intro N hN
      have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
      have hbm : Nat.Coprime b m := by
        apply Nat.coprime_of_dvd
        intro p hp hpb hpm
        exact ((hp.coprime_iff_not_dvd).mp (hP p (hsupp p hp hpm)).2) hpb
      obtain ⟨hA, hB0⟩ := GrowingLocalizedLog.constPair_nonneg b P k
      have hB1 : 1 ≤ (constPair b P k).2 := constPair_second_one_le b P hP k
      obtain ⟨hγ0, hγ1, hν1, hν2, hgap⟩ := expPair_bounds k
      have hα0 : 0 < alpha k := GrowingLocalizedLog.alpha_pos k
      have hα1 : alpha k < 1 := alpha_lt_one k
      have hr0 : 0 ≤ (2 : ℝ) ^ (-(k : ℝ)) := by positivity
      have hbound : ∀ (q : ℕ) (c : ℤ) (T : ℕ), q ≠ 0 → q ∣ m → T ≤ N →
          IsCoprime c (q : ℤ) →
          ‖∑ j ∈ range T, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
            ((constPair b P k).1 * (q : ℝ) ^ alpha k *
                (T : ℝ) ^ (expPair k).1 +
              (constPair b P k).2 * (q : ℝ) ^ (-alpha k) *
                (T : ℝ) ^ (expPair k).2) *
              (1 + Real.log q) ^ ((2 : ℝ) ^ (-(k : ℝ))) := by
        intro q c T hq hqdvd hTN hc
        have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
        have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
        have hlogq : 0 ≤ 1 + Real.log q := by
          have := Real.log_nonneg hq1R
          linarith
        by_cases hT0 : T = 0
        · subst T
          simp only [range_zero, sum_empty, norm_zero, Nat.cast_zero]
          exact mul_nonneg (add_nonneg (by positivity) (by positivity))
            (Real.rpow_nonneg hlogq _)
        · by_cases hqone : q = 1
          · subst q
            have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
            have hT1R : (1 : ℝ) ≤ T := by exact_mod_cast hT1
            have hTpow : (T : ℝ) ≤ (T : ℝ) ^ (expPair k).2 := by
              calc
                (T : ℝ) = (T : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (T : ℝ) ^ (expPair k).2 :=
                  Real.rpow_le_rpow_of_exponent_le hT1R hν1
            have hsmall :
                ‖∑ j ∈ range T, phase 1 c ((b : ℤ) ^ (j + 1))‖ ≤
                  (constPair b P k).1 * (T : ℝ) ^ (expPair k).1 +
                    (constPair b P k).2 * (T : ℝ) ^ (expPair k).2 := by
              calc
                ‖∑ j ∈ range T, phase 1 c ((b : ℤ) ^ (j + 1))‖ ≤ (T : ℝ) :=
                  norm_power_sum_range_le b 1 T c
                _ ≤ (constPair b P k).2 * (T : ℝ) ^ (expPair k).2 := by
                  calc
                    (T : ℝ) ≤ (T : ℝ) ^ (expPair k).2 := hTpow
                    _ = 1 * (T : ℝ) ^ (expPair k).2 := by ring
                    _ ≤ (constPair b P k).2 * (T : ℝ) ^ (expPair k).2 :=
                      mul_le_mul_of_nonneg_right hB1 (by positivity)
                _ ≤ (constPair b P k).1 * (T : ℝ) ^ (expPair k).1 +
                    (constPair b P k).2 * (T : ℝ) ^ (expPair k).2 := by
                  have hfirst : 0 ≤
                      (constPair b P k).1 * (T : ℝ) ^ (expPair k).1 := by
                    exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
                  linarith
            simpa using hsmall
          · have hq2 : 2 ≤ q := by omega
            have hsuppq : ∀ p, p.Prime → p ∣ q → p ∈ P := by
              intro p hp hpdvd
              exact hsupp p hp (dvd_trans hpdvd hqdvd)
            have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
            have hprev := ih q hq2 hsuppq c hc T hT1
            rw [sum_Icc_ePhase_eq_sum_range_phase] at hprev
            exact hprev
      have hstep := norm_power_sum_le_step b m N a hb hm hbm ha P hP hsupp
        (constPair b P k).1 (constPair b P k).2 (alpha k)
        (expPair k).1 (alpha k) (expPair k).2 ((2 : ℝ) ^ (-(k : ℝ)))
        hA hB1 hγ0 hγ1 hν1 hν2 hgap hr0 hα0 hα0 hα1 hN hbound
      have hcombine :
          (constPair b P k).2 * cP P (alpha k) +
              (constPair b P k).1 * cP P (alpha k) =
            ((constPair b P k).1 + (constPair b P k).2) * cP P (alpha k) := by
        ring
      rw [hcombine] at hstep
      rw [sum_Icc_ePhase_eq_sum_range_phase]
      simpa only [constPair, alpha_succ, GrowingLocalizedLog.expPair_succ,
        two_rpow_neg_succ, mul_assoc, neg_div] using hstep

/-- **Theorem A, unconditional.**  Every nonzero rational combination of Stoneham constants
`α_{b^{mᵢ}, cᵢ}` with the `cᵢ` pairwise coprime and coprime to `b` is `b`-normal. -/
theorem isNormal_stonehamCombination_unconditional
    (b : ℕ) (hb : 2 ≤ b) {r : ℕ} (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i) (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) :=
  StonehamSumsNormal.isNormal_stonehamCombination vandeheyThm51_holds b hb c m q hc hcop hcb hm hq

/-- **`α₂,₃ + α₂,₅` is normal in base 2**, unconditionally. -/
theorem isNormal_two_stoneham_three_add_five_unconditional :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 5) :=
  StonehamSumsNormal.isNormal_two_stoneham_three_add_five vandeheyThm51_holds

/-- **`ζ_Y` is normal**, unconditionally (was conditional on `VandeheyThm51`). -/
theorem zetaY_isNormal_unconditional
    (Y : ℕ → ℕ) (hmono : Monotone Y) (h3 : ∀ m, 3 ≤ Y m) (ε : ℝ) (hε : 0 < ε)
    (hY : ∀ᶠ n : ℕ in Filter.atTop,
      ((Y n).primeCounting : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.log n)) :
    IsNormal 2 (GrowingLocalizedLog.zetaY Y) :=
  GrowingLocalizedLog.zetaY_isNormal vandeheyThm51_holds Y hmono h3 ε hε hY

end NormalNumbers.VandeheyProof
