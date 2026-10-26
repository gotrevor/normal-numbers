/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSixStep

/-!
# What the reservoir recurrence does and does not determine

An exact homogeneous shift preserves the full residual recurrence and the
actual reservoir, exits, entries, and BBP kicks.  Its initial value changes.
Conversely the recurrence together with initial value zero is rigid.

A second comparison uses dyadic residuals.  They are integral at every odd
prime, so adding them preserves every nonintegral odd-prime pole of the
reservoir.  Nevertheless they can approximate any prescribed real head
sequence with arbitrarily small pointwise errors.  This comparison does NOT
preserve the exact BBP forcing; the defect is bounded explicitly below.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

/-- A comparison preserving the exact forcing, with a shifted initial value. -/
noncomputable def shiftedResidual (s : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  residualS s n + 16^n * (x - Real.pi)

theorem shiftedResidual_succ (s : ℕ) (x : ℝ) (n : ℕ) :
    shiftedResidual s x (n+1) = 16 * shiftedResidual s x n +
      exitS s n + 16 * bbpKick n - entryS s n := by
  simp only [shiftedResidual, residualS_succ, pow_succ]
  ring

theorem shiftedResidual_zero (s : ℕ) (x : ℝ) :
    shiftedResidual s x 0 = x - Real.pi := by
  simp [shiftedResidual, residualS, reservoirS, piPartial]

@[blueprint (title := "Exact reservoir forcing permits any orbit when the initial residual is free")]
theorem shiftedResidual_shadow (s : ℕ) (x : ℝ) (n : ℕ) :
    reservoirS s n + shiftedResidual s x n + 16^n * piTail n = 16^n * x := by
  simp only [shiftedResidual, residualS, piTail]
  ring

/-- Classification of all solutions, including their initial-value dependence. -/
theorem residual_recurrence_classification (s : ℕ) (S : ℕ → ℝ)
    (hS : ∀ n, S (n+1) = 16 * S n + exitS s n + 16 * bbpKick n - entryS s n)
    (n : ℕ) : S n = residualS s n + 16^n * S 0 := by
  induction n with
  | zero => simp [residualS, reservoirS, piPartial]
  | succ n ih => rw [hS, ih, residualS_succ, pow_succ]; ring

@[blueprint (title := "The exact BBP residual recurrence and zero seed determine the genuine residual")]
theorem residual_recurrence_rigid (s : ℕ) (S : ℕ → ℝ) (h0 : S 0 = 0)
    (hS : ∀ n, S (n+1) = 16 * S n + exitS s n + 16 * bbpKick n - entryS s n) :
    S = residualS s := by
  funext n
  simpa [h0] using residual_recurrence_classification s S hS n

/-- Dyadic rationals approximate any real, with an explicit denominator form. -/
theorem exists_dyadic_close (y ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℤ, ∃ k : ℕ, |(m : ℝ) / 2^k - y| < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
  have hd : (0 : ℝ) < 2^k := by positivity
  have hs : (1 : ℝ) / 2^k < ε := by simpa only [div_pow, one_pow] using hk
  have hmul : (1 : ℝ) < ε * 2^k := (div_lt_iff₀ hd).mp hs
  refine ⟨⌊y * 2^k⌋, k, ?_⟩
  have hlo := Int.floor_le (y * 2^k)
  have hhi := Int.lt_floor_add_one (y * 2^k)
  rw [abs_sub_lt_iff]
  constructor
  · have : (⌊y * 2^k⌋ : ℝ) / 2^k < y + ε :=
      (div_lt_iff₀ hd).mpr (by nlinarith)
    linarith
  · have : y - ε < (⌊y * 2^k⌋ : ℝ) / 2^k :=
      (lt_div_iff₀ hd).mpr (by nlinarith)
    linarith

theorem dyadic_padicNorm_le_one (m : ℤ) (k p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    padicNorm p ((m : ℚ) / 2^k) ≤ 1 := by
  have hp : Nat.Prime p := Fact.out
  have h2 : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hpow : padicNorm p ((2 : ℚ)^k) = 1 := by
    have hn := (padicNorm.nat_eq_one_iff (p := p) (2^k)).mpr
      (fun h => h2 (hp.dvd_of_dvd_pow h))
    simpa using hn
  rw [padicNorm.div, hpow, div_one]
  simpa using padicNorm.of_int (p := p) m

theorem dyadic_add_preserves_pole (R : ℚ) (m : ℤ) (k p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hR : 1 < padicNorm p R) :
    padicNorm p (R + (m : ℚ) / 2^k) = padicNorm p R := by
  have hD := dyadic_padicNorm_le_one m k p hp2
  rw [padicNorm.add_eq_max_of_ne (by linarith), max_eq_left (by linarith)]

/-- The entire odd-prime pole data is compatible with an arbitrary real head.
No independence, randomness, or numerical approximation hypothesis is used. -/
@[blueprint (title := "Rational residuals preserve all odd-prime poles while shadowing any prescribed head")]
theorem exists_rational_residual_shadow (R : ℕ → ℚ) (T ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) :
    ∃ S : ℕ → ℚ, ∀ n,
      |((R n + S n : ℚ) : ℝ) - T n| < ε n ∧
      ∀ p : ℕ, Nat.Prime p → p ≠ 2 → 1 < padicNorm p (R n) →
        padicNorm p (R n + S n) = padicNorm p (R n) := by
  classical
  have hex : ∀ n, ∃ m : ℤ, ∃ k : ℕ,
      |(m : ℝ) / 2^k - (T n - (R n : ℝ))| < ε n :=
    fun n => exists_dyadic_close _ _ (hε n)
  choose m k hmk using hex
  refine ⟨fun n => (m n : ℚ) / 2^(k n), fun n => ⟨?_, ?_⟩⟩
  · push_cast
    convert hmk n using 1
    congr 1
    ring
  · intro p hp hp2 hR
    letI : Fact p.Prime := ⟨hp⟩
    exact dyadic_add_preserves_pole _ _ _ _ hp2 hR

/-- Pointwise shadow errors give an explicit error in the expanding recurrence. -/
theorem forcing_defect_bound (A T ε : ℕ → ℝ) (h : ∀ n, |A n - T n| < ε n)
    (n : ℕ) :
    |(A (n+1) - 16*A n) - (T (n+1) - 16*T n)| < ε (n+1) + 16*ε n := by
  calc
    _ = |(A (n+1) - T (n+1)) - 16*(A n - T n)| := by congr 1; ring
    _ ≤ |A (n+1) - T (n+1)| + |16*(A n - T n)| := abs_sub _ _
    _ = |A (n+1) - T (n+1)| + 16*|A n - T n| := by rw [abs_mul]; norm_num
    _ < _ := by linarith [h n, h (n+1)]

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
