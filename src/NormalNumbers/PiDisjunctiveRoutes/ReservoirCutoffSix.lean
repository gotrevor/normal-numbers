/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffReview

/-! # Cutoff-six exits are not uniformly `O(1/n)` modulo one

For primes `p = 120m+89` and `n = 20m+14`, the full cutoff-six exit sum
`rationalExit 6 n` has exactly one term, equal to `2^(20m+18)/p`
(`rationalExit_six_eq`).  Its numerator `A` satisfies `A³ ≡ 1024 (mod p)`
(Euler's criterion, `p ≡ 1 mod 8`), and 1024 is not a cube, so every
integer `b ≡ A` has `|b|³ + 1024 ≥ p`.  With Dirichlet (mathlib) this gives
`exit_six_not_eventually_small`.  The lower bound `≈ p^{-2/3}` tends to zero:
this does NOT decide vanishing vs nonvanishing (`ExitSixNonvanishing`, next file).
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

open CutoffReview

/-- Exact one-term identification of the cutoff-six exit at `n = 20m+14`. -/
theorem rationalExit_six_eq (m : ℕ) (hp : Nat.Prime (120*m+89)) :
    rationalExit 6 (20*m+14) = (2:ℚ)^(20*m+18) / (120*m+89) := by
  unfold rationalExit
  rw [Finset.sum_eq_single (15*m+11)]
  · rw [if_pos ⟨by convert hp using 1; ring, by omega, by omega⟩,
      if_neg (by omega)]
    rw [show 20*m+14+1-(15*m+11) = 5*m+4 by omega]
    push_cast
    rw [show (8*((15*m:ℚ)+11)+1) = 120*m+89 by ring,
      show (16:ℚ) = 2^4 by norm_num, ← pow_mul,
      show (2:ℚ)^(20*m+18) = 2^(4*(5*m+4)) * 4 by
        rw [show 20*m+18 = 4*(5*m+4)+2 by ring, pow_add]; norm_num]
    ring
  · intro j _ hj
    rw [if_neg (by omega), if_neg]
    · simp
    rintro ⟨hpr, h1, h2⟩
    have : 8*j+5 = 5*(24*m+17) := by omega
    rw [this] at hpr
    exact Nat.not_prime_mul (by norm_num) (by omega) hpr
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- The exit numerator cubed is `1024` modulo `p` (`p = 120m+89` prime). -/
theorem dvd_cube_sub (m : ℕ) (hp : Nat.Prime (120*m+89)) (b : ℤ)
    (hb : (b : ZMod (120*m+89)) = 2^(20*m+18)) :
    ((120*m+89 : ℕ) : ℤ) ∣ b^3 - 1024 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have he := two_pow_half_eq (p := 120*m+89) (by omega)
  rw [if_pos (by omega), show (120*m+89)/2 = 60*m+44 by omega] at he
  push_cast
  rw [hb, ← pow_mul, show (20*m+18)*3 = 60*m+44+10 by ring, pow_add, he]
  norm_num

lemma cube_ne_1024 (b : ℤ) : b^3 ≠ 1024 := by
  intro h
  rcases le_or_gt b 10 with h1 | h1
  · nlinarith [sq_nonneg b, sq_nonneg (b-10), sq_nonneg (b+10)]
  · nlinarith [sq_nonneg b, sq_nonneg (b-11)]

/-- Any integer congruent to the exit numerator is large: `p ≤ |b|³ + 1024`. -/
theorem le_abs_cube (m : ℕ) (hp : Nat.Prime (120*m+89)) (b : ℤ)
    (hb : (b : ZMod (120*m+89)) = 2^(20*m+18)) :
    ((120*m+89 : ℕ) : ℤ) ≤ |b|^3 + 1024 := by
  obtain ⟨c, hc⟩ := dvd_cube_sub m hp b hb
  have hc0 : c ≠ 0 := by
    rintro rfl; exact cube_ne_1024 b (by linarith)
  have : ((120*m+89 : ℕ) : ℤ) ≤ |b^3 - 1024| := by
    rw [hc, abs_mul]
    have : (1:ℤ) ≤ |c| := Int.one_le_abs hc0
    have : (0:ℤ) ≤ ((120*m+89 : ℕ) : ℤ) := by positivity
    rw [abs_of_nonneg this]; nlinarith
  calc _ ≤ |b^3 - 1024| := this
    _ ≤ |b^3| + |(1024:ℤ)| := abs_sub _ _
    _ = |b|^3 + 1024 := by rw [abs_pow]; norm_num

/-- **First theorem.**  The full cutoff-six exit transfer is not eventually
`O(1/n)` modulo one: for every `C > 0` and every `N` there is `n ≥ N` with
`‖E₆(n)‖ℤ > C/(n+1)`.  Uses mathlib's Dirichlet theorem (primes `≡ 89 mod 120`). -/
@[blueprint (title := "Cutoff-six exit transfers are not uniformly O(1/n) mod 1")]
theorem exit_six_not_eventually_small (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∃ n ≥ N, C / (n + 1) <
      |(rationalExit 6 n : ℝ) - round (rationalExit 6 n : ℝ)| := by
  obtain ⟨K, hK⟩ := exists_nat_gt (6*C)
  obtain ⟨p, hpB, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq
    (6*N + K^3 + 1024) (q := 120) (a := 89) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; rfl)
  have hp120 : p % 120 = 89 := by
    have := hpmod; rw [Int.ModEq] at this; omega
  obtain ⟨m, rfl⟩ : ∃ m, p = 120*m+89 := ⟨p/120, by omega⟩
  refine ⟨20*m+14, by omega, ?_⟩
  rw [rationalExit_six_eq m hp]
  set x : ℝ := (((2:ℚ)^(20*m+18) / (120*m+89) : ℚ) : ℝ) with hx
  set z : ℤ := round x
  set b : ℤ := 2^(20*m+18) - z*(120*m+89 : ℕ)
  have hb : (b : ZMod (120*m+89)) = 2^(20*m+18) := by
    simp only [b, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, sub_zero, Int.cast_pow, Int.cast_ofNat]
  have hcube := le_abs_cube m hp b hb
  have hbK : (K:ℤ) < |b| := by
    by_contra h; push Not at h
    have h0 : 0 ≤ |b| := abs_nonneg b
    have : |b|^3 ≤ (K:ℤ)^3 := pow_le_pow_left₀ h0 h 3
    have : ((120*m+89 : ℕ):ℤ) > (K:ℤ)^3 + 1024 := by exact_mod_cast (by omega : 120*m+89 > K^3+1024)
    linarith
  have hbR : 6*C < |(b:ℝ)| := by
    have : ((K:ℤ):ℝ) < ((|b|:ℤ):ℝ) := by exact_mod_cast hbK
    push_cast at this; linarith
  have hP : (0:ℝ) < 120*m+89 := by positivity
  have hxz : x - z = (b:ℝ) / (120*m+89) := by
    simp only [hx, b]; push_cast; field_simp
  rw [hxz, abs_div, abs_of_pos hP]
  have hn : ((20*m+14 : ℕ) : ℝ) + 1 = (120*m+90)/6 := by push_cast; ring
  rw [hn, div_div_eq_mul_div, div_lt_div_iff₀ (by positivity) hP]
  clear_value x z b
  generalize |(b:ℝ)| = B at hbR ⊢
  generalize (m:ℝ) = M at hP ⊢
  have h1 := mul_lt_mul_of_pos_right hbR hP
  linarith only [h1, hbR, hC]

#print axioms exit_six_not_eventually_small

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
