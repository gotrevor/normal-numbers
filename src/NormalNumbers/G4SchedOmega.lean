/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaWitness
import NormalNumbers.G4SchedBEAssembly
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Size arithmetic for the `Ω` schedule

The two `Ω`-specific §4D fields of `ScheduleWitnessΩ` (`hjunk`, `hfar`) are pure size
arithmetic in the schedule parameters.  The one non-obvious input is the frozen sum

  `T(P₀) = ∑_{p ∣ P₀} 1/(p−1)`,

which must be **log log**-size, not `ω(P₀)`-size: the junk term is multiplied by `rowL1 b K`,
which only decays like `(2/3)^K`, while `ω(P₀)` is super-exponential in `K`.  The saving is that
the `j`-th smallest prime factor is at least `j + 2`, so `T(P₀) ≤ harmonic ω(P₀) ≤ 1 + log ω(P₀)`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- A finset of positive naturals has reciprocal sum at most the harmonic number of its size:
the `j`-th smallest element is at least `j+1`. -/
theorem sum_inv_le_harmonic : ∀ (n : ℕ) (B : Finset ℕ), B.card = n → 0 ∉ B →
    ∑ k ∈ B, (1 : ℝ) / k ≤ (harmonic n : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro B hB _
      rw [Finset.card_eq_zero.1 hB]
      simp
  | succ n ih =>
      intro B hB h0
      have hne : B.Nonempty := Finset.card_pos.1 (by omega)
      set M := B.max' hne with hM
      have hMmem : M ∈ B := B.max'_mem hne
      have hsub : B ⊆ Finset.Icc 1 M := by
        intro k hk
        refine Finset.mem_Icc.2 ⟨?_, B.le_max' k hk⟩
        rcases Nat.eq_zero_or_pos k with h | h
        · exact absurd (h ▸ hk) h0
        · exact h
      have hcard : n + 1 ≤ M := by
        have := Finset.card_le_card hsub
        rw [hB, Nat.card_Icc] at this
        omega
      have herase : (B.erase M).card = n := by
        rw [Finset.card_erase_of_mem hMmem, hB]
        omega
      have h0' : 0 ∉ B.erase M := fun h => h0 (Finset.mem_of_mem_erase h)
      have hih := ih (B.erase M) herase h0'
      have hMr : ((n : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hcard
      have hMpos : (0 : ℝ) < M := by linarith [(by positivity : (0:ℝ) ≤ (n:ℝ))]
      have hsplit : ∑ k ∈ B, (1 : ℝ) / k = 1 / M + ∑ k ∈ B.erase M, (1 : ℝ) / k :=
        (Finset.add_sum_erase _ _ hMmem).symm
      have hterm : (1 : ℝ) / M ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hMr
      have hhs : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
        rw [harmonic_succ]
        push_cast
        rw [inv_eq_one_div]
      rw [hsplit, hhs]
      linarith

/-- **`∑_{p ∣ N} 1/(p−1) ≤ harmonic ω(N)`.** -/
theorem sum_inv_sub_one_primeFactors_le (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ (harmonic N.primeFactors.card : ℝ) := by
  classical
  set B := N.primeFactors.image (fun p => p - 1) with hB
  have hinj : Set.InjOn (fun p => p - 1) N.primeFactors := by
    intro p hp q hq hpq
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
    simp only at hpq
    omega
  have hcard : B.card = N.primeFactors.card := Finset.card_image_of_injOn hinj
  have h0 : 0 ∉ B := by
    rw [hB]
    intro h
    obtain ⟨p, hp, hp0⟩ := Finset.mem_image.1 h
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have heq : ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) = ∑ k ∈ B, (1 : ℝ) / k := by
    rw [hB, Finset.sum_image (fun p hp q hq h => hinj hp hq h)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    congr 1
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [heq, ← hcard]
  exact sum_inv_le_harmonic B.card B rfl h0

/-- The `log log` form. -/
theorem sum_inv_sub_one_primeFactors_le_log (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ 1 + Real.log (N.primeFactors.card) :=
  (sum_inv_sub_one_primeFactors_le N).trans (harmonic_le_one_add_log _)

/-! ### The junk bound divided by the sample size -/

/-- **`junkShiftBound / |P|` in two clean pieces.**  The frozen piece is `log log`-size; the
`√X` piece carries the `P₀/√X` factor that the free cutoff `e` makes arbitrarily small. -/
theorem junkShiftBound_div_le {P₀ X ρmax : ℕ} (hP₀ : 0 < P₀) (hX : 0 < X) {c : ℝ} (hc : 0 < c)
    (hcard : (X : ℝ) / (2 * P₀) ≤ c) :
    junkShiftBound P₀ X ρmax / c
      ≤ 2 * (2 + Real.log (P₀.primeFactors.card))
        + (2 * P₀ / X) * (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hinv : 1 / c ≤ 2 * P₀ / X := by
    rw [div_le_div_iff₀ hc (by positivity)]
    have : (X : ℝ) / (2 * P₀) * (2 * P₀) ≤ c * (2 * P₀) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    rw [div_mul_cancel₀ _ (by positivity : (2 * (P₀ : ℝ)) ≠ 0)] at this
    linarith
  have hjb0 : 0 ≤ junkShiftBound P₀ X ρmax := junkShiftBound_nonneg _ _ _
  have hstep : junkShiftBound P₀ X ρmax / c ≤ junkShiftBound P₀ X ρmax * (2 * P₀ / X) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv hjb0
  have hexp : junkShiftBound P₀ X ρmax * (2 * P₀ / X)
      = ((X : ℝ) / P₀ * (2 * P₀ / X)) * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
        + (2 * P₀ / X) * (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by
    unfold junkShiftBound
    ring
  have he : (X : ℝ) / P₀ * (2 * P₀ / X) = 2 := by field_simp
  have hT := sum_inv_sub_one_primeFactors_le_log P₀
  rw [hexp, he] at hstep
  linarith

/-- **The `√X` piece of the junk average is at most `1`** once `X` dominates
`P₀ · √X · log₂ X` — which the free cutoff `e` arranges, since `X = 2^{100·2^{mE}}` while `P₀`
depends only on `K`. -/
theorem junk_sqrt_term_le {P₀ X ρmax : ℕ} (hX : 0 < X) (hρ : ρmax ≤ X)
    (hsize : 2 * P₀ * ((2 * Nat.sqrt X + 2) * (Nat.log 2 X + 1)) ≤ X) :
    (2 * (P₀ : ℝ) / X) * (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) ≤ 1 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  -- the numerator, in `ℕ`
  have hsq : Nat.sqrt (X + ρmax) ≤ 2 * Nat.sqrt X + 1 := by
    have h1 : Nat.sqrt (X + ρmax) ≤ Nat.sqrt (2 * X) := Nat.sqrt_le_sqrt (by omega)
    have h2 : Nat.sqrt (2 * X) < 2 * Nat.sqrt X + 2 := by
      rw [Nat.sqrt_lt']
      have := Nat.lt_succ_sqrt' X
      nlinarith [Nat.sqrt_le' X, this]
    omega
  have hlg : Nat.log 2 (X + ρmax) ≤ Nat.log 2 X + 1 := by
    have h1 : Nat.log 2 (X + ρmax) ≤ Nat.log 2 (X * 2) := Nat.log_mono_right (by omega)
    rwa [Nat.log_mul_base (by norm_num) (by omega)] at h1
  have hnum : (Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax)
      ≤ (2 * Nat.sqrt X + 2) * (Nat.log 2 X + 1) := Nat.mul_le_mul (by omega) hlg
  have hkey : 2 * P₀ * ((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax)) ≤ X :=
    le_trans (Nat.mul_le_mul_left _ hnum) hsize
  have hkeyr : 2 * (P₀ : ℝ) * (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ)
      ≤ (X : ℝ) := by exact_mod_cast hkey
  rw [div_mul_eq_mul_div, div_le_one hXr]
  linarith

/-- **The junk average, in one number**: `5 + 2 log ω(P₀)`. -/
theorem junkShiftBound_div_le' {P₀ X ρmax : ℕ} (hP₀ : 0 < P₀) (hX : 0 < X) (hρ : ρmax ≤ X)
    {c : ℝ} (hc : 0 < c) (hcard : (X : ℝ) / (2 * P₀) ≤ c)
    (hsize : 2 * P₀ * ((2 * Nat.sqrt X + 2) * (Nat.log 2 X + 1)) ≤ X) :
    junkShiftBound P₀ X ρmax / c ≤ 5 + 2 * Real.log (P₀.primeFactors.card) := by
  have h1 := junkShiftBound_div_le hP₀ hX hc hcard (ρmax := ρmax)
  have h2 := junk_sqrt_term_le (P₀ := P₀) (X := X) (ρmax := ρmax) hX hρ hsize
  linarith

/-- `100000 k³ ≤ 2^k` for `k ≥ 40`. -/
lemma cube_le_two_pow : ∀ {k : ℕ}, 40 ≤ k → 100000 * k ^ 3 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 40 with hn | hn
      · have hn40 : n = 39 := by omega
        subst hn40
        norm_num
      · have hih := ih hn
        have hstep : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
          have h40 : 40 ≤ n := hn
          nlinarith [sq_nonneg n, sq_nonneg (n - 1)]
        calc 100000 * (n + 1) ^ 3 ≤ 100000 * (2 * n ^ 3) := by
              exact Nat.mul_le_mul_left _ hstep
          _ = 2 * (100000 * n ^ 3) := by ring
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ hih
          _ = 2 ^ (n + 1) := by ring

/-! ### The schedule instance of the size condition -/

namespace SchedB

open Sched (N J logP₀Nat)

variable {b K e : ℕ}

/-- **The junk size condition holds in the schedule.**  `X = 2^{100·2^{mE}}` while
`P₀ ≤ 2^{2·2^{mE}}`, so `2P₀·√X·log₂X ≤ 2^{53·2^{mE}+10} ≤ X`. -/
theorem junk_size_holdsE (h : HypE b K e) :
    2 * (gridOf K (N K) h.hK1).P₀ *
        ((2 * Nat.sqrt (XE K e) + 2) * (Nat.log 2 (XE K e) + 1)) ≤ XE K e := by
  set t := 2 ^ mE K e with ht
  have ht1 : 1 ≤ t := Nat.one_le_two_pow
  have hX : XE K e = 2 ^ (100 * t) := rfl
  have hsqrt : Nat.sqrt (XE K e) = 2 ^ (50 * t) := by
    have : XE K e = (2 ^ (50 * t)) ^ 2 := by
      rw [hX, ← pow_mul]
      congr 1
      omega
    rw [this, Nat.sqrt_eq']
  have hlog : Nat.log 2 (XE K e) = 100 * t := by rw [hX, Nat.log_pow (by norm_num)]
  have hP₀ : (gridOf K (N K) h.hK1).P₀ ≤ 2 ^ (2 * t) := by
    have := P₀_le_two_powE h
    rw [← ht] at this
    exact_mod_cast this
  rw [hsqrt, hlog, hX]
  have h1 : 2 * 2 ^ (50 * t) + 2 ≤ 2 ^ (50 * t + 2) := by
    have : (2 : ℕ) ≤ 2 ^ (50 * t) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (50 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * 2 ^ (50 * t) + 2 ≤ 2 * 2 ^ (50 * t) + 2 * 2 ^ (50 * t) := by omega
      _ = 4 * 2 ^ (50 * t) := by ring
      _ = 2 ^ (50 * t + 2) := by rw [pow_add]; ring
  have htt : t ≤ 2 ^ t := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : 100 * t + 1 ≤ 2 ^ (t + 7) := by
    calc 100 * t + 1 ≤ 128 * t := by omega
      _ ≤ 128 * 2 ^ t := by exact Nat.mul_le_mul_left _ htt
      _ = 2 ^ (t + 7) := by rw [pow_add]; ring
  calc 2 * (gridOf K (N K) h.hK1).P₀ * ((2 * 2 ^ (50 * t) + 2) * (100 * t + 1))
      ≤ 2 * 2 ^ (2 * t) * (2 ^ (50 * t + 2) * 2 ^ (t + 7)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ hP₀) (Nat.mul_le_mul h1 h2)
    _ = 2 ^ (53 * t + 10) := by
        rw [show (2 : ℕ) * 2 ^ (2 * t) * (2 ^ (50 * t + 2) * 2 ^ (t + 7))
            = 2 ^ 1 * 2 ^ (2 * t) * (2 ^ (50 * t + 2) * 2 ^ (t + 7)) by norm_num]
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
    _ ≤ 2 ^ (100 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)

end SchedB

end NormalNumbers.G4
