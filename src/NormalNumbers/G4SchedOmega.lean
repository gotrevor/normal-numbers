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
open scoped BigOperators ArithmeticFunction.Omega

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

/-- `√X ≤ Nat.sqrt X + 1`. -/
lemma real_sqrt_le_nat_sqrt_add_one (X : ℕ) :
    Real.sqrt (X : ℝ) ≤ ((Nat.sqrt X : ℕ) : ℝ) + 1 := by
  have h : (X : ℝ) ≤ (((Nat.sqrt X : ℕ) : ℝ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' X
    have : (X : ℝ) ≤ ((Nat.sqrt X + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast this.le
    push_cast at this
    linarith
  calc Real.sqrt (X : ℝ) ≤ Real.sqrt ((((Nat.sqrt X : ℕ) : ℝ) + 1) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = ((Nat.sqrt X : ℕ) : ℝ) + 1 := Real.sqrt_sq (by positivity)

/-- `log N / log 2 ≤ Nat.log 2 N + 1`. -/
lemma log_div_log_two_le (N : ℕ) :
    Real.log (N : ℝ) / Real.log 2 ≤ ((Nat.log 2 N : ℕ) : ℝ) + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h]
    simp only [Nat.cast_zero, Real.log_zero, zero_div]
    positivity
  · have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hltr : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by exact_mod_cast hlt.le
    have := Real.log_le_log (by exact_mod_cast h) hltr
    rw [Real.log_pow] at this
    rw [div_le_iff₀ hlog2]
    push_cast at this ⊢
    linarith

/-- `2^{ω(N)} ≤ N`. -/
theorem two_pow_card_primeFactors_le {N : ℕ} (hN : N ≠ 0) : 2 ^ N.primeFactors.card ≤ N := by
  calc 2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ N.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)

/-- `ω(N) · log 2 ≤ log N`. -/
theorem card_primeFactors_mul_log_two_le {N : ℕ} (hN : N ≠ 0) :
    (N.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := two_pow_card_primeFactors_le hN
  have hr : ((2 : ℝ)) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast h
  have := Real.log_le_log (by positivity) hr
  rwa [Real.log_pow] at this

/-! ### The schedule instance of the size condition -/

namespace SchedB

open Sched (N J logP₀Nat)

variable {b K e : ℕ}

/-- **The junk size condition holds in the schedule, with room to spare.**
`X = 2^{100·2^{mE}}` while `P₀ ≤ 2^{2·2^{mE}}`, so even `2^{20}·P₀·√X·log₂X ≤ X`. -/
theorem junk_size_holdsE' (h : HypE b K e) :
    2 ^ 20 * (gridOf K (N K) h.hK1).P₀ *
        ((2 * Nat.sqrt (XE K e) + 2) * (Nat.log 2 (XE K e) + 2)) ≤ XE K e := by
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
  have h2 : 100 * t + 2 ≤ 2 ^ (t + 7) := by
    calc 100 * t + 2 ≤ 128 * t := by omega
      _ ≤ 128 * 2 ^ t := by exact Nat.mul_le_mul_left _ htt
      _ = 2 ^ (t + 7) := by rw [pow_add]; ring
  calc 2 ^ 20 * (gridOf K (N K) h.hK1).P₀ * ((2 * 2 ^ (50 * t) + 2) * (100 * t + 2))
      ≤ 2 ^ 20 * 2 ^ (2 * t) * (2 ^ (50 * t + 2) * 2 ^ (t + 7)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ hP₀) (Nat.mul_le_mul h1 h2)
    _ = 2 ^ (53 * t + 29) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
    _ ≤ 2 ^ (100 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The form consumed by `hjunk`. -/
theorem junk_size_holdsE (h : HypE b K e) :
    2 * (gridOf K (N K) h.hK1).P₀ *
        ((2 * Nat.sqrt (XE K e) + 2) * (Nat.log 2 (XE K e) + 1)) ≤ XE K e := by
  refine le_trans ?_ (junk_size_holdsE' h)
  have h1 : Nat.log 2 (XE K e) + 1 ≤ Nat.log 2 (XE K e) + 2 := by omega
  have h2 : 2 * (gridOf K (N K) h.hK1).P₀ ≤ 2 ^ 20 * (gridOf K (N K) h.hK1).P₀ :=
    Nat.mul_le_mul_right _ (by norm_num)
  exact Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ h1)

/-- **`junkA / |P|`** is `log log`-size. -/
theorem junkA_div_le {P₀ X : ℕ} (hP₀ : 0 < P₀) (hX : 0 < X) {c : ℝ} (hc : 0 < c)
    (hcard : (X : ℝ) / (2 * P₀) ≤ c) :
    junkA P₀ X / c ≤ 2 * (2 + Real.log (P₀.primeFactors.card)) := by
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hinv : 1 / c ≤ 2 * P₀ / X := by
    rw [div_le_div_iff₀ hc (by positivity)]
    have : (X : ℝ) / (2 * P₀) * (2 * P₀) ≤ c * (2 * P₀) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    rw [div_mul_cancel₀ _ (by positivity : (2 * (P₀ : ℝ)) ≠ 0)] at this
    linarith
  have h0 : 0 ≤ junkA P₀ X := junkA_nonneg _ _
  have hstep : junkA P₀ X / c ≤ junkA P₀ X * (2 * P₀ / X) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv h0
  have he : (X : ℝ) / P₀ * (2 * P₀ / X) = 2 := by field_simp
  have hexp : junkA P₀ X * (2 * P₀ / X)
      = ((X : ℝ) / P₀ * (2 * P₀ / X)) * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1) := by
    unfold junkA
    ring
  rw [hexp, he] at hstep
  have hT := sum_inv_sub_one_primeFactors_le_log P₀
  linarith

/-- **`junkB / |P| ≤ 1`** under the size condition. -/
theorem junkB_div_le {P₀ X Dm : ℕ} (hP₀ : 0 < P₀) (hX : 1 ≤ X) (hDm : Dm ≤ X)
    {c : ℝ} (hc : 0 < c) (hcard : (X : ℝ) / (2 * P₀) ≤ c)
    (hsize : 2 ^ 20 * P₀ * ((2 * Nat.sqrt X + 2) * (Nat.log 2 X + 2)) ≤ X) :
    junkB X Dm / c ≤ 1 := by
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  set s : ℝ := ((Nat.sqrt X : ℕ) : ℝ) with hs
  set L : ℝ := ((Nat.log 2 X : ℕ) : ℝ) with hL
  have hs0 : 0 ≤ s := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hinv : 1 / c ≤ 2 * P₀ / X := by
    rw [div_le_div_iff₀ hc (by positivity)]
    have : (X : ℝ) / (2 * P₀) * (2 * P₀) ≤ c * (2 * P₀) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    rw [div_mul_cancel₀ _ (by positivity : (2 * (P₀ : ℝ)) ≠ 0)] at this
    linarith
  have hB0 : 0 ≤ junkB X Dm := junkB_nonneg _ _
  have hstep : junkB X Dm / c ≤ junkB X Dm * (2 * P₀ / X) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv hB0
  -- bound `junkB` itself
  have hXD : ((X + Dm : ℕ) : ℝ) ≤ 2 * X := by
    have : X + Dm ≤ 2 * X := by omega
    exact_mod_cast this
  have hsq : Real.sqrt ((X + Dm : ℕ) : ℝ) + 1 ≤ 2 * (2 * s + 2) := by
    have h1 : Real.sqrt ((X + Dm : ℕ) : ℝ) ≤ Real.sqrt (4 * (X : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * (X : ℝ)) = 2 * Real.sqrt (X : ℝ) := by
      rw [show (4 : ℝ) * X = 2 ^ 2 * X by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have h3 : Real.sqrt (X : ℝ) ≤ s + 1 := real_sqrt_le_nat_sqrt_add_one X
    rw [h2] at h1
    linarith
  have hlg : Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 + 1 ≤ 2 * (L + 2) := by
    have h1 : Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 ≤ L + 2 := by
      have h2 := log_div_log_two_le (X + Dm)
      have h3 : Nat.log 2 (X + Dm) ≤ Nat.log 2 X + 1 := by
        have h4 : Nat.log 2 (X + Dm) ≤ Nat.log 2 (X * 2) := Nat.log_mono_right (by omega)
        rwa [Nat.log_mul_base (by norm_num) (by omega)] at h4
      have h3' : ((Nat.log 2 (X + Dm) : ℕ) : ℝ) ≤ L + 1 := by
        rw [hL]; exact_mod_cast h3
      linarith
    linarith
  have hjb : junkB X Dm ≤ 4 * ((2 * (2 * s + 2)) * (2 * (L + 2))) := by
    unfold junkB
    have h1 : 0 ≤ Real.sqrt ((X + Dm : ℕ) : ℝ) + 1 := by positivity
    have h2 : 0 ≤ Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 + 1 := by
      have : 0 ≤ Real.log ((X + Dm : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X + Dm))
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    calc 4 * (Real.sqrt ((X + Dm : ℕ) : ℝ) + 1) * (Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 + 1)
        = 4 * ((Real.sqrt ((X + Dm : ℕ) : ℝ) + 1) * (Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 + 1)) := by
          ring
      _ ≤ 4 * ((2 * (2 * s + 2)) * (2 * (L + 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hsq hlg h2 (by linarith)) (by norm_num)
  -- the size condition
  have hsizer : (2 : ℝ) ^ 20 * P₀ * ((2 * s + 2) * (L + 2)) ≤ X := by
    have : ((2 ^ 20 * P₀ * ((2 * Nat.sqrt X + 2) * (Nat.log 2 X + 2)) : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hsize
    push_cast at this
    rw [hs, hL]
    linarith
  have hfin : junkB X Dm * (2 * P₀ / X) ≤ 1 := by
    have hpos : (0 : ℝ) < 2 * P₀ / X := by positivity
    have h1 : junkB X Dm * (2 * P₀ / X)
        ≤ (4 * ((2 * (2 * s + 2)) * (2 * (L + 2)))) * (2 * P₀ / X) :=
      mul_le_mul_of_nonneg_right hjb hpos.le
    refine h1.trans ?_
    have hexp : 4 * ((2 * (2 * s + 2)) * (2 * (L + 2))) * (2 * P₀ / X)
        = (32 * ((P₀ : ℝ) * ((2 * s + 2) * (L + 2)))) / X := by
      field_simp
      ring
    rw [hexp, div_le_one hXr]
    nlinarith [hsizer, (by positivity : (0:ℝ) ≤ (P₀ : ℝ) * ((2 * s + 2) * (L + 2)))]
  linarith

/-! ### Power-of-two bookkeeping for the far pieces -/

lemma eight_mul_le_two_pow : ∀ {K : ℕ}, 8 ≤ K → 8 * K ≤ 2 ^ K := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 8 with hn | hn
      · have : n = 7 := by omega
        subst this
        norm_num
      · have := ih hn
        have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        omega

lemma half_pow_mul_two_pow {m c : ℕ} (h : c ≤ m) :
    ((1 : ℝ) / 2) ^ m * (2 : ℝ) ^ c = ((1 : ℝ) / 2) ^ (m - c) := by
  have hm : m = (m - c) + c := by omega
  rw [hm, pow_add]
  have : ((1 : ℝ) / 2) ^ c * (2 : ℝ) ^ c = 1 := by
    rw [← mul_pow]
    norm_num
  rw [show ((1 : ℝ) / 2) ^ (m - c + c - c) = ((1:ℝ)/2) ^ (m - c) by congr 1; omega]
  nlinarith [this, (by positivity : (0:ℝ) < ((1:ℝ)/2) ^ (m - c))]

/-- The target shape: `(1/2)^D ≤ (1/8)·(1/K)·2^{−k₄}` once `D ≥ k₄ + K`. -/
lemma half_pow_le_target {K k₄ D : ℕ} (hK : 100 ≤ K) (hD : k₄ + K ≤ D) :
    ((1 : ℝ) / 2) ^ D ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hKr : (0 : ℝ) < K := by positivity
  have hKr' : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have h8 : 8 * K ≤ 2 ^ K := eight_mul_le_two_pow (by omega)
  have h8r : (8 : ℝ) * K ≤ (2 : ℝ) ^ K := by exact_mod_cast h8
  have hsplit : ((1 : ℝ) / 2) ^ D ≤ ((1 : ℝ) / 2) ^ (k₄ + K) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
  have hKpow : ((1 : ℝ) / 2) ^ K ≤ 1 / (8 * K) := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ((1 : ℝ) / 2) ^ D ≤ ((1 : ℝ) / 2) ^ (k₄ + K) := hsplit
    _ = ((1 : ℝ) / 2) ^ k₄ * ((1 : ℝ) / 2) ^ K := by rw [pow_add]
    _ ≤ ((1 : ℝ) / 2) ^ k₄ * (1 / (8 * K)) := by
        exact mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by field_simp

/-- A version with room: `(1/2)^D ≤ (1/64)·(1/K)·2^{−k₄}` once `D ≥ k₄ + 2K`. -/
lemma half_pow_le_target' {K k₄ D : ℕ} (hK : 100 ≤ K) (hD : k₄ + 2 * K ≤ D) :
    ((1 : ℝ) / 2) ^ D ≤ (1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hKr : (0 : ℝ) < K := by positivity
  have hKr' : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have h8 : 8 * K ≤ 2 ^ K := eight_mul_le_two_pow (by omega)
  have h8r : (8 : ℝ) * K ≤ (2 : ℝ) ^ K := by exact_mod_cast h8
  have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hsplit : ((1 : ℝ) / 2) ^ D ≤ ((1 : ℝ) / 2) ^ (k₄ + 2 * K) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
  have hKpow : ((1 : ℝ) / 2) ^ (2 * K) ≤ 1 / (64 * K) := by
    rw [one_div_pow, pow_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : ((2 : ℝ) ^ 2) ^ K = ((2 : ℝ) ^ K) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h4]
    nlinarith [h8r, hpos, hKr]
  calc ((1 : ℝ) / 2) ^ D ≤ ((1 : ℝ) / 2) ^ (k₄ + 2 * K) := hsplit
    _ = ((1 : ℝ) / 2) ^ k₄ * ((1 : ℝ) / 2) ^ (2 * K) := by rw [pow_add]
    _ ≤ ((1 : ℝ) / 2) ^ k₄ * (1 / (64 * K)) := by
        exact mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = (1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by field_simp

/-- `log ω(P₀) ≤ 15K²`. -/
theorem log_card_primeFactors_P₀_leE (h : HypE b K e) :
    Real.log (((gridOf K (N K) h.hK1).P₀.primeFactors.card : ℕ) : ℝ) ≤ 15 * (K : ℝ) ^ 2 := by
  have hK := h.base.hK
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set G := gridOf K (N K) h.hK1 with hG
  have hP₀0 : G.P₀ ≠ 0 := G.P₀_pos.ne'
  have hl2 : (0.6 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  -- `ω(P₀) ≤ 2 logP₀Nat K ≤ 2^{21K²+1}`
  have h1 := card_primeFactors_mul_log_two_le hP₀0
  have h2 : Real.log (G.P₀ : ℝ) ≤ (logP₀Nat K : ℝ) := by
    have hpos : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
    calc Real.log (G.P₀ : ℝ) ≤ Real.log (Real.exp (logP₀Nat K)) :=
          Real.log_le_log hpos (Sched.P₀_le_exp (by omega))
      _ = logP₀Nat K := Real.log_exp _
  have h3 : (logP₀Nat K : ℝ) ≤ (2 : ℝ) ^ (21 * K ^ 2) := by
    have := Sched.logP₀Nat_le_two_pow (K := K) (by omega)
    exact_mod_cast this
  have hcard : ((G.P₀.primeFactors.card : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (21 * K ^ 2) := by
    have hle : ((G.P₀.primeFactors.card : ℕ) : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ (21 * K ^ 2) := by
      linarith
    nlinarith [(by positivity : (0:ℝ) ≤ ((G.P₀.primeFactors.card : ℕ) : ℝ)),
      (by positivity : (0:ℝ) < (2:ℝ) ^ (21 * K ^ 2))]
  rcases Nat.eq_zero_or_pos G.P₀.primeFactors.card with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    positivity
  · have hlog := Real.log_le_log (by exact_mod_cast h0) hcard
    have hsplit : Real.log (2 * (2 : ℝ) ^ (21 * K ^ 2))
        = Real.log 2 + (21 * (K : ℝ) ^ 2) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hsplit] at hlog
    nlinarith [(by positivity : (0:ℝ) ≤ (K:ℝ) ^ 2)]

/-- `Ω(P₀) ≤ 2^{21K²+1}`. -/
theorem cardFactors_P₀_leE (h : HypE b K e) :
    ((Ω (gridOf K (N K) h.hK1).P₀ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (21 * K ^ 2 + 1) := by
  have hK := h.base.hK
  set G := gridOf K (N K) h.hK1 with hG
  have hP₀0 : G.P₀ ≠ 0 := G.P₀_pos.ne'
  have h1 : (2 : ℝ) ^ (Ω G.P₀) ≤ (G.P₀ : ℝ) := by
    have := PrimeLambert.two_pow_cardFactors_le hP₀0
    exact_mod_cast this
  have h2 : (G.P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := by
    refine (Sched.P₀_le_exp (K := K) (by omega)).trans ?_
    exact Sched.exp_nat_le_two_pow (logP₀Nat K)
  have h3 : logP₀Nat K ≤ 2 ^ (21 * K ^ 2) := Sched.logP₀Nat_le_two_pow (by omega)
  have hmono : (2 : ℝ) ^ (Ω G.P₀) ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := le_trans h1 h2
  have hexp : Ω G.P₀ ≤ 2 * logP₀Nat K :=
    (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 hmono
  have : Ω G.P₀ ≤ 2 ^ (21 * K ^ 2 + 1) := by
    calc Ω G.P₀ ≤ 2 * logP₀Nat K := hexp
      _ ≤ 2 * 2 ^ (21 * K ^ 2) := by omega
      _ = 2 ^ (21 * K ^ 2 + 1) := by rw [pow_succ]; ring
  exact_mod_cast this

/-- **The frozen geometric far piece.** -/
theorem hfar_frozen_leE {k₄ : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e) :
    (2 : ℝ) ^ K * (((Ω (gridOf K (N K) h.hK1).P₀ : ℕ) : ℝ)
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ (1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  set G := gridOf K (N K) h.hK1 with hG
  have hΩ := cardFactors_P₀_leE h
  have hΩ0 : (0 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ) := by positivity
  -- the geometric factor
  have hg1 : (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
      ≤ (1 / 3 : ℝ) ^ (K + N K) := by
    have h1 : (1 / (b : ℝ)) ^ (K + N K + 1) ≤ (1 / 3 : ℝ) ^ (K + N K + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2 : (b : ℝ) / ((b : ℝ) - 1) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 : (0 : ℝ) < (1 / 3 : ℝ) ^ (K + N K + 1) := by positivity
    calc (1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))
        ≤ (1 / 3 : ℝ) ^ (K + N K + 1) * (3 / 2) := by
          have hb0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
            have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
            positivity
          exact mul_le_mul h1 h2 hb0 h3.le
      _ = (1 / 3 : ℝ) ^ (K + N K) * (1 / 2) := by rw [pow_succ]; ring
      _ ≤ (1 / 3 : ℝ) ^ (K + N K) := by nlinarith [(by positivity : (0:ℝ) < (1/3:ℝ) ^ (K + N K))]
  -- `2^K (1/3)^{K+N} ≤ (1/2)^{2k₄} (1/2)^{100K²}`
  have hNK : N K = 100 * K ^ 2 := rfl
  have hsplit : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
      ≤ ((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
    have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by
      rw [← mul_pow]; norm_num
    have hth : (2 / 3 : ℝ) ^ K ≤ ((1 / 2 : ℝ) ^ k₄) ^ 2 := two_thirds_pow_le hK4
    have hth' : (2 / 3 : ℝ) ^ K ≤ ((1 : ℝ) / 2) ^ (2 * k₄) := by
      rw [mul_comm, pow_mul]
      exact hth
    have hN3 : (1 / 3 : ℝ) ^ (N K) ≤ ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
      rw [hNK]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)
        = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K) * (1 / 3 : ℝ) ^ (N K) := by rw [pow_add]; ring
      _ = (2 / 3 : ℝ) ^ K * (1 / 3 : ℝ) ^ (N K) := by rw [h23]
      _ ≤ ((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2) := by
          exact mul_le_mul hth' hN3 (by positivity) (by positivity)
  -- assemble
  have hfinal : ((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (21 * K ^ 2 + 1)
      = ((1 : ℝ) / 2) ^ (100 * K ^ 2 - (21 * K ^ 2 + 1)) :=
    half_pow_mul_two_pow (by nlinarith [hK, sq_nonneg K])
  have hD : k₄ + 2 * K ≤ 2 * k₄ + (100 * K ^ 2 - (21 * K ^ 2 + 1)) := by
    have hKsq : K * 100 ≤ K ^ 2 := by nlinarith [hK]
    have hKk : K = 4 * k₄ := hK4
    omega
  calc (2 : ℝ) ^ K * (((Ω G.P₀ : ℕ) : ℝ)
        * ((1 / (b : ℝ)) ^ (K + N K + 1) * ((b : ℝ) / ((b : ℝ) - 1))))
      ≤ (2 : ℝ) ^ K * (((Ω G.P₀ : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (K + N K)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hΩ0) (by positivity)
    _ = ((2 : ℝ) ^ K * (1 / 3 : ℝ) ^ (K + N K)) * ((Ω G.P₀ : ℕ) : ℝ) := by ring
    _ ≤ (((1 : ℝ) / 2) ^ (2 * k₄) * ((1 : ℝ) / 2) ^ (100 * K ^ 2)) * (2 : ℝ) ^ (21 * K ^ 2 + 1) := by
        exact mul_le_mul hsplit hΩ hΩ0 (by positivity)
    _ = ((1 : ℝ) / 2) ^ (2 * k₄) * (((1 : ℝ) / 2) ^ (100 * K ^ 2) * (2 : ℝ) ^ (21 * K ^ 2 + 1)) := by
        ring
    _ = ((1 : ℝ) / 2) ^ (2 * k₄ + (100 * K ^ 2 - (21 * K ^ 2 + 1))) := by
        rw [hfinal, pow_add]
    _ ≤ (1 / 64 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := half_pow_le_target' (by omega) hD

/-- **`hjunk` in base `b ≥ 3`**, against `η = 2^{−k₄}`, `ε = 1/K`. -/
theorem hjunk_holdsE {k₄ : ℕ} (hK4 : K = 4 * k₄) (hk : 40 ≤ k₄) (h : HypE b K e) :
    (junkShiftBound (gridOf K (N K) h.hK1).P₀ (XE K e) (J K * gridDm K (N K))
        / ((apSample (XE K e) (gridOf K (N K) h.hK1).P₀
              (gridOf K (N K) h.hK1).b₀).card : ℝ)) * rowL1 b K
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.base.hb
  have hK := h.base.hK
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  set G := gridOf K (N K) h.hK1 with hG
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have hcard0 : (0 : ℝ) < (apSample (XE K e) G.P₀ G.b₀).card := by
    exact_mod_cast (sample_nonemptyE h).card_pos
  have hcard := Sched.card_apSample_ge_half (XE K e) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (two_mul_P₀_le_XE h)
  have hXpos : 0 < XE K e := by unfold XE; positivity
  have hV := junkShiftBound_div_le' (P₀ := G.P₀) (X := XE K e)
    (ρmax := J K * gridDm K (N K)) G.P₀_pos hXpos (J_mul_gridDm_le_XE h) hcard0 hcard
    (junk_size_holdsE h)
  have hlogω := log_card_primeFactors_P₀_leE h
  have hV' : junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) ≤ 5 + 30 * (K : ℝ) ^ 2 := by linarith
  have hV0 : (0 : ℝ) ≤ junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
      / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ) :=
    div_nonneg (junkShiftBound_nonneg _ _ _) hcard0.le
  have hL1 : rowL1 b K ≤ a ^ 2 / 2 := by
    have := rowL1_le_three hb K; have := two_thirds_pow_le (k₄ := k₄) hK4; linarith
  have hL10 : (0 : ℝ) ≤ rowL1 b K :=
    rowL1_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  -- the arithmetic condition `20K + 120K³ ≤ 2^{k₄}`
  have hcube : 100000 * k₄ ^ 3 ≤ 2 ^ k₄ := cube_le_two_pow hk
  have hk₄r : (40 : ℝ) ≤ k₄ := by exact_mod_cast hk
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  have hpow : (20 * (K : ℝ) + 120 * (K : ℝ) ^ 3) * a ≤ 1 := by
    have hcr : (100000 : ℝ) * (k₄ : ℝ) ^ 3 ≤ (2 : ℝ) ^ k₄ := by exact_mod_cast hcube
    have hae : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
    rw [hae, mul_one_div, div_le_one (by positivity), hKk]
    have hsq : (1600 : ℝ) ≤ (k₄ : ℝ) ^ 2 := by nlinarith [hk₄r]
    have hk3 : (k₄ : ℝ) ≤ (k₄ : ℝ) ^ 3 := by nlinarith [hk₄r, hsq]
    nlinarith [hcr, hk3, hk₄r]
  calc (junkShiftBound G.P₀ (XE K e) (J K * gridDm K (N K))
        / ((apSample (XE K e) G.P₀ G.b₀).card : ℝ)) * rowL1 b K
      ≤ (5 + 30 * (K : ℝ) ^ 2) * (a ^ 2 / 2) := by
        exact mul_le_mul hV' hL1 hL10 (by positivity)
    _ = ((20 * (K : ℝ) + 120 * (K : ℝ) ^ 3) * a) * (a / (8 * K)) := by
        have hKpos : (0 : ℝ) < K := by linarith
        field_simp
        ring
    _ ≤ 1 * (a / (8 * K)) := by
        have hKpos : (0 : ℝ) < K := by linarith
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
        have hKpos : (0 : ℝ) < K := by linarith
        field_simp

end SchedB

end NormalNumbers.G4
