/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerDivisorCoefficients
import Mathlib.Analysis.PSeries

/-!
# Power divisors along an arithmetic progression

For a modulus `Q`, the power-divisor count splits into the part whose roots `d` have
`d ^ r ∣ Q` (periodic modulo `Q`) and the remaining part.  When every `d ≤ D` has
`d ^ r ∣ Q`, the remaining part only sees roots `d > D`, and its average along a
progression `m₀ + k Q` is `O(m₀ / D)` up to an `O(√(m₀ + K Q))` boundary error.

The key counting input: `#{k < K : M ∣ m₀ + k Q} ≤ K m₀ / M + 1` for `m₀ ≥ 1`, because
the solutions form one class modulo `M / gcd(M, Q)` and `gcd(M, Q) ∣ m₀`.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- Roots `d` with `d ^ r ∣ Q` and `d ^ r ∣ m`: the part of the power-divisor count that is
periodic modulo `Q`. -/
def periodicPowerCount (r Q m : ℕ) : ℕ :=
  (Q.divisors.filter fun d => d ^ r ∣ Q ∧ d ^ r ∣ m).card

/-- Roots `d` with `d ^ r ∣ m` but `d ^ r ∤ Q`: the non-periodic part. -/
def aperiodicPowerCount (r Q m : ℕ) : ℕ :=
  (m.divisors.filter fun d => d ^ r ∣ m ∧ ¬ d ^ r ∣ Q).card

/-- The periodic part is periodic modulo `Q`. -/
theorem periodicPowerCount_add_mul (r Q m k : ℕ) :
    periodicPowerCount r Q (m + k * Q) = periodicPowerCount r Q m := by
  unfold periodicPowerCount
  congr 1
  apply Finset.filter_congr
  intro d _
  constructor
  · rintro ⟨hQ, hm⟩
    exact ⟨hQ, (Nat.dvd_add_left (Dvd.dvd.mul_left hQ k)).mp hm⟩
  · rintro ⟨hQ, hm⟩
    exact ⟨hQ, dvd_add hm (Dvd.dvd.mul_left hQ k)⟩

/-- For `m, Q ≥ 1` and `r ≥ 1`, the power-divisor count splits into its periodic and
non-periodic parts. -/
theorem powerDivisorCount_eq_periodic_add_aperiodic {r Q m : ℕ} (hr : 1 ≤ r)
    (hQ : 0 < Q) (hm : 0 < m) :
    powerDivisorCount r m = periodicPowerCount r Q m + aperiodicPowerCount r Q m := by
  classical
  unfold powerDivisorCount periodicPowerCount aperiodicPowerCount
  rw [← Finset.card_filter_add_card_filter_not
    (s := m.divisors.filter fun d => d ^ r ∣ m) (fun d => d ^ r ∣ Q)]
  rw [Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hdr : ∀ n, d ^ r ∣ n → d ∣ n := fun n h => (dvd_pow_self d (by omega)).trans h
  constructor
  · rintro ⟨⟨_, _⟩, hm', hQ'⟩
    exact ⟨⟨hdr Q hQ', by omega⟩, hQ', hm'⟩
  · rintro ⟨⟨_, _⟩, hQ', hm'⟩
    exact ⟨⟨hdr m hm', by omega⟩, hm', hQ'⟩

/-- The power-divisor count is at most its argument. -/
theorem powerDivisorCount_le_self (r m : ℕ) : powerDivisorCount r m ≤ m :=
  (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self m)

/-- The periodic part is at most its (positive) argument. -/
theorem periodicPowerCount_le_self {r Q m : ℕ} (hr : 1 ≤ r) (hQ : 0 < Q) (hm : 0 < m) :
    periodicPowerCount r Q m ≤ m := by
  have := powerDivisorCount_eq_periodic_add_aperiodic (r := r) hr hQ hm
  have := powerDivisorCount_le_self r m
  omega

/-- The non-periodic part is at most its argument. -/
theorem aperiodicPowerCount_le_self (r Q m : ℕ) : aperiodicPowerCount r Q m ≤ m :=
  (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self m)

/-- If every root `d ≤ D` has `d ^ r ∣ Q`, the non-periodic part vanishes below `D`. -/
theorem aperiodicPowerCount_eq_zero_of_le {r Q D m : ℕ}
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (hm : m ≤ D) :
    aperiodicPowerCount r Q m = 0 := by
  unfold aperiodicPowerCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d hd
  rw [Nat.mem_divisors] at hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  have hdm : d ≤ m := Nat.le_of_dvd (by omega) hd.1
  exact fun h => h.2 (hQD d hd1 (by omega))

/-- Pointwise: the non-periodic part is at most `m² / D`. -/
theorem aperiodicPowerCount_le_sq_div {r Q D m : ℕ} (hD : 0 < D)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) :
    (aperiodicPowerCount r Q m : ℝ) ≤ (m : ℝ) ^ 2 / D := by
  by_cases hm : m ≤ D
  · rw [aperiodicPowerCount_eq_zero_of_le hQD hm, Nat.cast_zero]
    positivity
  · have hle : (aperiodicPowerCount r Q m : ℝ) ≤ m := by
      exact_mod_cast aperiodicPowerCount_le_self r Q m
    have hDm : (D : ℝ) ≤ m := by exact_mod_cast (by omega : D ≤ m)
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    rw [le_div_iff₀ hDpos]
    nlinarith

/-- Integers `k < K` in one residue class modulo `T` number at most `K / T + 1`. -/
theorem card_le_of_modEq_class {S : Finset ℕ} {K T : ℕ}
    (hS : ∀ k ∈ S, k < K) (hmod : ∀ k ∈ S, ∀ k' ∈ S, k % T = k' % T) :
    S.card ≤ K / T + 1 := by
  have hinj : Set.InjOn (fun k => k / T) (S : Set ℕ) := by
    intro k hk k' hk' h
    have h1 := Nat.div_add_mod k T
    have h2 := Nat.div_add_mod k' T
    have h3 := hmod k hk k' hk'
    simp only at h
    rw [← h1, ← h2, h, h3]
  have hsub : S.image (fun k => k / T) ⊆ range (K / T + 1) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range]
    have : k / T ≤ K / T := Nat.div_le_div_right (hS k hk).le
    omega
  calc S.card = (S.image (fun k => k / T)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (range (K / T + 1)).card := Finset.card_le_card hsub
    _ = K / T + 1 := Finset.card_range _

/-- **Progression count.**  For `M, Q, m₀ ≥ 1`, the number of `k < K` with
`M ∣ m₀ + k Q` is at most `K m₀ / M + 1`.  The solutions form one residue class modulo
`M / gcd(M, Q)`, and `gcd(M, Q) ∣ m₀` forces `gcd(M, Q) ≤ m₀`. -/
theorem card_filter_dvd_add_mul_le {M Q m₀ : ℕ} (hM : 0 < M) (hm₀ : 0 < m₀) (K : ℕ) :
    (((range K).filter fun k => M ∣ m₀ + k * Q).card : ℝ) ≤ (K : ℝ) * m₀ / M + 1 := by
  classical
  set S := (range K).filter fun k => M ∣ m₀ + k * Q with hSdef
  rcases S.eq_empty_or_nonempty with hS | ⟨k₀, hk₀⟩
  · rw [hS, Finset.card_empty, Nat.cast_zero]
    positivity
  set g := Nat.gcd M Q with hg
  have hk₀' := (Finset.mem_filter.mp hk₀).2
  have hgm₀ : g ∣ m₀ := by
    have h1 : g ∣ m₀ + k₀ * Q := (Nat.gcd_dvd_left M Q).trans hk₀'
    exact (Nat.dvd_add_left (Dvd.dvd.mul_left (Nat.gcd_dvd_right M Q) k₀)).mp h1
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hM
  have hgle : g ≤ m₀ := Nat.le_of_dvd hm₀ hgm₀
  set T := M / g with hT
  have hTpos : 0 < T := Nat.div_pos (Nat.le_of_dvd hM (Nat.gcd_dvd_left M Q)) hgpos
  have hmod : ∀ k ∈ S, ∀ k' ∈ S, k % T = k' % T := by
    intro k hk k' hk'
    have hk1 := (Finset.mem_filter.mp hk).2
    have hk2 := (Finset.mem_filter.mp hk').2
    have h0 : m₀ + k * Q ≡ m₀ + k' * Q [MOD M] :=
      (Nat.modEq_zero_iff_dvd.mpr hk1).trans (Nat.modEq_zero_iff_dvd.mpr hk2).symm
    have h1 : k * Q ≡ k' * Q [MOD M] := Nat.ModEq.add_left_cancel' m₀ h0
    exact Nat.ModEq.cancel_right_div_gcd hM h1
  have hcard := card_le_of_modEq_class (K := K)
    (fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1) hmod
  have hTR : (T : ℝ) = (M : ℝ) / g := by
    rw [hT, Nat.cast_div (Nat.gcd_dvd_left M Q) (by exact_mod_cast hgpos.ne')]
  have hdiv : ((K / T : ℕ) : ℝ) ≤ (K : ℝ) * m₀ / M := by
    calc ((K / T : ℕ) : ℝ) ≤ (K : ℝ) / T := Nat.cast_div_le
      _ = (K : ℝ) * g / M := by
          rw [hTR]
          have : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
          have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
          field_simp
      _ ≤ (K : ℝ) * m₀ / M := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hgle) (by positivity)
  calc (S.card : ℝ) ≤ ((K / T + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((K / T : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (K : ℝ) * m₀ / M + 1 := by linarith

/-- A root of a non-periodic power divisor of `m ≤ X` lies in `(D, √X]`. -/
theorem aperiodicPowerCount_le_card_Ioo {r Q D m X : ℕ} (hr : 2 ≤ r) (hm : 0 < m)
    (hmX : m ≤ X) (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) :
    aperiodicPowerCount r Q m ≤
      ((Ioo D (Nat.sqrt X + 1)).filter fun d => d ^ r ∣ m).card := by
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdm, _⟩, hdr, hdQ⟩ := hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm hm
  have hDd : D < d := by
    by_contra h
    exact hdQ (hQD d hd1 (by omega))
  have hsq : d * d ≤ d ^ r := by
    rw [← sq]
    exact Nat.pow_le_pow_right hd1 hr
  have hpow : d ^ r ≤ m := Nat.le_of_dvd hm hdr
  have hdS : d ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  simp only [Finset.mem_filter, Finset.mem_Ioo]
  exact ⟨⟨hDd, by omega⟩, hdr⟩

/-- **Averaged non-periodic mass along a progression.**  If every root `d ≤ D` has
`d ^ r ∣ Q` (`r ≥ 2`), then along `m₀ + k Q`, `k < K`, the non-periodic power-divisor mass is
at most `2 K m₀ / (D + 1)` plus the boundary error `√(m₀ + K Q)`. -/
theorem sum_aperiodicPowerCount_le {r Q D m₀ : ℕ} (hr : 2 ≤ r) (hm₀ : 0 < m₀)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (K : ℕ) :
    (∑ k ∈ range K, (aperiodicPowerCount r Q (m₀ + k * Q) : ℝ)) ≤
      (K : ℝ) * m₀ * (2 / ((D : ℝ) + 1)) + Nat.sqrt (m₀ + K * Q) := by
  classical
  set I := Ioo D (Nat.sqrt (m₀ + K * Q) + 1) with hI
  have hstep1 : ∀ k ∈ range K, (aperiodicPowerCount r Q (m₀ + k * Q) : ℝ) ≤
      ((I.filter fun d => d ^ r ∣ m₀ + k * Q).card : ℝ) := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    exact_mod_cast aperiodicPowerCount_le_card_Ioo hr (by omega)
      (by nlinarith) hQD
  have hswap : (∑ k ∈ range K, (I.filter fun d => d ^ r ∣ m₀ + k * Q).card) =
      ∑ d ∈ I, ((range K).filter fun k => d ^ r ∣ m₀ + k * Q).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hstep3 : ∀ d ∈ I,
      ((((range K).filter fun k => d ^ r ∣ m₀ + k * Q).card : ℕ) : ℝ) ≤
        (K : ℝ) * m₀ * ((d : ℝ) ^ 2)⁻¹ + 1 := by
    intro d hd
    have hdD : D < d := (Finset.mem_Ioo.mp hd).1
    have hd1 : 1 ≤ d := by omega
    have hpos : 0 < d ^ r := Nat.pow_pos (by omega)
    have h := card_filter_dvd_add_mul_le (Q := Q) hpos hm₀ K
    have hsq : (d : ℝ) ^ 2 ≤ ((d ^ r : ℕ) : ℝ) := by
      push_cast
      exact pow_le_pow_right₀ (by exact_mod_cast hd1) hr
    have hsqpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    calc _ ≤ (K : ℝ) * m₀ / ((d ^ r : ℕ) : ℝ) + 1 := h
      _ ≤ (K : ℝ) * m₀ / (d : ℝ) ^ 2 + 1 := by
          gcongr
      _ = (K : ℝ) * m₀ * ((d : ℝ) ^ 2)⁻¹ + 1 := by rw [div_eq_mul_inv]
  have hsumsq : (∑ d ∈ I, ((d : ℝ) ^ 2)⁻¹) ≤ 2 / ((D : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
  have hcardI : ((I.card : ℕ) : ℝ) ≤ (Nat.sqrt (m₀ + K * Q) : ℝ) := by
    rw [hI, Nat.card_Ioo]
    exact_mod_cast (by omega)
  calc (∑ k ∈ range K, (aperiodicPowerCount r Q (m₀ + k * Q) : ℝ))
      ≤ ∑ k ∈ range K, ((I.filter fun d => d ^ r ∣ m₀ + k * Q).card : ℝ) :=
        Finset.sum_le_sum hstep1
    _ = ∑ d ∈ I, ((((range K).filter fun k => d ^ r ∣ m₀ + k * Q).card : ℕ) : ℝ) := by
        exact_mod_cast hswap
    _ ≤ ∑ d ∈ I, ((K : ℝ) * m₀ * ((d : ℝ) ^ 2)⁻¹ + 1) := Finset.sum_le_sum hstep3
    _ = (K : ℝ) * m₀ * (∑ d ∈ I, ((d : ℝ) ^ 2)⁻¹) + (I.card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (K : ℝ) * m₀ * (2 / ((D : ℝ) + 1)) + Nat.sqrt (m₀ + K * Q) := by
        gcongr

end NormalNumbers.ArithmeticDisjunctivity
