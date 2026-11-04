/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertRichCount
import NormalNumbers.PowerLambertDisjunctivity
import NormalNumbers.SmallCoefficientMean

/-!
# The power-Lambert orbit as a periodic tail plus a small tail

`orbit b (powerLambert b r) n = {P_Q(n) + R_Q(n)}`, where `P_Q(n)` is the Lambert tail of the
periodic power-divisor part (so `P_Q(n + kQ) = P_Q(n)`) and `R_Q(n) ≥ 0` is the tail of the
non-periodic part.  If every root `d ≤ D` has `d ^ r ∣ Q`, then `R_Q(n) ≤ 2 C(n) / (D + 1)` and
`Σ_{k<K} R_Q(n + kQ) ≤ C(n) (2K/(D+1) + √(KQ+1))` with `C(n) = Σ_j (n+1+j)/b^{j+1}`.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- The Lambert tail after position `n` of the `Q`-periodic power-divisor part. -/
noncomputable def periodicTail (b r Q n : ℕ) : ℝ :=
  ∑' j : ℕ, (periodicPowerCount r Q (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)

/-- The Lambert tail after position `n` of the non-periodic power-divisor part. -/
noncomputable def aperiodicTail (b r Q n : ℕ) : ℝ :=
  ∑' j : ℕ, (aperiodicPowerCount r Q (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)

/-- The affine weight `C(n) = Σ_j (n+1+j)/b^{j+1}` controlling both tails. -/
noncomputable def affineTailWeight (b n : ℕ) : ℝ :=
  ∑' j : ℕ, ((n + 1 + j : ℕ) : ℝ) / (b : ℝ) ^ (j + 1)

theorem summable_affineTailWeight (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    Summable (fun j : ℕ => ((n + 1 + j : ℕ) : ℝ) / (b : ℝ) ^ (j + 1)) := by
  simpa using JointLambert.summable_shift_tail b hb id (fun m => le_rfl) n

theorem affineTailWeight_nonneg (b n : ℕ) : 0 ≤ affineTailWeight b n :=
  tsum_nonneg fun j => by positivity

/-- A nonnegative coefficient sequence dominated by the index has a summable shifted tail. -/
theorem summable_tail_of_le (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (g : ℕ → ℕ)
    (hg : ∀ j, g (n + 1 + j) ≤ n + 1 + j) :
    Summable (fun j : ℕ => (g (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) :=
  Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => div_le_div_of_nonneg_right (by exact_mod_cast hg j) (by positivity))
    (summable_affineTailWeight b hb n)

theorem aperiodicTail_nonneg (b r Q n : ℕ) : 0 ≤ aperiodicTail b r Q n :=
  tsum_nonneg fun j => by positivity

/-- The periodic tail is periodic modulo `Q`. -/
theorem periodicTail_add_mul (b r Q n k : ℕ) :
    periodicTail b r Q (n + k * Q) = periodicTail b r Q n := by
  unfold periodicTail
  congr 1
  funext j
  rw [show n + k * Q + 1 + j = (n + 1 + j) + k * Q by ring, periodicPowerCount_add_mul]

/-- **Orbit decomposition.**  For `r ≥ 1` and `Q ≥ 1`, the base-`b` orbit of the
power-Lambert constant is the fractional part of the periodic tail plus the non-periodic
tail. -/
theorem orbit_powerLambert_eq (b r Q : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hQ : 0 < Q) (n : ℕ) :
    orbit b (powerLambert b r) n = Int.fract (periodicTail b r Q n + aperiodicTail b r Q n) := by
  have hx : powerLambert b r = CastingOut.lambertVal b (powerDivisorCount r) := by
    unfold powerLambert
    rw [powerLambert_eq_coefficientValue hb hr]
    rfl
  have hmaster := JointLambert.lambertVal_mul_pow_eq b hb (powerDivisorCount r)
    (powerDivisorCount_le_self r) n
  have hsplit : (∑' j : ℕ, (powerDivisorCount r (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) =
      periodicTail b r Q n + aperiodicTail b r Q n := by
    unfold periodicTail aperiodicTail
    rw [← (summable_tail_of_le b hb n _ fun j => periodicPowerCount_le_self hr hQ
      (by omega)).tsum_add (summable_tail_of_le b hb n _ fun j =>
        aperiodicPowerCount_le_self r Q _)]
    congr 1
    funext j
    rw [powerDivisorCount_eq_periodic_add_aperiodic hr hQ (by omega : 0 < n + 1 + j)]
    push_cast
    ring
  unfold orbit
  rw [hx, hmaster, hsplit, add_comm, Int.fract_add_natCast]

/-- Pointwise: the non-periodic part is at most `2 m / (D + 1)` when every root `d ≤ D`
has `d ^ r ∣ Q` (`r ≥ 2`, `m ≥ 1`). -/
theorem aperiodicPowerCount_le_two_mul_div {r Q D m : ℕ} (hr : 2 ≤ r) (hm : 0 < m)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) :
    (aperiodicPowerCount r Q m : ℝ) ≤ 2 * m / ((D : ℝ) + 1) := by
  classical
  set I := Ioo D (Nat.sqrt m + 1)
  have h1 := aperiodicPowerCount_le_card_Ioo hr hm le_rfl hQD (Q := Q)
  have h2 : (((I.filter fun d => d ^ r ∣ m).card : ℕ) : ℝ) ≤
      ∑ d ∈ I, (m : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := by have := (Finset.mem_Ioo.mp hd).1; omega
    split_ifs with hdvd
    · have hle : d ^ 2 ≤ m := (Nat.pow_le_pow_right hd1 hr).trans (Nat.le_of_dvd hm hdvd)
      have hpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
      rw [Nat.cast_one, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
      exact_mod_cast hle
    · positivity
  have h3 : (∑ d ∈ I, (m : ℝ) * ((d : ℝ) ^ 2)⁻¹) ≤ m * (2 / ((D : ℝ) + 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le _ _) (by positivity)
  calc (aperiodicPowerCount r Q m : ℝ) ≤ (((I.filter fun d => d ^ r ∣ m).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ _ := h2.trans h3
    _ = 2 * m / ((D : ℝ) + 1) := by ring

/-- The non-periodic tail at a single position is `O(1/D)`. -/
theorem aperiodicTail_le {b r Q D : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (n : ℕ) :
    aperiodicTail b r Q n ≤ 2 / ((D : ℝ) + 1) * affineTailWeight b n := by
  unfold aperiodicTail affineTailWeight
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_)
    (summable_tail_of_le b hb n _ fun j => aperiodicPowerCount_le_self r Q _)
    ((summable_affineTailWeight b hb n).mul_left _)
  have h := aperiodicPowerCount_le_two_mul_div hr (by omega : 0 < n + 1 + j) hQD (Q := Q)
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc (aperiodicPowerCount r Q (n + 1 + j) : ℝ) ≤ 2 * ((n + 1 + j : ℕ) : ℝ) / ((D : ℝ) + 1) := h
    _ = 2 / ((D : ℝ) + 1) * ((n + 1 + j : ℕ) : ℝ) := by ring

/-- The boundary error `√(m₀ + K Q) ≤ m₀ √(K Q + 1)` for `m₀ ≥ 1`. -/
theorem nat_sqrt_add_le_mul {m₀ X : ℕ} (hm₀ : 0 < m₀) :
    (Nat.sqrt (m₀ + X) : ℝ) ≤ (m₀ : ℝ) * Real.sqrt ((X : ℝ) + 1) := by
  have hm : (1 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
  calc (Nat.sqrt (m₀ + X) : ℝ) ≤ Real.sqrt ((m₀ + X : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ ≤ Real.sqrt ((m₀ : ℝ) * m₀ * ((X : ℝ) + 1)) := by
        apply Real.sqrt_le_sqrt
        push_cast
        have h1 : (1 : ℝ) ≤ (m₀ : ℝ) * m₀ := by nlinarith
        have hX : (0 : ℝ) ≤ X := by positivity
        have h2 : (X : ℝ) ≤ (m₀ : ℝ) * m₀ * X := by nlinarith
        have h3 : (m₀ : ℝ) ≤ (m₀ : ℝ) * m₀ := by nlinarith
        nlinarith
    _ = (m₀ : ℝ) * Real.sqrt ((X : ℝ) + 1) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]

/-- **Averaged non-periodic tail along the progression `n + kQ`.** -/
theorem sum_aperiodicTail_le {b r Q D : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (n K : ℕ) :
    (∑ k ∈ range K, aperiodicTail b r Q (n + k * Q)) ≤
      affineTailWeight b n *
        ((K : ℝ) * (2 / ((D : ℝ) + 1)) + Real.sqrt (((K * Q : ℕ) : ℝ) + 1)) := by
  set c : ℝ := (K : ℝ) * (2 / ((D : ℝ) + 1)) + Real.sqrt (((K * Q : ℕ) : ℝ) + 1)
  let g : ℕ → ℕ → ℝ := fun k j =>
    (aperiodicPowerCount r Q (n + 1 + j + k * Q) : ℝ) / (b : ℝ) ^ (j + 1)
  have hg : ∀ k, aperiodicTail b r Q (n + k * Q) = ∑' j, g k j := by
    intro k
    unfold aperiodicTail
    congr 1
    funext j
    simp only [g]
    rw [show n + k * Q + 1 + j = n + 1 + j + k * Q by ring]
  have hgs : ∀ k, Summable (g k) := by
    intro k
    have := summable_tail_of_le b hb (n + k * Q) (aperiodicPowerCount r Q)
      (fun j => aperiodicPowerCount_le_self r Q _)
    refine this.congr fun j => ?_
    simp only [g]
    rw [show n + k * Q + 1 + j = n + 1 + j + k * Q by ring]
  simp_rw [hg]
  rw [summable_sum_tsum_range K g hgs]
  unfold affineTailWeight
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun k _ => hgs k)
    ((summable_affineTailWeight b hb n).mul_right _)
  simp only [g]
  rw [← Finset.sum_div, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hm₀ : 0 < n + 1 + j := by omega
  have h := sum_aperiodicPowerCount_le hr hm₀ hQD K (Q := Q)
  have hsq := nat_sqrt_add_le_mul (X := K * Q) hm₀
  calc (∑ k ∈ range K, (aperiodicPowerCount r Q (n + 1 + j + k * Q) : ℝ))
      ≤ (K : ℝ) * ((n + 1 + j : ℕ) : ℝ) * (2 / ((D : ℝ) + 1)) +
          Nat.sqrt (n + 1 + j + K * Q) := h
    _ ≤ (K : ℝ) * ((n + 1 + j : ℕ) : ℝ) * (2 / ((D : ℝ) + 1)) +
          ((n + 1 + j : ℕ) : ℝ) * Real.sqrt (((K * Q : ℕ) : ℝ) + 1) := by linarith
    _ = ((n + 1 + j : ℕ) : ℝ) * c := by ring

end NormalNumbers.ArithmeticDisjunctivity
