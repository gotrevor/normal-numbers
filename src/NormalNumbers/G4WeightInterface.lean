/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeLambertFour
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# G5: the additive-weight interface — `ω` plus a bounded multiple of the excess valuation

Campaign G5 asks which properties of `ω` the disjunctivity proof of `∑ ω(n)/bⁿ` actually
uses, and to prove the theorem for a class of weights with `ω` and `Ω` as instances.

**The class.**  For coefficients `c : ℕ → ℝ` (indexed by primes) we set

  `valWeight c m = ∑_p c_p · v_p(m)`          (completely additive),
  `omegaW c m   = ∑_{p ∣ m} c_p`,
  `excess c m   = valWeight c m − omegaW c m = ∑_{p ∣ m} c_p (v_p(m) − 1)`,
  `weightW c m  = ω(m) + excess c m = ∑_{p ∣ m} (1 + c_p (v_p(m) − 1))`.

Instances: `c = 0` gives `ω` on the nose (`weightW_zero`), `c = 1` gives `Ω`
(`weightW_one`).  The standing hypothesis downstream is `0 ≤ c_p ≤ C` for a fixed `C`.

**Why exactly this class.**  Write an additive weight as `w(m) = ∑_p g_p(v_p(m))`, `g_p(0)=0`.
The exact affine transport identity of `G4Transport` (`w(dm) − w(m) − w(d)` periodic in `m`
modulo `rad d`) holds iff every `g_p` is affine on `v ≥ 1`, i.e. `g_p(v) = a_p + c_p(v−1)`.
The Fourier control of §4C is proved for the *indicator* model, i.e. for `a_p = 1`; so the
class for which the existing proof applies with its arithmetic untouched is exactly
`weightW c`, and the junk `excess c` must be carried by the §4D remainder budget, not by C2.
This file proves the transport identity for `excess` (`excess_mul`) and its periodicity
(`overlapW_congr`); the remainder-side estimates live in `G4WeightJunk`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.PrimeLambert

/-! ### Definitions -/

/-- `∑_p c_p v_p(m)`, completely additive. -/
noncomputable def valWeight (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  m.factorization.sum fun p v => c p * (v : ℝ)

/-- `∑_{p ∣ m} c_p`. -/
noncomputable def omegaW (c : ℕ → ℝ) (m : ℕ) : ℝ := ∑ p ∈ m.primeFactors, c p

/-- The excess valuation weight `∑_{p ∣ m} c_p (v_p(m) − 1)`. -/
noncomputable def excess (c : ℕ → ℝ) (m : ℕ) : ℝ := valWeight c m - omegaW c m

/-- The interface weight `w_c = ω + excess c`. -/
noncomputable def weightW (c : ℕ → ℝ) (m : ℕ) : ℝ := omegaR m + excess c m

/-- The interface constant `∑_n w_c(n)/bⁿ`. -/
noncomputable def weightLambert (b : ℕ) (c : ℕ → ℝ) : ℝ := ∑' n : ℕ, weightW c n / (b : ℝ) ^ n

/-! ### The sums as sums over the prime factors -/

lemma valWeight_eq (c : ℕ → ℝ) (m : ℕ) :
    valWeight c m = ∑ p ∈ m.primeFactors, c p * (m.factorization p : ℝ) := by
  unfold valWeight Finsupp.sum
  rw [Nat.support_factorization]

lemma excess_eq (c : ℕ → ℝ) (m : ℕ) :
    excess c m = ∑ p ∈ m.primeFactors, c p * ((m.factorization p : ℝ) - 1) := by
  unfold excess omegaW
  rw [valWeight_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-! ### The two instances -/

@[simp] lemma valWeight_zero_coeff (m : ℕ) : valWeight (fun _ => (0 : ℝ)) m = 0 := by
  simp [valWeight_eq]

@[simp] lemma omegaW_zero_coeff (m : ℕ) : omegaW (fun _ => (0 : ℝ)) m = 0 := by
  simp [omegaW]

lemma excess_zero_coeff (m : ℕ) : excess (fun _ => (0 : ℝ)) m = 0 := by
  simp [excess]

/-- **Instance `ω`**: `c = 0`. -/
theorem weightW_zero (m : ℕ) : weightW (fun _ => (0 : ℝ)) m = omegaR m := by
  simp [weightW, excess_zero_coeff]

theorem weightLambert_zero (b : ℕ) : weightLambert b (fun _ => (0 : ℝ)) = primeLambertAtBase b := by
  unfold weightLambert primeLambertAtBase
  simp_rw [weightW_zero]

lemma valWeight_one_coeff (m : ℕ) : valWeight (fun _ => (1 : ℝ)) m = (Ω m : ℝ) := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, valWeight, Finsupp.sum, Finsupp.sum]
  push_cast
  simp

lemma omegaW_one_coeff (m : ℕ) : omegaW (fun _ => (1 : ℝ)) m = omegaR m := by
  simp [omegaW, omegaR_eq]

/-- **Instance `Ω`**: `c = 1`. -/
theorem weightW_one (m : ℕ) : weightW (fun _ => (1 : ℝ)) m = (Ω m : ℝ) := by
  unfold weightW excess
  rw [valWeight_one_coeff, omegaW_one_coeff]
  ring

theorem weightLambert_one (b : ℕ) :
    weightLambert b (fun _ => (1 : ℝ)) = ∑' n : ℕ, (Ω n : ℝ) / (b : ℝ) ^ n := by
  unfold weightLambert
  simp_rw [weightW_one]

/-! ### Complete additivity of `valWeight` -/

theorem valWeight_mul (c : ℕ → ℝ) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    valWeight c (d * m) = valWeight c d + valWeight c m := by
  unfold valWeight
  rw [Nat.factorization_mul hd hm]
  rw [Finsupp.sum_add_index' (fun p => by simp) (fun p a b => by push_cast; ring)]

/-! ### The overlap correction and the transport identity -/

/-- `∑_{p ∣ d, p ∣ m} c_p`. -/
noncomputable def overlapW (c : ℕ → ℝ) (d m : ℕ) : ℝ :=
  ∑ p ∈ d.primeFactors.filter (fun p => p ∣ m), c p

theorem omegaW_mul (c : ℕ → ℝ) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    omegaW c (d * m) = omegaW c d + omegaW c m - overlapW c d m := by
  unfold omegaW overlapW
  rw [Nat.primeFactors_mul hd hm, ← Finset.sum_union_inter]
  have : d.primeFactors ∩ m.primeFactors = d.primeFactors.filter (fun p => p ∣ m) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpd, _⟩, ⟨_, hpm, _⟩⟩; exact ⟨⟨hp, hpd, hd⟩, hpm⟩
    · rintro ⟨⟨hp, hpd, _⟩, hpm⟩; exact ⟨⟨hp, hpd, hd⟩, ⟨hp, hpm, hm⟩⟩
  rw [this]; ring

/-- **Exact transport for the excess**: `excess(dm) = excess(d) + excess(m) + ∑_{p∣d, p∣m} c_p`. -/
theorem excess_mul (c : ℕ → ℝ) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    excess c (d * m) = excess c d + excess c m + overlapW c d m := by
  unfold excess
  rw [valWeight_mul c hd hm, omegaW_mul c hd hm]; ring

/-- **Exact transport for `w_c`**: `w_c(dm) = w_c(m) + w_c(d) − ∑_{p∣d,p∣m} (1 − c_p)`. -/
theorem weightW_mul (c : ℕ → ℝ) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    weightW c (d * m) = weightW c m + weightW c d - ((overlap d m : ℝ) - overlapW c d m) := by
  unfold weightW
  rw [omegaR_mul_eq d m hd hm, excess_mul c hd hm]; ring

/-- Periodicity of the overlap correction modulo the primes of `d`. -/
theorem overlapW_congr (c : ℕ → ℝ) (d k k' : ℕ) (h : ∀ p ∈ d.primeFactors, k ≡ k' [MOD p]) :
    overlapW c d k = overlapW c d k' := by
  unfold overlapW
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (Nat.ModEq.dvd_iff (h p hp) (dvd_refl p)).1 hk⟩
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (Nat.ModEq.dvd_iff (h p hp) (dvd_refl p)).2 hk⟩

/-! ### Bounds -/

lemma valWeight_nonneg {c : ℕ → ℝ} (hc : ∀ p, 0 ≤ c p) (m : ℕ) : 0 ≤ valWeight c m := by
  rw [valWeight_eq]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hc p) (by positivity)

lemma excess_nonneg {c : ℕ → ℝ} (hc : ∀ p, 0 ≤ c p) (m : ℕ) : 0 ≤ excess c m := by
  rw [excess_eq]
  refine Finset.sum_nonneg fun p hp => mul_nonneg (hc p) ?_
  have h1 : 1 ≤ m.factorization p :=
    (Nat.mem_primeFactors.1 hp).1.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hp).2.2
      |>.1 (Nat.mem_primeFactors.1 hp).2.1
  have : (1 : ℝ) ≤ m.factorization p := by exact_mod_cast h1
  linarith

/-- `excess c m ≤ C · (Ω(m) − ω(m))` when `0 ≤ c_p ≤ C`. -/
lemma excess_le {c : ℕ → ℝ} {C : ℝ} (hc : ∀ p, 0 ≤ c p) (hC : ∀ p, c p ≤ C) (m : ℕ) :
    excess c m ≤ C * ((Ω m : ℝ) - omegaR m) := by
  have h1 : (Ω m : ℝ) - omegaR m = excess (fun _ => (1 : ℝ)) m := by
    unfold excess; rw [valWeight_one_coeff, omegaW_one_coeff]
  rw [h1, excess_eq, excess_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have h2 : 1 ≤ m.factorization p :=
    (Nat.mem_primeFactors.1 hp).1.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hp).2.2
      |>.1 (Nat.mem_primeFactors.1 hp).2.1
  have : (0 : ℝ) ≤ (m.factorization p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ m.factorization p := by exact_mod_cast h2
    linarith
  nlinarith [hc p, hC p]

/-- `Ω(m) ≤ log₂ m`: `2^{Ω(m)} ≤ m`. -/
lemma two_pow_cardFactors_le {m : ℕ} (hm : m ≠ 0) : 2 ^ (Ω m) ≤ m := by
  induction m using Nat.recOnPrimePow with
  | zero => exact absurd rfl hm
  | one => simp
  | prime_pow_mul a p n hp _ hn ih =>
    have ha : a ≠ 0 := by rintro rfl; simp at hm
    rw [ArithmeticFunction.cardFactors_mul (pow_ne_zero _ hp.ne_zero) ha,
      ArithmeticFunction.cardFactors_apply_prime_pow hp, pow_add]
    have h2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n
    exact Nat.mul_le_mul h2 (ih ha)

lemma cardFactors_le_log {m : ℕ} (hm : m ≠ 0) : Ω m ≤ Nat.log 2 m :=
  Nat.le_log_of_pow_le (by norm_num) (two_pow_cardFactors_le hm)

/-- `w_c(m) ≤ (1 + C) · m`: crude growth, enough for summability. -/
lemma weightW_le {c : ℕ → ℝ} {C : ℝ} (hc : ∀ p, 0 ≤ c p) (hC : ∀ p, c p ≤ C) (hC0 : 0 ≤ C)
    (m : ℕ) : weightW c m ≤ (1 + C) * m := by
  unfold weightW
  have h1 := excess_le hc hC m
  have h2 : (Ω m : ℝ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact_mod_cast (two_pow_cardFactors_le hm.ne').trans' (Nat.lt_two_pow_self).le
  have h3 := omegaR_le m
  have h4 := omegaR_nonneg m
  nlinarith

lemma weightW_nonneg {c : ℕ → ℝ} (hc : ∀ p, 0 ≤ c p) (m : ℕ) : 0 ≤ weightW c m :=
  add_nonneg (omegaR_nonneg m) (excess_nonneg hc m)

/-- Summability of the interface series in any base `b ≥ 2`. -/
theorem summable_weightW_div_pow {b : ℕ} (hb : 2 ≤ b) {c : ℕ → ℝ} {C : ℝ} (hc : ∀ p, 0 ≤ c p)
    (hC : ∀ p, c p ≤ C) (hC0 : 0 ≤ C) :
    Summable (fun n : ℕ => weightW c n / (b : ℝ) ^ n) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : Summable (fun n : ℕ => (1 + C) * ((n : ℝ) / (b : ℝ) ^ n)) := by
    refine Summable.mul_left _ ?_
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (b : ℝ)⁻¹)
      (by rw [norm_inv, Real.norm_of_nonneg (by positivity), inv_lt_one_iff₀]; right; linarith)
    refine this.congr fun n => ?_
    simp [div_eq_mul_inv, inv_pow]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact div_nonneg (weightW_nonneg hc n) (by positivity)
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (weightW_le hc hC hC0 n) (by positivity)

end NormalNumbers.PrimeLambert
