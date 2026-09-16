/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaWeight

/-!
# The closed form of the `Ω`-Lambert constant

`∑_n Ω(n)/bⁿ = ∑_{q a prime power} 1/(b^q − 1)`, the `Ω` analogue of
`∑_n ω(n)/bⁿ = ∑_{p prime} 1/(b^p − 1)`.  Both are the same double count of the pairs
`(n, q)` with `q ∣ n`, run in the two orders; for `Ω` the inner index ranges over the
prime *powers* `p^a`, `a ≥ 1`, because `Ω(n) = #{q ∣ n : q a prime power}`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

/-- **`Ω` counts prime-power divisors.** -/
theorem card_divisors_filter_isPrimePow {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter IsPrimePow).card = Ω n := by
  classical
  have hcard : (n.primeFactors.sigma (fun p => Finset.Icc 1 (n.factorization p))).card
      = (n.divisors.filter IsPrimePow).card := by
    refine Finset.card_bij (fun x _ => x.1 ^ x.2) ?_ ?_ ?_
    · rintro ⟨p, i⟩ hx
      simp only [Finset.mem_sigma, Nat.mem_primeFactors, Finset.mem_Icc] at hx
      obtain ⟨⟨hp, hpd, -⟩, hi1, hi2⟩ := hx
      refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, hn⟩, ?_⟩
      · exact (Nat.Prime.pow_dvd_iff_le_factorization hp hn).2 hi2
      · exact ⟨p, i, hp.prime, by omega, rfl⟩
    · rintro ⟨p, i⟩ hx ⟨q, j⟩ hy hpq
      simp only [Finset.mem_sigma, Nat.mem_primeFactors, Finset.mem_Icc] at hx hy
      have hp : p.Prime := hx.1.1
      have hq : q.Prime := hy.1.1
      simp only at hpq
      have hdvd : p ∣ q ^ j := hpq ▸ dvd_pow_self p (by omega)
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)
      subst hpq'
      have : i = j := Nat.pow_right_injective hp.two_le hpq
      simp [this]
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, -⟩, p, i, hp, hi, rfl⟩ := hd
      have hp' : p.Prime := Nat.prime_iff.2 hp
      have hi' : 1 ≤ i := by exact_mod_cast hi
      refine ⟨⟨p, i⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Nat.mem_primeFactors, Finset.mem_Icc]
      refine ⟨⟨hp', dvd_trans (dvd_pow_self p (by omega)) hdvd, hn⟩, hi', ?_⟩
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp' hn).1 hdvd
  rw [← hcard, Finset.card_sigma]
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.card_Icc]
  simp

/-- The double family `[q a prime power, q ∣ n, n ≠ 0]·b^{−n}`. -/
private noncomputable def cellΩ (b : ℕ) (n q : ℕ) : ℝ :=
  if IsPrimePow q ∧ q ∣ n ∧ n ≠ 0 then ((b : ℝ) ^ n)⁻¹ else 0

/-- **The closed form.**  `∑_n Ω(n)/bⁿ = ∑_{q a prime power} 1/(b^q − 1)`. -/
theorem cardFactorsLambert_eq_tsum_inv {b : ℕ} (hb : 2 ≤ b) :
    TWeight.cardFactors.lambert b
      = ∑' q : ℕ, (if IsPrimePow q then 1 / ((b : ℝ) ^ q - 1) else 0) := by
  classical
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  set f : ℕ → ℕ → ℝ := cellΩ b with hf
  have hf0 : ∀ n q, 0 ≤ f n q := by
    intro n q
    rw [hf, cellΩ]
    split_ifs
    · positivity
    · exact le_rfl
  have hrowsupp : ∀ n : ℕ, ∀ q ∉ n.divisors.filter IsPrimePow, f n q = 0 := by
    intro n q hq
    have hc : ¬ (IsPrimePow q ∧ q ∣ n ∧ n ≠ 0) := by
      intro hc
      exact hq (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hc.2.1, hc.2.2⟩, hc.1⟩)
    simp only [hf, cellΩ]
    exact if_neg hc
  have hrowS : ∀ n, Summable (f n) := fun n => summable_of_ne_finset_zero (hrowsupp n)
  have hrow : ∀ n, ∑' q, f n q = ((Ω n : ℕ) : ℝ) / (b : ℝ) ^ n := by
    intro n
    rw [tsum_eq_sum (hrowsupp n)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Nat.divisors_zero]
    · have hval : ∀ q ∈ n.divisors.filter IsPrimePow, f n q = ((b : ℝ) ^ n)⁻¹ := by
        intro q hq
        simp only [Finset.mem_filter, Nat.mem_divisors] at hq
        simp only [hf, cellΩ]
        exact if_pos ⟨hq.2, hq.1.1, hn⟩
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
        card_divisors_filter_isPrimePow hn, div_eq_mul_inv]
  have hcolS : ∀ q, Summable (fun n => f n q) := by
    intro q
    refine Summable.of_nonneg_of_le (fun n => hf0 n q) (fun n => ?_)
      (summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity) (by
        rw [inv_lt_one_iff₀]; right; linarith))
    simp only [hf, cellΩ]
    split_ifs
    · rw [← inv_pow]
    · positivity
  have hcol : ∀ q : ℕ, ∑' n, f n q = if IsPrimePow q then 1 / ((b : ℝ) ^ q - 1) else 0 := by
    intro q
    by_cases hq : IsPrimePow q
    · rw [if_pos hq]
      have hq2 : 2 ≤ q := hq.two_le
      have hbq : (1 : ℝ) < (b : ℝ) ^ q := one_lt_pow₀ (by linarith) (by omega)
      set r : ℝ := ((b : ℝ) ^ q)⁻¹ with hrdef
      have hr0 : 0 < r := by rw [hrdef]; positivity
      have hr1 : r < 1 := by rw [hrdef, inv_lt_one_iff₀]; right; exact hbq
      have hgeo0 : HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ :=
        hasSum_geometric_of_lt_one hr0.le hr1
      have hval : r * (1 - r)⁻¹ = 1 / ((b : ℝ) ^ q - 1) := by
        have hne : ((b : ℝ) ^ q - 1) ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
        rw [hrdef]
        field_simp
      have hgeo : HasSum (fun k : ℕ => r ^ (k + 1)) (1 / ((b : ℝ) ^ q - 1)) := by
        rw [← hval]
        exact (hgeo0.mul_left r).congr_fun (fun k => by rw [pow_succ]; ring)
      have hinj : Function.Injective (fun k : ℕ => q * (k + 1)) := by
        intro k1 k2 hk
        simp only at hk
        have : k1 + 1 = k2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) hk
        omega
      have hzero : ∀ n ∉ Set.range (fun k : ℕ => q * (k + 1)), f n q = 0 := by
        intro n hn
        have hc : ¬ (IsPrimePow q ∧ q ∣ n ∧ n ≠ 0) := by
          rintro ⟨-, hdvd, hn0⟩
          obtain ⟨m, rfl⟩ := hdvd
          have hm : m ≠ 0 := by rintro rfl; exact hn0 (by ring)
          exact hn ⟨m - 1, by simp only; congr 1; omega⟩
        simp only [hf, cellΩ]
        exact if_neg hc
      have hcomp : ∀ k : ℕ, f (q * (k + 1)) q = r ^ (k + 1) := by
        intro k
        have hne : q * (k + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero k)
        simp only [hf, cellΩ]
        rw [if_pos ⟨hq, Dvd.intro _ rfl, hne⟩, hrdef, inv_pow, ← pow_mul]
      have hHS : HasSum (fun n => f n q) (1 / ((b : ℝ) ^ q - 1)) :=
        (Function.Injective.hasSum_iff (f := fun n => f n q) hinj hzero).1
          (hgeo.congr_fun (fun k => hcomp k))
      exact hHS.tsum_eq
    · rw [if_neg hq]
      have hz : ∀ n, f n q = 0 := by
        intro n
        simp only [hf, cellΩ]
        exact if_neg (fun hc => hq hc.1)
      simp [hz]
  have huncurry : Summable (Function.uncurry f) := by
    have huc : Function.uncurry f = fun x : ℕ × ℕ => f x.1 x.2 := rfl
    rw [huc, summable_prod_of_nonneg (fun x => hf0 x.1 x.2)]
    refine ⟨fun n => hrowS n, ?_⟩
    exact Summable.congr (TWeight.summable_cardFactors_div_pow hb) (fun n => (hrow n).symm)
  calc TWeight.cardFactors.lambert b = ∑' n, ∑' q, f n q := by
        rw [TWeight.lambert]
        exact tsum_congr fun n => (hrow n).symm
    _ = ∑' q, ∑' n, f n q := (huncurry.tsum_comm' hrowS hcolS).symm
    _ = ∑' q : ℕ, (if IsPrimePow q then 1 / ((b : ℝ) ^ q - 1) else 0) := tsum_congr hcol

end NormalNumbers.G4
