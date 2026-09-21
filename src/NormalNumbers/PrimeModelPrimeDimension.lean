/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelBrunLower
import NormalNumbers.PrimeModelRadicalMoment

/-!
# The prime-density dimension input for the lower Brun sieve

`NormalNumbers.PrimeModel.Brun.brun_lower_fundamental` carries the tail-product hypothesis
`Brun.Dimension U g y K k`.  This file **discharges** it for the density of interest,
`g p = h / p` on a finite set `U` of primes `p` with `h < p ≤ y`, with

    `K = 4 ^ h * exp (16 h)`,   `k = 24 h`.

No prime-distribution input beyond the crude Mertens bound
`NormalNumbers.PrimeModel.Radical.mertens_crude` (`∑_{p ≤ N} log p / p ≤ 4 log N`) is used.

## Route

* **Small primes** `h < p ≤ 2h`: the factors `(1 - h/p)⁻¹ = p / (p - h)` are bounded by the
  full integer-interval product `∏_{m = h+1}^{2h} m/(m-h) = binom(2h, h) ≤ 4 ^ h`
  (`prod_Ioc_inv_eq_centralBinom`).
* **Large primes** `p > 2h`: `x = h/p < 1/2`, and `(1-x)⁻¹ ≤ exp (2x)` elementarily
  (`inv_one_sub_le_exp`), so the tail product is `exp (2h · ∑ 1/p)`.
* **Reciprocal prime sums**: for real `v ≥ 2` each *log-dyadic block* `(v, v²]` has
  `∑ 1/p ≤ 8` (`block_le_eight`, directly from `mertens_crude`), and `(v, y]` is covered by
  `⌈log₂ (log y / log v)⌉` such blocks (`primeRecipSum_le_blocks`), giving
  `∑_{v < p ≤ y} 1/p ≤ 8 + 12 log (log y / log v)` (`primeRecipSum_le`).

Combining, with `L = log y / log (max 2 t)`:
`∏_{p ∈ U, p > t} (1 - h/p)⁻¹ ≤ 4^h · exp (2h (8 + 12 log L)) = 4^h exp (16 h) · L ^ (24 h)`.

## Main results

* `prime_density_dimension` — the `Brun.Dimension` hypothesis, discharged.
* `prime_density_brun_lower` — `brun_lower_fundamental` instantiated at this density: the three
  weight properties hold under elementary hypotheses on `U, h, y, s` only.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace NormalNumbers.PrimeModel.PrimeDensity

open NormalNumbers.PrimeModel

/-! ### Elementary inequalities -/

/-- `(1 - x)⁻¹ ≤ exp (2 x)` for `0 ≤ x ≤ 1/2`.  Proof: `exp (-2x) ≤ (1 + 2x)⁻¹ ≤ 1 - x`, the
last step being `2x² ≤ x`. -/
lemma inv_one_sub_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1 : (1 : ℝ) + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  have hpos : (0 : ℝ) < 1 + 2 * x := by linarith
  have h2 : Real.exp (-(2 * x)) ≤ (1 + 2 * x)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hpos h1
  have h3 : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  have hsub : (0 : ℝ) < 1 - x := by linarith
  have h4 : Real.exp (-(2 * x)) ≤ 1 - x := h2.trans h3
  have h5 := inv_anti₀ (Real.exp_pos (-(2*x))) h4
  rw [← Real.exp_neg, neg_neg] at h5
  exact h5

/-! ### The small-prime product -/

/-- `Ioc h (2h)` reindexed by `range h`. -/
lemma Ioc_eq_image (h : ℕ) :
    Finset.Ioc h (2 * h) = (Finset.range h).image (fun i => h + 1 + i) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨m - h - 1, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩; omega

/-- `∏_{m = h+1}^{2h} (1 - h/m)⁻¹ = binom(2h, h)`. -/
lemma prod_Ioc_inv_eq_centralBinom (h : ℕ) :
    ∏ m ∈ Finset.Ioc h (2 * h), (1 - (h : ℝ) / m)⁻¹ = ((2 * h).choose h : ℝ) := by
  rw [Ioc_eq_image, Finset.prod_image (by intro a _ b _ hab; dsimp only at hab; omega)]
  have hterm : ∀ i ∈ Finset.range h,
      (1 - (h : ℝ) / ((h + 1 + i : ℕ) : ℝ))⁻¹ = ((h + 1 + i : ℕ) : ℝ) / ((1 + i : ℕ) : ℝ) := by
    intro i _
    have hne : ((h : ℝ) + 1 + i) ≠ 0 := by positivity
    have key : (1:ℝ) - (h : ℝ) / ((h : ℝ) + 1 + i) = (1 + (i:ℝ)) / ((h : ℝ) + 1 + i) := by
      field_simp
      ring
    push_cast
    rw [key, inv_div]
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
  have hA : ∏ i ∈ Finset.range h, ((h + 1 + i : ℕ) : ℝ) = (((h + 1).ascFactorial h : ℕ) : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast [add_assoc]
    ring_nf
  have hB : ∏ i ∈ Finset.range h, ((1 + i : ℕ) : ℝ) = ((Nat.factorial h : ℕ) : ℝ) := by
    have hf : (Nat.ascFactorial 1 h) = Nat.factorial h := by
      have h0 := Nat.factorial_mul_ascFactorial 0 h
      rw [Nat.factorial_zero, one_mul, Nat.zero_add] at h0
      simpa using h0
    rw [← hf, Nat.ascFactorial_eq_prod_range]
    push_cast
    ring_nf
  rw [hA, hB]
  have hkey : (h + 1).ascFactorial h = Nat.factorial h * ((2 * h).choose h) := by
    have hac := Nat.ascFactorial_eq_factorial_mul_choose h h
    rw [hac, two_mul]
  rw [hkey]
  push_cast
  field_simp

/-! ### Reciprocal prime sums from crude Mertens -/

open NormalNumbers.PrimeModel.Radical in
/-- **One log-dyadic block.**  For real `v ≥ 2`, `∑_{v < p ≤ v²} 1/p ≤ 8`.
Each term obeys `1/p ≤ (log p / p) / log v`, and `mertens_crude` caps the numerator sum by
`4 log ⌊v²⌋ ≤ 8 log v`. -/
lemma block_le_eight (v : ℝ) (hv : 2 ≤ v) (N : ℕ) :
    ∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
      (1 : ℝ) / p ≤ 8 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  set M := ⌊v ^ 2⌋₊ with hMdef
  have hv4 : (4 : ℝ) ≤ v ^ 2 := by nlinarith
  have hM2 : 2 ≤ M := by
    have h4 : (4 : ℕ) ≤ M := Nat.le_floor (by exact_mod_cast hv4)
    omega
  have hMle : (M : ℝ) ≤ v ^ 2 := Nat.floor_le (by positivity)
  have hsub : (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2)
      ⊆ (Finset.Iic M).filter (fun p => Nat.Prime p) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Iic] at hp ⊢
    exact ⟨Nat.le_floor hp.2.2.2, hp.2.1⟩
  have step : ∀ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
      (1 : ℝ) / p ≤ (Real.log p / p) / Real.log v := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨-, hpp, hvp, -⟩ := hp
    have hp0 : (0 : ℝ) < p := by
      have := hpp.two_le; positivity
    have hlp : Real.log v ≤ Real.log p := Real.log_le_log hv0 hvp.le
    rw [div_div, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith
  calc ∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
        (1 : ℝ) / p
      ≤ ∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
          (Real.log p / p) / Real.log v := Finset.sum_le_sum step
    _ = (∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
          Real.log p / p) / Real.log v := by rw [Finset.sum_div]
    _ ≤ mertensSum M / Real.log v := by
        refine div_le_div_of_nonneg_right ?_ hlogv.le
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro q hq _
        simp only [Finset.mem_filter, Finset.mem_Iic] at hq
        have := hq.2.two_le
        have : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.2.one_lt.le)
        positivity
    _ ≤ (4 * Real.log M) / Real.log v := by
        exact div_le_div_of_nonneg_right (mertens_crude M hM2) hlogv.le
    _ ≤ (8 * Real.log v) / Real.log v := by
        refine div_le_div_of_nonneg_right ?_ hlogv.le
        have hlogM : Real.log M ≤ Real.log (v ^ 2) :=
          Real.log_le_log (by positivity) hMle
        rw [Real.log_pow] at hlogM
        push_cast at hlogM
        linarith
    _ = 8 := by field_simp

/-- **Block count.**  `∑_{v < p ≤ N} 1/p ≤ 8 n` whenever `N ≤ v ^ (2 ^ n)`. -/
lemma primeRecipSum_le_blocks : ∀ n : ℕ, ∀ v : ℝ, 2 ≤ v → ∀ N : ℕ, (N : ℝ) ≤ v ^ (2 ^ n) →
    ∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ)), (1 : ℝ) / p ≤ 8 * n := by
  intro n
  induction n with
  | zero =>
    intro v hv N hN
    have hempty : (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ)) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro p hp
      simp only [Finset.mem_Iic] at hp
      rintro ⟨-, hvp⟩
      have : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp
      simp only [pow_zero, pow_one] at hN
      linarith
    rw [hempty]
    simp
  | succ n ih =>
    intro v hv N hN
    have hv2 : (2 : ℝ) ≤ v ^ 2 := by nlinarith
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ)))
      (fun p : ℕ => (p : ℝ) ≤ v ^ 2) (fun p : ℕ => (1 : ℝ) / p)
    have hnn : ∀ q : ℕ, (0:ℝ) ≤ 1 / q := by intro q; positivity
    have hA : ∑ p ∈ ((Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) ≤ v ^ 2), (1 : ℝ) / p ≤ 8 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => hnn q))
        (block_le_eight v hv N)
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2, hp.2⟩
    have hBsub : ((Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ))).filter
        (fun p : ℕ => ¬ (p : ℝ) ≤ v ^ 2)
        ⊆ (Finset.Iic N).filter (fun p => Nat.Prime p ∧ v ^ 2 < (p : ℝ)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic, not_le] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
    have hB : ∑ p ∈ ((Finset.Iic N).filter (fun p => Nat.Prime p ∧ v < (p : ℝ))).filter
        (fun p : ℕ => ¬ (p : ℝ) ≤ v ^ 2), (1 : ℝ) / p ≤ 8 * n := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun q _ _ => hnn q)) ?_
      refine ih (v ^ 2) hv2 N ?_
      calc (N : ℝ) ≤ v ^ (2 ^ (n + 1)) := hN
        _ = (v ^ 2) ^ (2 ^ n) := by rw [← pow_mul]; ring_nf
    rw [← hsplit]
    push_cast
    linarith

/-- **The reciprocal prime sum.**  For `2 ≤ v ≤ y`,
`∑_{v < p ≤ y} 1/p ≤ 8 + 12 log (log y / log v)`. -/
lemma primeRecipSum_le (v : ℝ) (hv : 2 ≤ v) (y : ℕ) (hvy : v ≤ (y : ℝ)) :
    ∑ p ∈ (Finset.Iic y).filter (fun p => Nat.Prime p ∧ v < (p : ℝ)), (1 : ℝ) / p
      ≤ 8 + 12 * Real.log (Real.log y / Real.log v) := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le hv0 hvy
  have hlogy : Real.log v ≤ Real.log y := Real.log_le_log hv0 hvy
  set L := Real.log y / Real.log v with hLdef
  have hL1 : 1 ≤ L := (one_le_div hlogv).2 hlogy
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  set n := ⌈Real.logb 2 L⌉₊ with hndef
  have hlb0 : 0 ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) hL1
  have hle : Real.logb 2 L ≤ (n : ℝ) := Nat.le_ceil _
  have hLpow : L ≤ ((2 ^ n : ℕ) : ℝ) := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 L) = L := Real.rpow_logb (by norm_num) (by norm_num) hL0
    have h2 : (2 : ℝ) ^ (Real.logb 2 L) ≤ (2 : ℝ) ^ ((n : ℕ) : ℝ) :=
      Real.rpow_le_rpow_left_iff (by norm_num) |>.2 hle
    rw [h1] at h2
    rw [Real.rpow_natCast] at h2
    exact_mod_cast h2
  have hNy : (y : ℝ) ≤ v ^ (2 ^ n) := by
    have hlog : Real.log y ≤ Real.log (v ^ (2 ^ n)) := by
      rw [Real.log_pow]
      have : L * Real.log v ≤ ((2 ^ n : ℕ) : ℝ) * Real.log v :=
        mul_le_mul_of_nonneg_right hLpow hlogv.le
      rw [hLdef, div_mul_cancel₀ _ hlogv.ne'] at this
      exact this
    have hpos : (0 : ℝ) < v ^ (2 ^ n) := by positivity
    exact (Real.log_le_log_iff hy0 hpos).1 hlog
  refine le_trans (primeRecipSum_le_blocks n v hv y hNy) ?_
  -- `n ≤ logb 2 L + 1` and `8 / log 2 ≤ 12`
  have hn1 : (n : ℝ) < Real.logb 2 L + 1 := Nat.ceil_lt_add_one hlb0
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogb : Real.logb 2 L = Real.log L / Real.log 2 := rfl
  have hkey : 8 * Real.logb 2 L ≤ 12 * Real.log L := by
    rw [hlogb, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

/-! ### The dimension estimate -/

/-- **The prime-density dimension estimate.**  For a finite set `U` of primes in `(h, y]`,
the tail products of `g p = h / p` obey the `Brun.Dimension` bound with
`K = 4 ^ h exp (16 h)` and dimension `24 h`. -/
theorem prime_density_dimension {h y : ℕ} (hh : 1 ≤ h) (hy : 2 ≤ y) {U : Finset ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p ∧ h < p ∧ p ≤ y) :
    Brun.Dimension U (fun p => (h : ℝ) / p) y ((4 : ℝ) ^ h * Real.exp (16 * h)) (24 * h) := by
  intro t ht1 hty
  set v := max 2 t with hvdef
  have hv2 : (2 : ℝ) ≤ v := le_max_left _ _
  have hvt : t ≤ v := le_max_right _ _
  have hv0 : (0 : ℝ) < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hvy : v ≤ (y : ℝ) := max_le (by exact_mod_cast hy) hty
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le hv0 hvy
  set L := Real.log y / Real.log v with hLdef
  have hL1 : 1 ≤ L := (one_le_div hlogv).2 (Real.log_le_log hv0 hvy)
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  set F := U.filter (fun p : ℕ => t < (p : ℝ)) with hFdef
  -- factors are nonnegative
  have hfac0 : ∀ p ∈ U, (0 : ℝ) ≤ (1 - (h : ℝ) / p)⁻¹ := by
    intro p hp
    obtain ⟨hpp, hhp, -⟩ := hU p hp
    have hp0 : (0 : ℝ) < p := by have := hpp.two_le; positivity
    have : (h : ℝ) / p ≤ 1 := by
      rw [div_le_one hp0]; exact_mod_cast hhp.le
    have : (0 : ℝ) ≤ 1 - (h : ℝ) / p := by linarith
    positivity
  rw [← Finset.prod_filter_mul_prod_filter_not F (fun p : ℕ => p ≤ 2 * h)]
  -- Part A: the small primes `h < p ≤ 2h`
  have hA : ∏ p ∈ F.filter (fun p : ℕ => p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹ ≤ (4 : ℝ) ^ h := by
    have hsubset : F.filter (fun p : ℕ => p ≤ 2 * h) ⊆ Finset.Ioc h (2 * h) := by
      intro p hp
      simp only [Finset.mem_filter, hFdef] at hp
      exact Finset.mem_Ioc.2 ⟨(hU p hp.1.1).2.1, hp.2⟩
    have hone : ∀ m ∈ Finset.Ioc h (2 * h), (1 : ℝ) ≤ (1 - (h : ℝ) / m)⁻¹ := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.1 hm
      have hm0 : (0 : ℝ) < m := by
        have : 0 < m := lt_of_le_of_lt (Nat.zero_le h) hm1
        exact_mod_cast this
      have hle : (h : ℝ) / m ≤ 1 := by
        rw [div_le_one hm0]; exact_mod_cast hm1.le
      have hpos : (0 : ℝ) < 1 - (h : ℝ) / m := by
        have : (h : ℝ) / m < 1 := by
          rw [div_lt_one hm0]; exact_mod_cast hm1
        linarith
      rw [le_inv_comm₀ one_pos hpos]
      simpa using div_nonneg (Nat.cast_nonneg h) hm0.le
    calc ∏ p ∈ F.filter (fun p : ℕ => p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹
        ≤ ∏ m ∈ Finset.Ioc h (2 * h), (1 - (h : ℝ) / m)⁻¹ :=
          Finset.prod_le_prod_of_subset_of_one_le hsubset
            (fun p hp => hfac0 p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
            (fun m hm _ => hone m hm)
      _ = ((2 * h).choose h : ℝ) := prod_Ioc_inv_eq_centralBinom h
      _ ≤ (4 : ℝ) ^ h := by
          have := Nat.centralBinom_le_four_pow h
          rw [Nat.centralBinom_eq_two_mul_choose] at this
          exact_mod_cast this
  -- Part B: the large primes `p > 2h`
  have hB : ∏ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹
      ≤ Real.exp (16 * h) * L ^ (24 * h) := by
    have hstep : ∀ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h),
        (1 - (h : ℝ) / p)⁻¹ ≤ Real.exp (2 * ((h : ℝ) / p)) := by
      intro p hp
      simp only [Finset.mem_filter, not_le, hFdef] at hp
      have hp2h : 2 * h < p := hp.2
      have hp0 : (0 : ℝ) < p := by
        have : 0 < p := by omega
        exact_mod_cast this
      refine inv_one_sub_le_exp (by positivity) ?_
      rw [div_le_iff₀ hp0]
      have : (2 * h : ℕ) < (p : ℕ) := hp2h
      have hcast : (2 : ℝ) * h < p := by exact_mod_cast this
      linarith
    have hsum : ∑ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 : ℝ) / p ≤ 8 + 12 * Real.log L := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by positivity))
        (primeRecipSum_le v hv2 y hvy)
      intro p hp
      simp only [Finset.mem_filter, not_le, hFdef] at hp
      obtain ⟨⟨hpU, hpt⟩, hp2h⟩ := hp
      obtain ⟨hpp, hhp, hpy⟩ := hU p hpU
      have hvp : v < (p : ℝ) := by
        rcases max_cases 2 t with ⟨he, -⟩ | ⟨he, -⟩
        · rw [hvdef, he]
          have : 2 * h < p := hp2h
          have : (2 : ℕ) < p := by omega
          exact_mod_cast this
        · rw [hvdef, he]; exact hpt
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨hpy, hpp, hvp⟩
    calc ∏ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹
        ≤ ∏ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), Real.exp (2 * ((h : ℝ) / p)) :=
          Finset.prod_le_prod (fun p hp => hfac0 p (Finset.mem_filter.1
            (Finset.mem_filter.1 hp).1).1) hstep
      _ = Real.exp (∑ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), 2 * ((h : ℝ) / p)) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * (h : ℝ) * (8 + 12 * Real.log L)) := by
          refine Real.exp_le_exp.2 ?_
          have hrw : ∑ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), 2 * ((h : ℝ) / p)
              = 2 * (h : ℝ) * ∑ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 : ℝ) / p := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by ring
          rw [hrw]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (16 * h) * L ^ (24 * h) := by
          have hpow : L ^ (24 * h) = Real.exp ((24 * (h:ℝ)) * Real.log L) := by
            rw [← Real.rpow_natCast L (24 * h), Real.rpow_def_of_pos hL0]
            push_cast
            ring_nf
          rw [hpow, ← Real.exp_add]
          congr 1
          ring
  have hAnn : (0 : ℝ) ≤ ∏ p ∈ F.filter (fun p : ℕ => p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹ :=
    Finset.prod_nonneg (fun p hp => hfac0 p (Finset.mem_filter.1
      (Finset.mem_filter.1 hp).1).1)
  have hBnn : (0 : ℝ) ≤ ∏ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹ :=
    Finset.prod_nonneg (fun p hp => hfac0 p (Finset.mem_filter.1
      (Finset.mem_filter.1 hp).1).1)
  calc (∏ p ∈ F.filter (fun p : ℕ => p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹) *
        ∏ p ∈ F.filter (fun p : ℕ => ¬ p ≤ 2 * h), (1 - (h : ℝ) / p)⁻¹
      ≤ (4 : ℝ) ^ h * (Real.exp (16 * h) * L ^ (24 * h)) :=
        mul_le_mul hA hB hBnn (by positivity)
    _ = (4 : ℝ) ^ h * Real.exp (16 * h) * L ^ (24 * h) := by ring

/-! ### The lower Brun sieve at the prime density -/

open NormalNumbers.PrimeModel.Brun in
/-- **The lower Brun sieve for `g p = h / p` on primes in `(h, y]`.**  `brun_lower_fundamental`
instantiated with the dimension estimate of `prime_density_dimension`: no analytic hypothesis
remains, only the elementary size conditions on `U, h, y, s`. -/
theorem prime_density_brun_lower {h y : ℕ} (hh : 1 ≤ h) {s : ℝ} (hy : Real.exp 2 ≤ (y : ℝ))
    (hs80 : 80 * ((24 * h : ℕ) : ℝ) ≤ s)
    (hsA : 40 * Real.log ((4 : ℝ) ^ h * Real.exp (16 * h)) + 4 ≤ s)
    {U : Finset ℕ} (hU : ∀ p ∈ U, Nat.Prime p ∧ h < p ∧ p ≤ y) :
    (∀ E ⊆ U, |lam (brunCut (24 * h) s y) E| ≤ 1 ∧
        (lam (brunCut (24 * h) s y) E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ (y : ℝ) ^ s)) ∧
      (∀ B ⊆ U, ∑ E ∈ B.powerset, lam (brunCut (24 * h) s y) E ≤ if B = ∅ then 1 else 0) ∧
      (1 - 2 * Real.exp (-s / 2)) * ∏ p ∈ U, (1 - (h : ℝ) / p)
        ≤ ∑ E ∈ U.powerset, lam (brunCut (24 * h) s y) E * ∏ p ∈ E, (h : ℝ) / p := by
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := le_trans he2 hy
  have hy2 : 2 ≤ y := by exact_mod_cast hy2R
  have hk : 1 ≤ 24 * h := by omega
  have hK : (1 : ℝ) ≤ (4 : ℝ) ^ h * Real.exp (16 * h) := by
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ h := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp (16 * h) := Real.one_le_exp (by positivity)
    nlinarith
  have hg0 : ∀ p ∈ U, (0 : ℝ) ≤ (h : ℝ) / p := by
    intro p _; positivity
  have hg1 : ∀ p ∈ U, (h : ℝ) / p < 1 := by
    intro p hp
    obtain ⟨hpp, hhp, -⟩ := hU p hp
    have hp0 : (0 : ℝ) < p := by have := hpp.two_le; positivity
    rw [div_lt_one hp0]; exact_mod_cast hhp
  exact brun_lower_fundamental hk hK hy hs80 hsA hg0 hg1 (fun p hp => (hU p hp).2.2)
    (by omega) (prime_density_dimension hh hy2 hU)

end NormalNumbers.PrimeModel.PrimeDensity

