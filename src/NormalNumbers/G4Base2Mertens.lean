/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointMertensLower

/-!
# Mertens on log-windows

`mertens_window` (from the explicit Mertens first theorem) and `sum_inv_primes_Y102_le`:
the primes in `(Y, Y^{102}]` have reciprocal mass `≤ 5` once `log Y ≥ 13860`
(blocks of log-width `log Y / 20`, harmonic tail `≤ log(2039/19) ≤ 7 log 2`).
-/

open Finset
namespace NormalNumbers.G4.Base2
open NormalNumbers.CastingOut

lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.floor_eq_zero]; linarith)
  linarith

/-- Mertens on a log-window: `Σ_{e^a < p ≤ e^b} log p / p ≤ b − a + 12`. -/
lemma mertens_window {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ primesLe ⌊Real.exp b⌋₊ \ primesLe ⌊Real.exp a⌋₊, Real.log p / (p : ℝ) ≤ b - a + 12 := by
  have hea : 1 ≤ Real.exp a := Real.one_le_exp ha
  have heb : 1 ≤ Real.exp b := Real.one_le_exp (ha.trans hab)
  have hN1 : 1 ≤ ⌊Real.exp a⌋₊ := Nat.one_le_iff_ne_zero.2 (by rw [Ne, Nat.floor_eq_zero]; linarith)
  have hN2 : 1 ≤ ⌊Real.exp b⌋₊ := Nat.one_le_iff_ne_zero.2 (by rw [Ne, Nat.floor_eq_zero]; linarith)
  have hsub : primesLe ⌊Real.exp a⌋₊ ⊆ primesLe ⌊Real.exp b⌋₊ := by
    intro p hp
    simp only [primesLe, mem_filter, mem_range] at hp ⊢
    exact ⟨by have := Nat.floor_le_floor (R := ℝ) (Real.exp_le_exp.2 hab); omega, hp.2⟩
  have hsd := sum_sdiff hsub (f := fun p : ℕ => Real.log p / (p : ℝ))
  have hU := mertens_upper _ hN2
  have hL := mertens_lower _ hN1
  have hlb : Real.log ⌊Real.exp b⌋₊ ≤ b := by
    have := Real.log_le_log (by exact_mod_cast hN2) (Nat.floor_le (by linarith : (0:ℝ) ≤ Real.exp b))
    rwa [Real.log_exp] at this
  have hla : a - Real.log 2 ≤ Real.log ⌊Real.exp a⌋₊ := by
    have := Real.log_le_log (by positivity) (half_le_floor hea)
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_exp] at this
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

/-- `Σ_{i<n} 1/(a+i) ≤ log(a+n−1) − log(a−1)` for `a ≥ 2`. -/
lemma sum_inv_le_log (a : ℕ) (ha : 2 ≤ a) : ∀ n : ℕ,
    ∑ i ∈ range n, ((a + i : ℕ) : ℝ)⁻¹ ≤ Real.log ((a + n - 1 : ℕ) : ℝ) - Real.log ((a - 1 : ℕ) : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ]
    have ih := sum_inv_le_log a ha n
    have hk : (2 : ℝ) ≤ ((a + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ a + n)
    have e1 : ((a + (n + 1) - 1 : ℕ) : ℝ) = ((a + n : ℕ) : ℝ) := by congr 1
    have e2 : ((a + n - 1 : ℕ) : ℝ) = ((a + n : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [e1]; rw [e2] at ih
    have := Real.log_le_sub_one_of_pos (x := (((a + n : ℕ) : ℝ) - 1) / ((a + n : ℕ) : ℝ))
      (by apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith)] at this
    have h3 : (((a + n : ℕ) : ℝ) - 1) / ((a + n : ℕ) : ℝ) - 1 = -((a + n : ℕ) : ℝ)⁻¹ := by
      field_simp; ring
    linarith

/-- The primes in `(Y, Y^{102}]` have reciprocal mass `≤ 5` once `Y ≥ 2^{20000}`. -/
theorem sum_inv_primes_Y102_le {Y : ℕ} (hlogY : 13860 ≤ Real.log Y) :
    ∑ p ∈ (range (Y ^ 102 + 1)).filter (fun p => p.Prime ∧ Y < p), (p : ℝ)⁻¹ ≤ 5 := by
  set W := (range (Y ^ 102 + 1)).filter (fun p => p.Prime ∧ Y < p) with hW
  have hY1 : (1 : ℝ) < Y := (Real.log_pos_iff (Nat.cast_nonneg _)).1 (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  set ℓ := Real.log Y / 20 with hℓ
  have hℓ0 : 693 ≤ ℓ := by rw [hℓ]; linarith
  have hℓpos : 0 < ℓ := by linarith
  -- block index
  set g : ℕ → ℕ := fun p => ⌈Real.log p / ℓ⌉₊ - 21 with hg
  have hblk : ∀ p ∈ W, g p ∈ range 2020 ∧ ((20 + g p : ℕ) : ℝ) * ℓ < Real.log p ∧
      Real.log p ≤ ((21 + g p : ℕ) : ℝ) * ℓ := by
    intro p hp
    rw [hW, mem_filter, mem_range] at hp
    have hpY : (Y : ℝ) < p := by exact_mod_cast hp.2.2
    have hpM : (p : ℝ) ≤ (Y : ℝ) ^ 102 := by exact_mod_cast (by omega : p ≤ Y ^ 102)
    have h1 : Real.log Y < Real.log p := Real.log_lt_log (by linarith) hpY
    have h2 : Real.log p ≤ 102 * Real.log Y := by
      have := Real.log_le_log (by linarith) hpM
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hr1 : 20 < Real.log p / ℓ := by rw [lt_div_iff₀ hℓpos]; rw [hℓ]; linarith
    have hr2 : Real.log p / ℓ ≤ 2040 := by rw [div_le_iff₀ hℓpos]; rw [hℓ]; linarith
    set c := ⌈Real.log p / ℓ⌉₊ with hc
    have hc1 : Real.log p / ℓ ≤ c := Nat.le_ceil _
    have hc2 : (c : ℝ) < Real.log p / ℓ + 1 := Nat.ceil_lt_add_one (by linarith)
    have hc21 : 21 ≤ c := by
      have : (20 : ℝ) < c := by linarith
      exact_mod_cast (show (20 : ℝ) < c from this)
    have hc2040 : c ≤ 2040 := Nat.ceil_le.2 (by exact_mod_cast hr2)
    have hgc : ((21 + g p : ℕ) : ℝ) = c := by
      simp only [hg]; rw [← hc]; congr 1; omega
    have hgc' : ((20 + g p : ℕ) : ℝ) = c - 1 := by
      rw [show 20 + g p = (21 + g p) - 1 by omega, Nat.cast_sub (by omega), hgc]; simp
    refine ⟨mem_range.2 (by simp only [hg]; omega), ?_, ?_⟩
    · rw [hgc']
      have := (lt_div_iff₀ hℓpos).1 (by linarith : (c : ℝ) - 1 < Real.log p / ℓ)
      linarith
    · rw [hgc]; exact (div_le_iff₀ hℓpos).1 hc1
  rw [← sum_fiberwise_of_maps_to (g := g) (t := range 2020) (fun p hp => (hblk p hp).1)]
  have hfib : ∀ i ∈ range 2020, ∑ p ∈ W with g p = i, (p : ℝ)⁻¹
      ≤ (1 + 12 / ℓ) * ((20 + i : ℕ) : ℝ)⁻¹ := by
    intro i _
    have hk : (20 : ℝ) ≤ ((20 + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 20 ≤ 20 + i)
    have hkℓ : 0 < ((20 + i : ℕ) : ℝ) * ℓ := by positivity
    have hpt : ∀ p ∈ W.filter (fun p => g p = i),
        (p : ℝ)⁻¹ ≤ (((20 + i : ℕ) : ℝ) * ℓ)⁻¹ * (Real.log p / (p : ℝ)) := by
      intro p hp
      obtain ⟨hpW, hgi⟩ := mem_filter.1 hp
      obtain ⟨-, hlo, -⟩ := hblk p hpW
      rw [hgi] at hlo
      have hp0 : (0 : ℝ) < p := by
        have := (mem_filter.1 hpW).2.1.pos; exact_mod_cast this
      rw [inv_mul_eq_div, div_div, le_div_iff₀ (by positivity), inv_mul_eq_div,
        mul_div_cancel_left₀ _ hp0.ne']
      linarith
    have hsubW : W.filter (fun p => g p = i) ⊆
        primesLe ⌊Real.exp (((21 + i : ℕ) : ℝ) * ℓ)⌋₊ \ primesLe ⌊Real.exp (((20 + i : ℕ) : ℝ) * ℓ)⌋₊ := by
      intro p hp
      obtain ⟨hpW, hgi⟩ := mem_filter.1 hp
      obtain ⟨-, hlo, hhi⟩ := hblk p hpW
      rw [hgi] at hlo hhi
      have hpr := (mem_filter.1 hpW).2.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      rw [mem_sdiff]
      simp only [primesLe, mem_filter, mem_range]
      refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hpr⟩, fun h => ?_⟩
      · rw [← Real.exp_log hp0]; exact Real.exp_le_exp.2 hhi
      · have h1 : (p : ℝ) ≤ ⌊Real.exp (((20 + i : ℕ) : ℝ) * ℓ)⌋₊ := by exact_mod_cast (by omega)
        have h2 := Nat.floor_le (Real.exp_pos (((20 + i : ℕ) : ℝ) * ℓ)).le
        have h3 := Real.log_le_log hp0 (h1.trans h2)
        rw [Real.log_exp] at h3
        linarith
    have hw := mertens_window (a := ((20 + i : ℕ) : ℝ) * ℓ) (b := ((21 + i : ℕ) : ℝ) * ℓ)
      (by positivity) (by gcongr; omega)
    have hw' : ((21 + i : ℕ) : ℝ) * ℓ - ((20 + i : ℕ) : ℝ) * ℓ = ℓ := by push_cast; ring
    rw [hw'] at hw
    calc ∑ p ∈ W with g p = i, (p : ℝ)⁻¹
        ≤ ∑ p ∈ W with g p = i, (((20 + i : ℕ) : ℝ) * ℓ)⁻¹ * (Real.log p / (p : ℝ)) :=
          sum_le_sum hpt
      _ = (((20 + i : ℕ) : ℝ) * ℓ)⁻¹ * ∑ p ∈ W with g p = i, Real.log p / (p : ℝ) := by
          rw [mul_sum]
      _ ≤ (((20 + i : ℕ) : ℝ) * ℓ)⁻¹ * (ℓ + 12) := by
          gcongr
          refine (sum_le_sum_of_subset_of_nonneg hsubW fun p hp _ => ?_).trans hw
          have := (mem_filter.1 (mem_sdiff.1 hp).1).2.pos
          have : (1 : ℝ) ≤ p := by exact_mod_cast this
          exact div_nonneg (Real.log_nonneg this) (by linarith)
      _ = (1 + 12 / ℓ) * ((20 + i : ℕ) : ℝ)⁻¹ := by field_simp
  refine (sum_le_sum hfib).trans ?_
  rw [← mul_sum]
  have hH := sum_inv_le_log 20 (by norm_num) 2020
  have e : ((20 - 1 : ℕ) : ℝ) = 19 := by norm_num
  have e' : ((20 + 2020 - 1 : ℕ) : ℝ) = 2039 := by norm_num
  rw [e, e', ← Real.log_div (by norm_num) (by norm_num)] at hH
  have h128 : Real.log (2039 / 19) ≤ 7 * Real.log 2 := by
    calc Real.log (2039 / 19) ≤ Real.log (2 ^ 7) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hq : 12 / ℓ ≤ 12 / 693 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hℓ0
  have hS0 : 0 ≤ ∑ i ∈ range 2020, ((20 + i : ℕ) : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
  calc (1 + 12 / ℓ) * ∑ i ∈ range 2020, ((20 + i : ℕ) : ℝ)⁻¹
      ≤ (1 + 12 / 693) * (7 * Real.log 2) :=
        mul_le_mul (by linarith) (hH.trans h128) hS0 (by norm_num)
    _ ≤ 5 := by linarith
end NormalNumbers.G4.Base2
