/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadThreshold
import NormalNumbers.UniformBadPowerEngine

/-!
# `c⋆ ≤ 12`: the power engine on all bases

The power engine (`exists_avoid_powPot`) with `K = 4096`, `α = 1/4`, `ρ = 1/81`, on the
obstacles `(b, n, a)`, `n ≥ 1`, of radius `b^{−n−12}` around `a/bⁿ`, charged at the stage
`k + 1` with `4096^k ≤ 8bⁿ < 4096^{k+1}` (so `t = ℓ_k bⁿ ∈ [1/16, 256)`).

Per level the averaged new charge is `(t + 1 + 2b^{−12})(2v + 2)v^{1/4}`, `v = 4096 b^{−12}/t`;
summing the geometric levels gives `≤ 3886 b^{−3}` per base, and `Σ_b b^{−3} ≤ 1/4`.
-/

namespace NormalNumbers.UniformBadThreshold

/-! ## Geometric level sums -/

/-- Increasing geometric levels below `T`: `Σ (s₀bⁿ)^p ≤ T^p/(1 − q)` for `b^{−p} ≤ q < 1`. -/
theorem sum_geom_rpow_le (N : Finset ℕ) {s₀ b p q T : ℝ} (hs₀ : 0 < s₀) (hb : 1 < b)
    (hp : 0 < p) (hq : b ^ (-p) ≤ q) (hq1 : q < 1) (hT0 : 0 < T)
    (hT : ∀ n ∈ N, s₀ * b ^ n ≤ T) :
    ∑ n ∈ N, (s₀ * b ^ n) ^ p ≤ T ^ p / (1 - q) := by
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hb0 _).le.trans hq
  rcases N.eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg hT0.le _) (by linarith)
  have key : ∀ m : ℕ, ((b ^ m)⁻¹ : ℝ) ^ p = (b ^ (-p)) ^ m := by
    intro m
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast b m, ← Real.rpow_mul hb0.le,
      ← Real.rpow_natCast (b ^ (-p)) m, ← Real.rpow_mul hb0.le, ← Real.rpow_neg hb0.le]
    ring_nf
  set M := N.max' h
  have hTM : s₀ * b ^ M ≤ T := hT M (N.max'_mem h)
  have hterm : ∀ n ∈ N, (s₀ * b ^ n) ^ p ≤ T ^ p * q ^ (M - n) := by
    intro n hn
    have hnM : n ≤ M := N.le_max' n hn
    have e : s₀ * b ^ n = (s₀ * b ^ M) * (b ^ (M - n))⁻¹ := by
      rw [show M = n + (M - n) by omega, pow_add]
      field_simp
      rw [Nat.add_sub_cancel_left]
    rw [e, Real.mul_rpow (by positivity) (by positivity), key]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) hTM hp.le)
      (pow_le_pow_left₀ (Real.rpow_pos_of_pos hb0 _).le hq _) (by positivity)
      (Real.rpow_nonneg hT0.le _)
  calc ∑ n ∈ N, (s₀ * b ^ n) ^ p ≤ ∑ n ∈ N, T ^ p * q ^ (M - n) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range (M + 1), T ^ p * q ^ (M - n) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_range.2
          (Nat.lt_succ_of_le (N.le_max' n hn))) fun _ _ _ => by positivity
    _ = T ^ p * ∑ j ∈ Finset.range (M + 1), q ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        congr 2; omega
    _ ≤ T ^ p * (1 / (1 - q)) := by
        gcongr
        rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
        linarith [pow_nonneg hq0 (M + 1)]
    _ = T ^ p / (1 - q) := by ring


/-- Increasing geometric levels above `μ`: `Σ (s₀bⁿ)^{−p} ≤ μ^{−p}/(1 − q)` for `b^{−p} ≤ q < 1`. -/
theorem sum_geom_rpow_neg_le (N : Finset ℕ) {s₀ b p q μ : ℝ} (hs₀ : 0 < s₀) (hb : 1 < b)
    (hp : 0 < p) (hq : b ^ (-p) ≤ q) (hq1 : q < 1) (hμ : 0 < μ)
    (hμN : ∀ n ∈ N, μ ≤ s₀ * b ^ n) :
    ∑ n ∈ N, (s₀ * b ^ n) ^ (-p) ≤ μ ^ (-p) / (1 - q) := by
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hb0 _).le.trans hq
  rcases N.eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg hμ.le _) (by linarith)
  set m := N.min' h
  set M := N.max' h
  have hμm : μ ≤ s₀ * b ^ m := hμN m (N.min'_mem h)
  have key : ∀ j : ℕ, ((b : ℝ) ^ j) ^ (-p) = (b ^ (-p)) ^ j := by
    intro j
    rw [← Real.rpow_natCast b j, ← Real.rpow_mul hb0.le, ← Real.rpow_natCast (b ^ (-p)) j,
      ← Real.rpow_mul hb0.le]
    ring_nf
  have hterm : ∀ n ∈ N, (s₀ * b ^ n) ^ (-p) ≤ μ ^ (-p) * q ^ (n - m) := by
    intro n hn
    have hmn : m ≤ n := N.min'_le n hn
    have e : s₀ * b ^ n = (s₀ * b ^ m) * b ^ (n - m) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
    rw [e, Real.mul_rpow (by positivity) (by positivity), key]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hμ hμm (by linarith))
      (pow_le_pow_left₀ (Real.rpow_pos_of_pos hb0 _).le hq _) (by positivity)
      (Real.rpow_nonneg hμ.le _)
  calc ∑ n ∈ N, (s₀ * b ^ n) ^ (-p) ≤ ∑ n ∈ N, μ ^ (-p) * q ^ (n - m) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ico m (M + 1), μ ^ (-p) * q ^ (n - m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_Ico.2
          ⟨N.min'_le n hn, Nat.lt_succ_of_le (N.le_max' n hn)⟩) fun _ _ _ => by positivity
    _ = μ ^ (-p) * ∑ j ∈ Finset.range (M + 1 - m), q ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 2; omega
    _ ≤ μ ^ (-p) * (1 / (1 - q)) := by
        gcongr
        rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
        linarith [pow_nonneg hq0 (M + 1 - m)]
    _ = μ ^ (-p) / (1 - q) := by ring

/-- Integers `a` whose obstacle `[a/B − r, a/B + r]` meets `[x, x + ℓ]` number at most
`(ℓ + 2r)B + 1`. -/
theorem card_int_meet_le {B r x ℓ : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hℓ : 0 ≤ ℓ) :
    ∃ F : Finset ℤ, {a : ℤ | (Set.Icc ((a : ℝ) / B - r) (a / B + r) ∩
      Set.Icc x (x + ℓ)).Nonempty} ⊆ F ∧ (F.card : ℝ) ≤ (ℓ + 2 * r) * B + 1 := by
  refine ⟨Finset.Icc ⌈B * (x - r)⌉ ⌊B * (x + ℓ + r)⌋, ?_, ?_⟩
  · rintro a ⟨y, ⟨h1, h2⟩, h3, h4⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rw [Int.ceil_le]
      have : x - r ≤ a / B := by linarith
      rw [le_div_iff₀ hB] at this; linarith
    · rw [Int.le_floor]
      have : (a : ℝ) / B ≤ x + ℓ + r := by linarith
      rw [div_le_iff₀ hB] at this; linarith
  · rw [Int.card_Icc]
    set z := ⌊B * (x + ℓ + r)⌋ + 1 - ⌈B * (x - r)⌉
    have hz : (z : ℝ) ≤ (ℓ + 2 * r) * B + 1 := by
      simp only [z]; push_cast
      have := Int.floor_le (B * (x + ℓ + r)); have := Int.le_ceil (B * (x - r)); nlinarith
    rcases le_or_gt 0 z with h0 | h0
    · rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg h0]; exact hz
    · rw [Int.toNat_of_nonpos h0.le]; push_cast; positivity

/-! ## The per-base level sum -/

theorem rpow_le_of_pow4 {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (h : a ^ 4 ≤ y ^ 4) : a ≤ y :=
  (pow_le_pow_iff_left₀ ha hy (by norm_num)).1 h

theorem two_rpow_neg_le {p y : ℝ} (hy : 0 ≤ y) (h : (2 : ℝ) ^ (-(4 * p)) ≤ y ^ 4) :
    (2 : ℝ) ^ (-p) ≤ y := by
  refine rpow_le_of_pow4 (by positivity) hy ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  convert h using 2; push_cast; ring

theorem base_rpow_neg_le {b p : ℝ} (hb : 2 ≤ b) (hp : 0 ≤ p) : b ^ (-p) ≤ 2 ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos (by norm_num) hb (by linarith)

/-- The per-base level sum at `c = 12`, `K = 4096`, `α = 1/4`. -/
theorem level_sum_le {b ℓ : ℝ} (hb : 2 ≤ b) (hℓ : 0 < ℓ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 1 / 16 ≤ ℓ * b ^ n ∧ ℓ * b ^ n ≤ 256) :
    ∑ n ∈ N, ((ℓ + 2 * (b ^ (n + 12))⁻¹) * b ^ n + 1) *
        (2 * ((b ^ (n + 12))⁻¹ / (ℓ / 4096)) + 2) * ((b ^ (n + 12))⁻¹ / (ℓ / 4096)) ^ (1/4 : ℝ)
      ≤ 3886 / b ^ 3 := by
  have hb0 : 0 < b := by linarith
  set γ : ℝ := (b ^ 3)⁻¹ with hγ
  set β : ℝ := (b ^ 12)⁻¹ with hβ
  have hγ0 : 0 < γ := by positivity
  have hβγ : β = γ ^ 4 := by rw [hβ, hγ, inv_pow, ← pow_mul]
  have hβle : β ≤ 1 / 4096 := by
    rw [hβ, one_div]
    exact inv_anti₀ (by norm_num) (by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hb 12; norm_num at this ⊢; linarith)
  have hβ0 : 0 ≤ β := by positivity
  -- rewrite each term
  have hterm : ∀ n ∈ N, ((ℓ + 2 * (b ^ (n + 12))⁻¹) * b ^ n + 1) *
        (2 * ((b ^ (n + 12))⁻¹ / (ℓ / 4096)) + 2) * ((b ^ (n + 12))⁻¹ / (ℓ / 4096)) ^ (1/4 : ℝ)
      = 8 * γ * (2 * (ℓ * b ^ n) ^ (3/4 : ℝ) + (4 * β + 2 + 8192 * β) * (ℓ * b ^ n) ^ (-(1/4) : ℝ)
          + 8192 * β * (2 * β + 1) * (ℓ * b ^ n) ^ (-(5/4) : ℝ)) := by
    intro n hn
    set t := ℓ * b ^ n with ht
    have ht0 : 0 < t := by positivity
    have hrb : (b ^ (n + 12))⁻¹ * b ^ n = β := by
      rw [hβ, pow_add]; field_simp
    have hv : (b ^ (n + 12))⁻¹ / (ℓ / 4096) = (8 * γ) ^ 4 / t := by
      rw [show (8 * γ) ^ 4 = 4096 * β by rw [hβγ]; ring, ← hrb, ht]
      field_simp
    have hq : ((8 * γ) ^ 4 / t) ^ (1/4 : ℝ) = 8 * γ * t ^ (-(1/4) : ℝ) := by
      rw [Real.div_rpow (by positivity) ht0.le, Real.rpow_neg ht0.le, div_eq_mul_inv]
      congr 1
      rw [show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    have h34 : t ^ (3/4 : ℝ) = t * t ^ (-(1/4) : ℝ) := by
      rw [← Real.rpow_one_add' ht0.le (by norm_num)]; norm_num
    have h54 : t ^ (-(5/4) : ℝ) = t⁻¹ * t ^ (-(1/4) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
    have hlin : (ℓ + 2 * (b ^ (n + 12))⁻¹) * b ^ n = t + 2 * β := by
      rw [← hrb, ht]; ring
    rw [hlin, hv, hq, h34, h54]
    have h4 : (8 * γ) ^ 4 = 4096 * β := by rw [hβγ]; ring
    rw [h4]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  -- the three geometric sums
  have hℓpos := hℓ
  have hS1 : ∑ n ∈ N, (ℓ * b ^ n) ^ (3/4 : ℝ) ≤ 64 / (1 - 0.6) := by
    have := sum_geom_rpow_le N hℓ (by linarith : (1:ℝ) < b) (by norm_num : (0:ℝ) < 3/4)
      ((base_rpow_neg_le hb (by norm_num)).trans (two_rpow_neg_le (y := 0.6) (by norm_num) (by
        rw [show -(4 * (3/4 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num)))
      (by norm_num) (by norm_num : (0:ℝ) < 256) (fun n hn => (hN n hn).2)
    refine this.trans (le_of_eq ?_)
    rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hS2 : ∑ n ∈ N, (ℓ * b ^ n) ^ (-(1/4) : ℝ) ≤ 2 / (1 - 0.85) := by
    have := sum_geom_rpow_neg_le N hℓ (by linarith : (1:ℝ) < b) (by norm_num : (0:ℝ) < 1/4)
      ((base_rpow_neg_le hb (by norm_num)).trans (two_rpow_neg_le (y := 0.85) (by norm_num) (by
        rw [show -(4 * (1/4 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num)))
      (by norm_num) (by norm_num : (0:ℝ) < 1/16) (fun n hn => (hN n hn).1)
    refine this.trans (le_of_eq ?_)
    rw [show (1/16 : ℝ) = 2 ^ (-4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hS3 : ∑ n ∈ N, (ℓ * b ^ n) ^ (-(5/4) : ℝ) ≤ 32 / (1 - 0.43) := by
    have := sum_geom_rpow_neg_le N hℓ (by linarith : (1:ℝ) < b) (by norm_num : (0:ℝ) < 5/4)
      ((base_rpow_neg_le hb (by norm_num)).trans (two_rpow_neg_le (y := 0.43) (by norm_num) (by
        rw [show -(4 * (5/4 : ℝ)) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num)))
      (by norm_num) (by norm_num : (0:ℝ) < 1/16) (fun n hn => (hN n hn).1)
    refine this.trans (le_of_eq ?_)
    rw [show (1/16 : ℝ) = 2 ^ (-4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hS10 : 0 ≤ ∑ n ∈ N, (ℓ * b ^ n) ^ (3/4 : ℝ) :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
  have hS20 : 0 ≤ ∑ n ∈ N, (ℓ * b ^ n) ^ (-(1/4) : ℝ) :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
  have hS30 : 0 ≤ ∑ n ∈ N, (ℓ * b ^ n) ^ (-(5/4) : ℝ) :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _
  have hγb : 3886 / b ^ 3 = 3886 * γ := by rw [hγ]; ring
  rw [hγb]
  have hc2 : 4 * β + 2 + 8192 * β ≤ 4.001 := by linarith
  have hc3 : 8192 * β * (2 * β + 1) ≤ 2.001 := by nlinarith
  have hinner : 2 * ∑ n ∈ N, (ℓ * b ^ n) ^ (3/4 : ℝ) +
      (4 * β + 2 + 8192 * β) * ∑ n ∈ N, (ℓ * b ^ n) ^ (-(1/4) : ℝ) +
      8192 * β * (2 * β + 1) * ∑ n ∈ N, (ℓ * b ^ n) ^ (-(5/4) : ℝ) ≤ 485.75 := by
    have e1 := mul_le_mul hc2 hS2 hS20 (by norm_num)
    have e2 := mul_le_mul hc3 hS3 hS30 (by norm_num)
    norm_num at hS1 e1 e2 ⊢
    linarith
  nlinarith

end NormalNumbers.UniformBadThreshold
