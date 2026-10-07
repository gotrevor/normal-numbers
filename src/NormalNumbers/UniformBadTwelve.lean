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

open scoped ENNReal

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


/-- Real base-weight sum: `Σ_{b ≥ 2} 3886/b³ ≤ 3886/4`. -/
theorem tsum_base_cube_le :
    ∑' b : ℕ, (if 2 ≤ b then 3886 / (b : ℝ) ^ 3 else 0) ≤ 3886 / 4 ∧
    Summable (fun b : ℕ => if 2 ≤ b then 3886 / (b : ℝ) ^ 3 else 0) := by
  set g : ℕ → ℝ := fun b => if 2 ≤ b then 3886 / (b : ℝ) ^ 3 else 0 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => by simp only [hg]; split_ifs <;> positivity
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 3), g i ≤
      3886 * (1 / 4 - 1 / (2 * ((n : ℝ) + 2) ^ 2)) := by
    intro n
    induction n with
    | zero => simp [Finset.sum_range_succ, hg]; norm_num
    | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Finset.sum_range_succ]
      have hgn : g (n + 3) = 3886 / ((n : ℝ) + 3) ^ 3 := by
        simp only [hg, if_pos (by omega : 2 ≤ n + 3)]; push_cast; ring
      rw [hgn]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have key : 1 / ((n : ℝ) + 3) ^ 3 ≤ 1 / (2 * ((n : ℝ) + 2) ^ 2) -
          1 / (2 * ((n : ℝ) + 3) ^ 2) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]
      push_cast
      have : 3886 / ((n : ℝ) + 3) ^ 3 = 3886 * (1 / ((n : ℝ) + 3) ^ 3) := by ring
      rw [this, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      linarith
  have hall : ∀ n : ℕ, ∑ i ∈ Finset.range n, g i ≤ 3886 / 4 := by
    intro n
    calc ∑ i ∈ Finset.range n, g i ≤ ∑ i ∈ Finset.range (n + 3), g i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            fun i _ _ => hg0 i
      _ ≤ 3886 * (1 / 4 - 1 / (2 * ((n : ℝ) + 2) ^ 2)) := hpart n
      _ ≤ 3886 / 4 := by
          have : 0 ≤ 1 / (2 * ((n : ℝ) + 2) ^ 2) := by positivity
          linarith
  exact ⟨Real.tsum_le_of_sum_range_le hg0 hall, summable_of_sum_range_le hg0 hall⟩


/-! ## The obstacle family -/

/-- Obstacle index `(b, n, a)` with `b ≥ 2`, `n ≥ 1`. -/
abbrev Ix := {p : ℕ × ℕ × ℤ // 2 ≤ p.1 ∧ 1 ≤ p.2.1}

/-- Centre `a/bⁿ`. -/
noncomputable def ctr12 (p : Ix) : ℝ := (p.1.2.2 : ℝ) / (p.1.1 : ℝ) ^ p.1.2.1

/-- Radius `b^{−(n+12)}`. -/
noncomputable def rad12 (p : Ix) : ℝ := ((p.1.1 : ℝ) ^ (p.1.2.1 + 12))⁻¹

/-- Charging stage `k + 1` with `4096^k ≤ 8bⁿ < 4096^{k+1}`. -/
def st12 (p : Ix) : ℕ := Nat.log 4096 (8 * p.1.1 ^ p.1.2.1) + 1

theorem rad12_pos (p : Ix) : 0 < rad12 p := by
  have : (0 : ℝ) < p.1.1 := by have := p.2.1; positivity
  exact inv_pos.2 (pow_pos this _)

/-- The level weight (count bound times per-obstacle charge). -/
noncomputable def W12 (k b n : ℕ) : ℝ :=
  ((1 / 2 / (4096 : ℝ) ^ k + 2 * ((b : ℝ) ^ (n + 12))⁻¹) * (b : ℝ) ^ n + 1) *
    (2 * (((b : ℝ) ^ (n + 12))⁻¹ / (1 / 2 / (4096 : ℝ) ^ k / 4096)) + 2) *
    (((b : ℝ) ^ (n + 12))⁻¹ / (1 / 2 / (4096 : ℝ) ^ k / 4096)) ^ (1/4 : ℝ)

/-- The level facts: a level charged at stage `k + 1` has `t = ℓ_k bⁿ ∈ [1/16, 256]` and
`n < 12k + 12`. -/
theorem level_facts {b n k : ℕ} (hb : 2 ≤ b) (hk : Nat.log 4096 (8 * b ^ n) = k) :
    (1 / 16 ≤ 1 / 2 / (4096 : ℝ) ^ k * (b : ℝ) ^ n ∧
      1 / 2 / (4096 : ℝ) ^ k * (b : ℝ) ^ n ≤ 256) ∧ n < 12 * k + 12 := by
  have hpos : 8 * b ^ n ≠ 0 := by positivity
  have h1 := Nat.pow_log_le_self 4096 hpos
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4096) (8 * b ^ n)
  rw [hk] at h1 h2
  have h1' : (4096 : ℝ) ^ k ≤ 8 * (b : ℝ) ^ n := by exact_mod_cast h1
  have h2' : 8 * (b : ℝ) ^ n < (4096 : ℝ) ^ (k + 1) := by exact_mod_cast h2
  have hK : (0 : ℝ) < 4096 ^ k := by positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_mul_eq_mul_div, le_div_iff₀ hK]; linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hK]; rw [pow_succ] at h2'; linarith
  · have h3 : 2 ^ n ≤ b ^ n := Nat.pow_le_pow_left hb n
    have h4 : 2 ^ n < 2 ^ (12 * k + 12) := by
      have : (4096 : ℕ) ^ (k + 1) = 2 ^ (12 * k + 12) := by
        rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, ← pow_mul]; ring_nf
      omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4

theorem W12_nonneg (k b n : ℕ) : 0 ≤ W12 k b n := by
  unfold W12; positivity

/-- Per base: the levels charged at stage `k + 1` weigh at most `3886/b³` in total. -/
theorem tsum_W12_le (k b : ℕ) (hb : 2 ≤ b) :
    ∑' n : ℕ, (if 1 ≤ n ∧ Nat.log 4096 (8 * b ^ n) = k then ENNReal.ofReal (W12 k b n) else 0)
      ≤ ENNReal.ofReal (3886 / (b : ℝ) ^ 3) := by
  classical
  set N := (Finset.range (12 * k + 12)).filter (fun n => 1 ≤ n ∧ Nat.log 4096 (8 * b ^ n) = k)
  rw [tsum_eq_sum (s := N) (fun n hn => by
    rw [if_neg]; intro h; exact hn (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (level_facts hb h.2).2, h⟩))]
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_filter.1 hn).2),
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ => W12_nonneg k b n)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  exact level_sum_le hb' (by positivity) N fun n hn =>
    (level_facts hb (Finset.mem_filter.1 hn).2.2).1


open NormalNumbers.UniformBad (obstacle window) in
/-- **The averaged new charge at `c = 12`** is at most `1050`. -/
theorem newCost12_le (k : ℕ) (x : ℝ) :
    ∑' i, (potSetP ctr12 rad12 st12 (1 / 2) 4096 (· = k + 1) k x).indicator
      (fun i => ENNReal.ofReal ((2 * (rad12 i / (1 / 2 / ((4096 : ℕ) : ℝ) ^ (k + 1))) + 2) *
        (rad12 i / (1 / 2 / ((4096 : ℕ) : ℝ) ^ (k + 1))) ^ (1/4 : ℝ))) i ≤
      ENNReal.ofReal 1050 := by
  classical
  set T := potSetP ctr12 rad12 st12 (1 / 2) 4096 (· = k + 1) k x with hT
  set ℓ : ℝ := 1 / 2 / (4096 : ℝ) ^ k with hℓ
  have hℓ' : (1 / 2 / ((4096 : ℕ) : ℝ) ^ (k + 1)) = ℓ / 4096 := by
    rw [hℓ]; push_cast; rw [pow_succ]; ring
  set A : ℕ × ℕ → ℝ := fun p => (2 * (((p.1 : ℝ) ^ (p.2 + 12))⁻¹ / (ℓ / 4096)) + 2) *
      (((p.1 : ℝ) ^ (p.2 + 12))⁻¹ / (ℓ / 4096)) ^ (1/4 : ℝ) with hA
  set f : Ix → ℝ≥0∞ := fun i => ENNReal.ofReal ((2 * (rad12 i / (1 / 2 / ((4096 : ℕ) : ℝ) ^
    (k + 1))) + 2) * (rad12 i / (1 / 2 / ((4096 : ℕ) : ℝ) ^ (k + 1))) ^ (1/4 : ℝ)) with hf
  set π : T → ℕ × ℕ := fun t => (t.1.1.1, t.1.1.2.1) with hπ
  set φ : ℕ × ℕ → ℝ≥0∞ := fun p =>
    if 2 ≤ p.1 ∧ 1 ≤ p.2 ∧ Nat.log 4096 (8 * p.1 ^ p.2) = k then
      ENNReal.ofReal (W12 k p.1 p.2) else 0 with hφ
  have hfib : ∀ p : ℕ × ℕ, ∑' t : π ⁻¹' {p}, f t.1 ≤ φ p := by
    rintro ⟨b, n⟩
    by_cases hc : 2 ≤ b ∧ 1 ≤ n ∧ Nat.log 4096 (8 * b ^ n) = k
    · have hconst : ∀ t : π ⁻¹' {(b, n)}, f t.1 = ENNReal.ofReal (A (b, n)) := by
        rintro ⟨⟨⟨⟨b', n', a⟩, hbn⟩, ht⟩, hp⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        simp only [hf, hA, rad12, hℓ']
      rw [tsum_congr hconst, ENNReal.tsum_set_const]
      have hbpos : (0 : ℝ) < (b : ℝ) ^ n := by have := hc.1; positivity
      obtain ⟨F, hFsub, hFcard⟩ := card_int_meet_le (B := (b : ℝ) ^ n)
        (r := ((b : ℝ) ^ (n + 12))⁻¹) (x := x) (ℓ := ℓ) hbpos (by positivity) (by positivity)
      have hinj : Set.InjOn (fun t : T => t.1.1.2.2) (π ⁻¹' {(b, n)}) := by
        rintro ⟨⟨⟨b1, n1, a1⟩, h1⟩, _⟩ hb1 ⟨⟨⟨b2, n2, a2⟩, h2⟩, _⟩ hb2 he
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, Prod.mk.injEq] at hb1 hb2
        obtain ⟨rfl, rfl⟩ := hb1; obtain ⟨rfl, rfl⟩ := hb2
        simp only at he; subst he; rfl
      have himg : (fun t : T => t.1.1.2.2) '' (π ⁻¹' {(b, n)}) ⊆ (F : Set ℤ) := by
        rintro _ ⟨⟨⟨⟨b1, n1, a1⟩, h1⟩, ht⟩, hb1, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, Prod.mk.injEq] at hb1
        obtain ⟨rfl, rfl⟩ := hb1
        apply hFsub
        obtain ⟨-, y, hy, hyw⟩ := ht
        exact ⟨y, hy, by simpa [window, hℓ] using hyw⟩
      have henc : (π ⁻¹' {(b, n)}).encard ≤ F.card := by
        rw [← hinj.encard_image, ← Set.encard_coe_eq_coe_finsetCard]
        exact Set.encard_le_encard himg
      calc ((π ⁻¹' {(b, n)}).encard : ℝ≥0∞) * ENNReal.ofReal (A (b, n))
          ≤ ENNReal.ofReal ((ℓ + 2 * ((b : ℝ) ^ (n + 12))⁻¹) * (b : ℝ) ^ n + 1) *
              ENNReal.ofReal (A (b, n)) := by
            gcongr
            calc ((π ⁻¹' {(b, n)}).encard : ℝ≥0∞) ≤ ((F.card : ℕ∞) : ℝ≥0∞) := by
                  exact_mod_cast henc
              _ = ENNReal.ofReal (F.card : ℝ) := by simp
              _ ≤ _ := ENNReal.ofReal_le_ofReal hFcard
        _ = φ (b, n) := by
            simp only [hφ, if_pos hc]
            rw [← ENNReal.ofReal_mul (by positivity)]
            simp only [W12, hA, hℓ]; ring_nf
    · have hempty : π ⁻¹' {(b, n)} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 ?_
        rintro ⟨⟨⟨b1, n1, a1⟩, h1⟩, ht⟩ hb1
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, Prod.mk.injEq] at hb1
        obtain ⟨rfl, rfl⟩ := hb1
        apply hc
        refine ⟨h1.1, h1.2, ?_⟩
        have := ht.1; simp only [st12] at this; omega
      rw [hempty]; simp
  calc ∑' i, T.indicator f i = ∑' t : T, f t := (tsum_subtype T f).symm
    _ = ∑' p, ∑' t : π ⁻¹' {p}, f t.1 := (ENNReal.tsum_fiberwise _ π).symm
    _ ≤ ∑' p, φ p := ENNReal.tsum_le_tsum hfib
    _ = ∑' b, ∑' n, φ (b, n) := by exact ENNReal.tsum_prod (f := fun b n => φ (b, n))
    _ ≤ ∑' b : ℕ, ENNReal.ofReal (if 2 ≤ b then 3886 / (b : ℝ) ^ 3 else 0) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : 2 ≤ b
        · rw [if_pos hb]
          refine le_trans (le_of_eq ?_) (tsum_W12_le k b hb)
          refine tsum_congr fun n => ?_
          simp only [hφ, hb, true_and]
        · rw [if_neg hb, ENNReal.ofReal_zero]
          refine le_of_eq (ENNReal.tsum_eq_zero.2 fun n => ?_)
          simp only [hφ]; rw [if_neg (fun h => hb h.1)]
    _ = ENNReal.ofReal (∑' b : ℕ, if 2 ≤ b then 3886 / (b : ℝ) ^ 3 else 0) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun b => by split_ifs <;> positivity)
          tsum_base_cube_le.2).symm
    _ ≤ ENNReal.ofReal 1050 :=
        ENNReal.ofReal_le_ofReal (tsum_base_cube_le.1.trans (by norm_num))


open NormalNumbers.UniformBad (dnear) in
/-- **`12` is admissible**: some `ξ ∈ [1/4, 3/4]` has `‖bⁿξ‖ > b^{−12}` for all `b ≥ 2`, `n ≥ 0`. -/
theorem admissible_twelve : Admissible 12 := by
  have h8 : ((4096 : ℕ) : ℝ) ^ (1/4 : ℝ) = 8 := by
    rw [show ((4096 : ℕ) : ℝ) = 8 ^ (4 : ℕ) by norm_num,
      show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h3 : (1 / 81 : ℝ) ^ (1/4 : ℝ) = 1 / 3 := by
    rw [show (1 / 81 : ℝ) = (1 / 3) ^ (4 : ℕ) by norm_num,
      show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  obtain ⟨ξ, hξ, havoid, -⟩ := exists_avoid_powPot ctr12 rad12 st12 (K := 4096) (K' := 4096)
    (by norm_num) (x₀ := 1 / 4) (ℓ₀ := 1 / 2) (α := 1/4) (ρ := 1 / 81) (g := 1050)
    (by norm_num) (by norm_num) (by norm_num) rad12_pos (fun i => by simp [st12])
    (by norm_num) (by rw [h8, h3]; norm_num)
    (fun k x => (sum_children_powPot_le ctr12 rad12 st12 (by norm_num) (by norm_num)
      (fun i => (rad12_pos i).le) k x).trans (newCost12_le k x))
    (fun _ _ => True) trivial (fun k x _ => by simp)
  refine ⟨ξ, fun b hb n => ?_⟩
  have hbpos : (0 : ℝ) < b := by positivity
  have hrpow : (b : ℝ) ^ (-(12 : ℝ)) = ((b : ℝ) ^ 12)⁻¹ := by
    rw [Real.rpow_neg hbpos.le]; norm_cast
  rw [hrpow]
  have hsmall : ((b : ℝ) ^ 12)⁻¹ < 1 / 4 := by
    have : (2 : ℝ) ^ 12 ≤ (b : ℝ) ^ 12 :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) 12
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num at this ⊢; linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, one_mul, dnear]
    have : 1 / 4 ≤ |ξ - round ξ| := by
      rcases le_or_gt (round ξ) 0 with hz | hz
      · have : ((round ξ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hz
        rw [abs_of_nonneg (by linarith [hξ.1])]; linarith [hξ.1]
      · have : (1 : ℝ) ≤ ((round ξ : ℤ) : ℝ) := by exact_mod_cast hz
        rw [abs_of_nonpos (by linarith [hξ.2])]; linarith [hξ.2]
    linarith
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
  have h := havoid ⟨(b, n, round ((b : ℝ) ^ n * ξ)), hb, hn⟩
  simp only [NormalNumbers.UniformBad.obstacle, ctr12, rad12, Set.mem_Icc, not_and_or,
    not_le] at h
  rw [dnear]
  set m : ℝ := (round ((b : ℝ) ^ n * ξ) : ℝ)
  have e1 : (b : ℝ) ^ n * (m / (b : ℝ) ^ n) = m := by field_simp
  have e2 : (b : ℝ) ^ n * ((b : ℝ) ^ (n + 12))⁻¹ = ((b : ℝ) ^ 12)⁻¹ := by
    rw [pow_add]; field_simp
  have hinv : 0 < ((b : ℝ) ^ 12)⁻¹ := by positivity
  rcases h with h | h
  · have := mul_lt_mul_of_pos_left h hbn
    rw [mul_sub, e1, e2] at this
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have := mul_lt_mul_of_pos_left h hbn
    rw [mul_add, e1, e2] at this
    rw [abs_of_pos (by linarith)]
    linarith

/-- **`c⋆ ≤ 12`**, halving the repo's `24`. -/
theorem cStar_le_twelve : cStar ≤ 12 :=
  csInf_le bddBelow_admissible admissible_twelve

end NormalNumbers.UniformBadThreshold
