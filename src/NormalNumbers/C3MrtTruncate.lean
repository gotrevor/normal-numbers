/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtDyadicContent

/-!
# Truncating the depth product: how much the deep factors can matter

The crux `DepthDyadicBound` asks for cancellation in
`∑_{N<n≤2N, n≡r (M)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}`.  Its deep factors are *almost* trivial:
`e(h'/b^{i+1})` is within `O(b^{-i})` of `1`, which is lap 92's content.  The natural hope is
that this lets one truncate the product at some `i₀ ≪ K` and reduce the `K`-point problem to an
`i₀`-point one.

This file makes the truncation quantitative, and the quantitative form REFUTES the hope.

* `norm_ee_sub_one_le` — `‖e(y) − 1‖ ≤ 4π|y|` for every real `y`, unconditionally.
* `depth_prod_eq_ee` — the depth product is a single additive character:
  `∏_{i<K} e(h/b^{i+1})^{ω(n+i+1)} = e(∑_{i<K} ω(n+i+1)·h/b^{i+1})`.
* `depth_prod_truncate_norm_le` — truncating at `i₀ ≤ K` costs at most
  `4π|h| ∑_{i₀≤i<K} ω(n+i+1)/b^{i+1}` per `n`.
* `dyadic_truncate_le` — hence, summing over the window,
  `‖S_K‖ ≤ ‖S_{i₀}‖ + 8π|h|·N·log₂(2N+K+1)·b^{−(i₀+1)}`.

**Why this refutes the truncation route** (recorded, not formalised — the asymptotics are
recorded in `PENDING_WORK.md` lap 99).  At the diagonal the target saving is
`(2 log N)^{-κ c₀ b^{-θK}}`, and with `b^K ≍ Λ := log log N` that is `≍ exp(−κc₀Λ^{1−θ})`.  The
truncation error above is `≍ N·(log log N)·b^{−i₀}`, so it drops below the target only once
`i₀ ≳ Λ^{1−θ}/log b`.  But the diagonal has `K ≍ log_b Λ`.  Since `Λ^{1−θ} ≫ log Λ` for every
`θ < 1`, the required truncation depth **exceeds `K` itself**, by an exponential factor.  So the
deep factors cannot be discarded at any depth below `K`: the `K`-point problem does not reduce to
a shallower one, in either direction.  This is the structural reason the route needs genuine
uniformity in `K` (lap 87's finding, now with the quantitative mechanism attached), and it is why
lap 92's "the deep digits are almost pretentious" does NOT translate into "the deep digits are
negligible".
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- `‖e(y) − 1‖ ≤ 4π|y|`, for every real `y`.  (Sharp up to the constant; unconditional, the
large-`|y|` case being covered by `‖e(y) − 1‖ ≤ 2`.) -/
theorem norm_ee_sub_one_le (y : ℝ) : ‖ee ((y : ℝ) : ℂ) - 1‖ ≤ 4 * Real.pi * |y| := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hnorm : ‖(2 * Real.pi * Complex.I * ((y : ℝ) : ℂ))‖ = 2 * Real.pi * |y| := by
    have : ‖(2 * Real.pi * Complex.I * ((y : ℝ) : ℂ))‖
        = ‖(2 : ℂ)‖ * ‖((Real.pi : ℝ) : ℂ)‖ * ‖Complex.I‖ * ‖((y : ℝ) : ℂ)‖ := by
      rw [norm_mul, norm_mul, norm_mul]
    rw [this, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rcases le_or_gt (2 * Real.pi * |y|) 1 with hsmall | hbig
  · have h := Complex.norm_exp_sub_one_le (x := 2 * Real.pi * Complex.I * ((y : ℝ) : ℂ))
      (by rw [hnorm]; exact hsmall)
    rw [ee] at *
    calc ‖Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) : ℂ)) - 1‖
        ≤ 2 * ‖(2 * Real.pi * Complex.I * ((y : ℝ) : ℂ))‖ := h
      _ = 4 * Real.pi * |y| := by rw [hnorm]; ring
  · have h2 : ‖ee ((y : ℝ) : ℂ) - 1‖ ≤ 2 := by
      calc ‖ee ((y : ℝ) : ℂ) - 1‖ ≤ ‖ee ((y : ℝ) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_ee_real]; norm_num
    linarith

/-- **The depth product is one additive character.** -/
theorem depth_prod_eq_ee (b n : ℕ) (h : ℤ) (K : ℕ) :
    ∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1)
      = ee (((∑ i ∈ range K,
          (omegaNat (n + i + 1) : ℝ) * ((h : ℝ) / (b : ℝ) ^ (i + 1)) : ℝ) : ℂ)) := by
  induction K with
  | zero => simp [ee_zero]
  | succ K ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, depthRoot]
    rw [← ee_nat_mul, ← ee_add]
    push_cast
    ring_nf

/-- **The cost of truncating the depth product at depth `i₀`.** -/
theorem depth_prod_truncate_norm_le (b n : ℕ) (h : ℤ) {i₀ K : ℕ} (hi : i₀ ≤ K) :
    ‖(∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1))
        - ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1)‖
      ≤ 4 * Real.pi * |(h : ℝ)| *
          ∑ i ∈ Finset.Ico i₀ K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
  classical
  set f : ℕ → ℝ := fun i => (omegaNat (n + i + 1) : ℝ) * ((h : ℝ) / (b : ℝ) ^ (i + 1)) with hf
  have hsplit : ∑ i ∈ range K, f i = (∑ i ∈ range i₀, f i) + ∑ i ∈ Finset.Ico i₀ K, f i := by
    rw [← Finset.sum_range_add_sum_Ico f hi]
  rw [depth_prod_eq_ee, depth_prod_eq_ee]
  show ‖ee (((∑ i ∈ range K, f i : ℝ) : ℂ)) - ee (((∑ i ∈ range i₀, f i : ℝ) : ℂ))‖ ≤ _
  rw [hsplit]
  have hpush : (((∑ i ∈ range i₀, f i) + ∑ i ∈ Finset.Ico i₀ K, f i : ℝ) : ℂ)
      = (((∑ i ∈ range i₀, f i : ℝ) : ℂ)) + (((∑ i ∈ Finset.Ico i₀ K, f i : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hpush, ee_add]
  have hfac : ee (((∑ i ∈ range i₀, f i : ℝ) : ℂ)) * ee (((∑ i ∈ Finset.Ico i₀ K, f i : ℝ) : ℂ))
      - ee (((∑ i ∈ range i₀, f i : ℝ) : ℂ))
      = ee (((∑ i ∈ range i₀, f i : ℝ) : ℂ))
        * (ee (((∑ i ∈ Finset.Ico i₀ K, f i : ℝ) : ℂ)) - 1) := by ring
  rw [hfac, norm_mul, norm_ee_real, one_mul]
  refine le_trans (norm_ee_sub_one_le _) ?_
  -- |∑ f| ≤ |h| ∑ ω/b^{i+1}
  have habs : |∑ i ∈ Finset.Ico i₀ K, f i|
      ≤ |(h : ℝ)| * ∑ i ∈ Finset.Ico i₀ K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [hf]
    simp only
    rw [abs_mul, abs_div]
    have hb : |(b : ℝ) ^ (i + 1)| = (b : ℝ) ^ (i + 1) := abs_of_nonneg (by positivity)
    have hom : |(omegaNat (n + i + 1) : ℝ)| = (omegaNat (n + i + 1) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hb, hom]
    rw [mul_div_assoc']
    apply le_of_eq
    ring
  have hpi : (0 : ℝ) < 4 * Real.pi := by
    have := Real.pi_gt_three; linarith
  calc 4 * Real.pi * |∑ i ∈ Finset.Ico i₀ K, f i|
      ≤ 4 * Real.pi * (|(h : ℝ)| *
          ∑ i ∈ Finset.Ico i₀ K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
        exact mul_le_mul_of_nonneg_left habs hpi.le
    _ = 4 * Real.pi * |(h : ℝ)| *
          ∑ i ∈ Finset.Ico i₀ K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by ring

/-- Triangle inequality against a comparison family, termwise. -/
theorem norm_sum_le_norm_sum_add {ι : Type*} (s : Finset ι) (F G : ι → ℂ) :
    ‖∑ n ∈ s, F n‖ ≤ ‖∑ n ∈ s, G n‖ + ∑ n ∈ s, ‖F n - G n‖ := by
  have hid : (∑ n ∈ s, F n) = (∑ n ∈ s, G n) + ∑ n ∈ s, (F n - G n) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have h2 : ‖∑ n ∈ s, (F n - G n)‖ ≤ ∑ n ∈ s, ‖F n - G n‖ := norm_sum_le _ _
  calc ‖∑ n ∈ s, F n‖ = ‖(∑ n ∈ s, G n) + ∑ n ∈ s, (F n - G n)‖ := by rw [hid]
    _ ≤ ‖∑ n ∈ s, G n‖ + ‖∑ n ∈ s, (F n - G n)‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ s, G n‖ + ∑ n ∈ s, ‖F n - G n‖ := by linarith

/-- **The truncation cost over any index set, symbolically.** -/
theorem truncate_sum_le (b : ℕ) (h : ℤ) {i₀ K : ℕ} (hi : i₀ ≤ K) (S : Finset ℕ) :
    ‖∑ n ∈ S, ∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1)‖
      ≤ ‖∑ n ∈ S, ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1)‖
        + 4 * Real.pi * |(h : ℝ)| *
            ∑ n ∈ S, ∑ i ∈ Finset.Ico i₀ K,
              (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
  have hstep := norm_sum_le_norm_sum_add S
    (fun n => ∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1))
    (fun n => ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1))
  have hterm : ∑ n ∈ S, ‖(∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1))
        - ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1)‖
      ≤ 4 * Real.pi * |(h : ℝ)| *
          ∑ n ∈ S, ∑ i ∈ Finset.Ico i₀ K,
            (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => depth_prod_truncate_norm_le b n h hi
  linarith

/-- **The truncation cost, made explicit.**  For `b ≥ 2` the geometric tail collapses, so the
whole window costs at most `8π|h|·#S·log₂ W·b^{−(i₀+1)}` where `W` bounds the shifted arguments.
This is the estimate whose comparison with the target saving refutes the truncation route (see
the module docstring). -/
theorem truncate_sum_explicit_le {b : ℕ} (hb : 2 ≤ b) (h : ℤ) {i₀ K : ℕ} (hi : i₀ ≤ K)
    (S : Finset ℕ) {W : ℕ} (hW : ∀ n ∈ S, n + K ≤ W) :
    ‖∑ n ∈ S, ∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1)‖
      ≤ ‖∑ n ∈ S, ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1)‖
        + 8 * Real.pi * |(h : ℝ)| * (S.card : ℝ)
            * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hLm0 : (0 : ℝ) ≤ ((Nat.log 2 W : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb1 : (0 : ℝ) < (b : ℝ) ^ (i₀ + 1) := by positivity
  -- per-`n` geometric bound
  have hper : ∀ n ∈ S, ∑ i ∈ Finset.Ico i₀ K,
      (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
      ≤ 2 * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by
    intro n hn
    have hω : ∀ i ∈ Finset.Ico i₀ K,
        (omegaNat (n + i + 1) : ℝ) ≤ ((Nat.log 2 W : ℕ) : ℝ) := by
      intro i hi'
      have hiK : i < K := (Finset.mem_Ico.1 hi').2
      have hne : n + i + 1 ≠ 0 := by omega
      have h1 : omegaNat (n + i + 1) ≤ Nat.log 2 (n + i + 1) := omegaNat_le_log _ hne
      have h2 : Nat.log 2 (n + i + 1) ≤ Nat.log 2 W := by
        refine Nat.log_mono_right ?_
        have := hW n hn
        omega
      exact_mod_cast le_trans h1 h2
    have hstep : ∀ i ∈ Finset.Ico i₀ K,
        (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
          ≤ (((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1)) * (1 / 2 : ℝ) ^ (i - i₀) := by
      intro i hi'
      have hi0 : i₀ ≤ i := (Finset.mem_Ico.1 hi').1
      have hpow : (b : ℝ) ^ (i + 1) = (b : ℝ) ^ (i₀ + 1) * (b : ℝ) ^ (i - i₀) := by
        rw [← pow_add]; congr 1; omega
      have h2p : ((2 : ℝ)) ^ (i - i₀) ≤ (b : ℝ) ^ (i - i₀) :=
        pow_le_pow_left₀ (by norm_num) hbR _
      have h2d : (0 : ℝ) < (2 : ℝ) ^ (i - i₀) := by positivity
      have hωLm := hω i hi'
      have hRHS : ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) * (1 / 2 : ℝ) ^ (i - i₀)
          = ((Nat.log 2 W : ℕ) : ℝ) / ((b : ℝ) ^ (i₀ + 1) * (2 : ℝ) ^ (i - i₀)) := by
        rw [div_pow, one_pow]
        field_simp
      have hmul : (omegaNat (n + i + 1) : ℝ) * (2 : ℝ) ^ (i - i₀)
          ≤ ((Nat.log 2 W : ℕ) : ℝ) * (b : ℝ) ^ (i - i₀) :=
        mul_le_mul hωLm h2p h2d.le hLm0
      rw [hpow, hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hmul hb1.le]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hgeo : ∑ i ∈ Finset.Ico i₀ K, (1 / 2 : ℝ) ^ (i - i₀) ≤ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hre : ∀ j ∈ range (K - i₀), (1 / 2 : ℝ) ^ (i₀ + j - i₀) = (1 / 2 : ℝ) ^ j := by
        intro j _; congr 1; omega
      rw [Finset.sum_congr rfl hre]
      exact sum_geometric_two_le (K - i₀)
    have hLb : (0 : ℝ) ≤ ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hgeo hLb) (le_of_eq (by ring))
  have hsum : ∑ n ∈ S, ∑ i ∈ Finset.Ico i₀ K,
      (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
      ≤ (S.card : ℝ) * (2 * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1)) := by
    calc ∑ n ∈ S, ∑ i ∈ Finset.Ico i₀ K,
          (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
        ≤ ∑ _n ∈ S, (2 * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1)) :=
          Finset.sum_le_sum hper
      _ = (S.card : ℝ) * (2 * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpi : (0 : ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by
    have := Real.pi_pos; positivity
  have hmain := truncate_sum_le b h hi S
  have hscale : 4 * Real.pi * |(h : ℝ)| *
      ∑ n ∈ S, ∑ i ∈ Finset.Ico i₀ K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
      ≤ 8 * Real.pi * |(h : ℝ)| * (S.card : ℝ)
          * ((Nat.log 2 W : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hsum hpi
    refine le_trans h1 (le_of_eq ?_)
    field_simp
    ring
  linarith

open scoped Classical in
/-- The dyadic-window instance of `truncate_sum_explicit_le`. -/
theorem dyadic_truncate_explicit_le {b : ℕ} (hb : 2 ≤ b) (h : ℤ) {i₀ K : ℕ} (hi : i₀ ≤ K)
    (N M r : ℕ) :
    ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, depthRoot b h i ^ omegaNat (n + i + 1)‖
      ≤ ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
          ∏ i ∈ range i₀, depthRoot b h i ^ omegaNat (n + i + 1)‖
        + 8 * Real.pi * |(h : ℝ)| * (N : ℝ)
            * ((Nat.log 2 (2 * N + K) : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by
  classical
  set S : Finset ℕ := (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M) with hS
  have hW : ∀ n ∈ S, n + K ≤ 2 * N + K := by
    intro n hn
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).2
    omega
  have hcard : (S.card : ℝ) ≤ (N : ℝ) := by
    have hc : S.card ≤ N := by
      have := Finset.card_filter_le (Finset.Ioc N (2 * N)) (fun n => n % M = r % M)
      rw [hS]
      rw [Nat.card_Ioc, show 2 * N - N = N by omega] at this
      exact this
    exact_mod_cast hc
  have hmain := truncate_sum_explicit_le hb h hi S hW
  have hb1 : (0 : ℝ) < (b : ℝ) ^ (i₀ + 1) := by
    have : (0 : ℝ) < (b : ℝ) := by
      have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    positivity
  have hpi : (0 : ℝ) ≤ 8 * Real.pi * |(h : ℝ)| * ((Nat.log 2 (2 * N + K) : ℕ) : ℝ) := by
    have := Real.pi_pos; positivity
  have hmono : 8 * Real.pi * |(h : ℝ)| * (S.card : ℝ)
        * ((Nat.log 2 (2 * N + K) : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1)
      ≤ 8 * Real.pi * |(h : ℝ)| * (N : ℝ)
        * ((Nat.log 2 (2 * N + K) : ℕ) : ℝ) / (b : ℝ) ^ (i₀ + 1) := by
    rw [div_le_div_iff₀ hb1 hb1]
    nlinarith [mul_le_mul_of_nonneg_left hcard hpi, hb1.le]
  linarith

#print axioms NormalNumbers.CastingOut.norm_ee_sub_one_le
#print axioms NormalNumbers.CastingOut.depth_prod_eq_ee
#print axioms NormalNumbers.CastingOut.depth_prod_truncate_norm_le
#print axioms NormalNumbers.CastingOut.truncate_sum_le
#print axioms NormalNumbers.CastingOut.truncate_sum_explicit_le
#print axioms NormalNumbers.CastingOut.dyadic_truncate_explicit_le

end CastingOut

end NormalNumbers
