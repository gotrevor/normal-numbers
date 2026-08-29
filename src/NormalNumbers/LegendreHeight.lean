/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LegendreShifted
import NormalNumbers.LcmUptoGrowth

/-!
# Height and lower bounds for the Legendre linear forms in `log 2`

The vendored `LegendreShifted.lean` supplies, for each `n`, a nonzero integer
combination `P + Q·log 2` with `|P + Q·log 2| ≤ lcm(1..n)·(1/5)ⁿ`
(`legendre_log_two_small`) — but deliberately no bound on the coefficient `Q`
and no lower bound on the form.  Those are the two honest gaps of the
`LnTwoExpSep` discharge (lane-2 target 4), and this module closes them:

* **Height** (`legendre_log_two_package`, third conjunct): rerunning the
  denominator-clearing with the *explicit* coefficients
  `legendreCoeff n k = (−1)ᵏ·C(n,k)·C(n+k,n)` tracks
  `|Q| ≤ (n+1)·8ⁿ·lcm(1..n)`: each per-moment log-coefficient is
  `±legendreCoeff n k · lcm(1..n)` and `|legendreCoeff n k| ≤ 8ⁿ`
  (two applications of `Nat.choose_le_two_pow`).
* **Lower bound** (second conjunct): at `a = −1` the linear form *equals*
  `lcm(1..n)` times the positive remainder integral
  `∫₀¹ yⁿ(1−y)ⁿ/(1+y)ⁿ⁺¹`, which is `≥ (1/6)·(1/12)ⁿ` by restricting to
  `[1/4, 1/2]` where `y(1−y)/(1+y) ≥ 1/12` and `1/(1+y) ≥ 2/3`.

The consumer is `LnTwoExpSepProof.lean` (pairing argument).
-/

open Polynomial Finset intervalIntegral

namespace NormalNumbers.Legendre

/-- The explicit integer coefficients of the shifted Legendre polynomial:
`shiftedLegendre n = Σ legendreCoeff n k · Xᵏ`. -/
def legendreCoeff (n k : ℕ) : ℤ :=
  (-1) ^ k * (n.choose k) * ((n + k).choose n)

/-- `shiftedLegendre n` with its coefficients named (the explicit form of
`shiftedLegendre_eq_int_poly`). -/
lemma shiftedLegendre_eq_coeff_sum (n : ℕ) : shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), ((legendreCoeff n k : ℤ) : ℝ[X]) * X ^ k := by
  simp_rw [shiftedLegendre_eq_sum, legendreCoeff]
  congr! 1 with x
  push_cast
  simp only [map_pow, map_neg, map_one]

/-- Crude but explicit height: `|legendreCoeff n k| ≤ 8ⁿ` for `k ≤ n`. -/
lemma abs_legendreCoeff_le {n k : ℕ} (hk : k ≤ n) :
    |legendreCoeff n k| ≤ (8 : ℤ) ^ n := by
  have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have h2 : (n + k).choose n ≤ 2 ^ (n + k) := Nat.choose_le_two_pow (n + k) n
  have h2' : (n + k).choose n ≤ 2 ^ (2 * n) :=
    h2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have habs : |legendreCoeff n k| = ((n.choose k : ℤ)) * ((n + k).choose n : ℤ) := by
    rw [legendreCoeff, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Int.abs_natCast, Int.abs_natCast]
  rw [habs]
  have : (n.choose k : ℤ) * ((n + k).choose n : ℤ) ≤ (2 : ℤ) ^ n * (2 : ℤ) ^ (2 * n) := by
    have ha : (0 : ℤ) ≤ (n.choose k : ℤ) := Int.natCast_nonneg _
    have hb : (0 : ℤ) ≤ ((n + k).choose n : ℤ) := Int.natCast_nonneg _
    exact mul_le_mul (by exact_mod_cast h1) (by exact_mod_cast h2') hb (by positivity)
  calc (n.choose k : ℤ) * ((n + k).choose n : ℤ)
      ≤ (2 : ℤ) ^ n * (2 : ℤ) ^ (2 * n) := this
    _ = (8 : ℤ) ^ n := by
        rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul]
        norm_num

/-- Height-tracked variant of `sum_int_linear`: a finite sum of terms
`p + q·L` with `|q| ≤ B k` is `P + Q·L` with `|Q| ≤ Σ B k`. -/
private lemma sum_int_linear_bound {L : ℝ} (f : ℕ → ℝ) (B : ℕ → ℤ) :
    ∀ (s : Finset ℕ),
      (∀ k ∈ s, ∃ p q : ℤ, f k = (p : ℝ) + (q : ℝ) * L ∧ |q| ≤ B k) →
      ∃ P Q : ℤ, ∑ k ∈ s, f k = (P : ℝ) + (Q : ℝ) * L ∧ |Q| ≤ ∑ k ∈ s, B k := by
  intro s
  induction s using Finset.induction with
  | empty => intro _; exact ⟨0, 0, by simp, by simp⟩
  | @insert x s hx ih =>
      intro h
      obtain ⟨px, qx, hxeq, hxb⟩ := h x (Finset.mem_insert_self x s)
      obtain ⟨P, Q, hPQ, hQb⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      refine ⟨px + P, qx + Q, by rw [Finset.sum_insert hx, hxeq, hPQ]; push_cast; ring, ?_⟩
      rw [Finset.sum_insert hx]
      calc |qx + Q| ≤ |qx| + |Q| := abs_add_le _ _
        _ ≤ B x + ∑ k ∈ s, B k := add_le_add hxb hQb

/-- **Height-tracked integer linear form at `a = −1`.**  The cleared
Legendre–Möbius approximant is `P + Q·log 2` with the log-coefficient
bounded: `|Q| ≤ (n+1)·8ⁿ·lcm(1..n)`.  This is the coefficient-height
estimate the donor module deliberately omitted (honest gap 1). -/
theorem legendre_log_two_int_linear_form_height (n : ℕ) :
    ∃ P Q : ℤ, (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
        (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
      = (P : ℝ) + (Q : ℝ) * Real.log 2 ∧
      |Q| ≤ ((n : ℤ) + 1) * 8 ^ n * (Nat.lcmUpto n : ℤ) := by
  set L : ℝ := Real.log 2 with hLdef
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 + y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    linarith [hy.1]
  set c : ℕ → ℤ := legendreCoeff n with hcdef
  have hc := shiftedLegendre_eq_coeff_sum n
  -- expand the integral into a sum of moments
  have hInt : ∀ k ∈ Finset.range (n + 1),
      IntervalIntegrable (fun y => (c k : ℝ) * (y ^ k / (1 + y)))
        MeasureTheory.volume 0 1 := by
    intro k _
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun y hy => ne_of_gt (hpos y hy)
  have hΛ : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
      = ∑ k ∈ Finset.range (n + 1),
          (c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y)) := by
    have hintegrand : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        eval y (shiftedLegendre n) / (1 + y)
          = ∑ k ∈ Finset.range (n + 1), (c k : ℝ) * (y ^ k / (1 + y)) := by
      intro y _
      rw [hc, eval_finset_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp only [eval_mul, eval_intCast, eval_pow, eval_X]
      ring
    rw [intervalIntegral.integral_congr hintegrand,
      intervalIntegral.integral_finset_sum hInt]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul]
  -- per-moment integrality WITH the log-coefficient height
  have hden : ∀ y : ℝ, (1 : ℝ) - ((-1 : ℤ) : ℝ) * y = 1 + y := fun y => by
    push_cast; ring
  have hlog2 : Real.log (1 - ((-1 : ℤ) : ℝ)) = L := by
    rw [hLdef]; norm_num
  have per_k : ∀ k ∈ Finset.range (n + 1), ∃ p q : ℤ,
      (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
          ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y)))
        = (p : ℝ) + (q : ℝ) * L ∧
      |q| ≤ 8 ^ n * (Nat.lcmUpto n : ℤ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    obtain ⟨s, hs⟩ := mobius_moment_int_cleared (-1) (by norm_num) k
    simp only [hlog2] at hs
    have hsden : (∫ y in (0 : ℝ)..1, y ^ k / (1 - ((-1 : ℤ) : ℝ) * y))
        = ∫ y in (0 : ℝ)..1, y ^ k / (1 + y) := by
      apply intervalIntegral.integral_congr
      intro y _; dsimp only; rw [hden]
    rw [hsden] at hs
    obtain ⟨w, hw⟩ := lcmUpto_dvd_of_le hkn
    refine ⟨c k * (w : ℤ) * (-1) ^ (n - k) * s,
            -(c k * (w : ℤ) * (-1) ^ (n - k) * (Nat.lcmUpto k : ℤ)), ?_, ?_⟩
    · have hlcmR : (Nat.lcmUpto n : ℝ) = (Nat.lcmUpto k : ℝ) * (w : ℝ) := by
        rw [hw]; push_cast; ring
      have hpowR : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ (k + 1) := by
        rw [← pow_add]; congr 1; omega
      have hACast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
      calc (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
              ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y)))
          = ((c k : ℝ) * (w : ℝ) * (-1 : ℝ) ^ (n - k)) *
              ((Nat.lcmUpto k : ℝ) * (((-1 : ℤ) : ℝ)) ^ (k + 1) *
                (∫ y in (0 : ℝ)..1, y ^ k / (1 + y))) := by
            rw [hlcmR, hpowR, hACast]; ring
        _ = ((c k : ℝ) * (w : ℝ) * (-1 : ℝ) ^ (n - k)) *
              ((s : ℝ) - (Nat.lcmUpto k : ℝ) * L) := by rw [hs]
        _ = _ := by push_cast; ring
    · -- |q| = |c k| · w · lcmUpto k = |c k| · lcmUpto n ≤ 8ⁿ · lcmUpto n
      have habs : |(-(c k * (w : ℤ) * (-1) ^ (n - k) * (Nat.lcmUpto k : ℤ)))|
          = |c k| * ((w : ℤ) * (Nat.lcmUpto k : ℤ)) := by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          mul_one, Int.abs_natCast, Int.abs_natCast]
        ring
      have hwl : (w : ℤ) * (Nat.lcmUpto k : ℤ) = (Nat.lcmUpto n : ℤ) := by
        rw [hw]; push_cast; ring
      rw [habs, hwl]
      exact mul_le_mul_of_nonneg_right (abs_legendreCoeff_le hkn) (Int.natCast_nonneg _)
  rw [hΛ, Finset.mul_sum]
  obtain ⟨P, Q, hPQ, hQb⟩ := sum_int_linear_bound (L := L)
    (fun k => (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
      ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y))))
    (fun _ => 8 ^ n * (Nat.lcmUpto n : ℤ)) _ per_k
  refine ⟨P, Q, hPQ, hQb.trans_eq ?_⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Lower bound on the `a = −1` remainder integral** (honest gap 2's
zero-case input): `∫₀¹ yⁿ(1−y)ⁿ/(1+y)ⁿ⁺¹ ≥ (1/6)·(1/12)ⁿ`, by restricting
to `[1/4, 1/2]`, where `y(1−y) ≥ (1/12)(1+y)` and `1/(1+y) ≥ 2/3`. -/
theorem legendre_remainder_neg_one_lower (n : ℕ) :
    (1 / 6 : ℝ) * (1 / 12) ^ n
      ≤ ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
  set F : ℝ → ℝ := fun y => (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) with hF
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    have : (0 : ℝ) < 1 + y := by linarith [hy.1]
    positivity
  have hint : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a ≤ b →
      IntervalIntegrable F MeasureTheory.volume a b := by
    intro a b ha hb hab
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb
  have hnonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F y := by
    intro y hy
    obtain ⟨h0, h1⟩ := hy
    have : (0 : ℝ) < 1 + y := by linarith
    rw [hF]
    positivity
  -- split ∫₀¹ = ∫₀^{1/4} + ∫_{1/4}^{1/2} + ∫_{1/2}^1
  have hsplit1 : (∫ y in (0 : ℝ)..(1 / 2), F y) + ∫ y in (1 / 2 : ℝ)..1, F y
      = ∫ y in (0 : ℝ)..1, F y :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (1 / 2) le_rfl (by norm_num) (by norm_num))
      (hint (1 / 2) 1 (by norm_num) le_rfl (by norm_num))
  have hsplit2 : (∫ y in (0 : ℝ)..(1 / 4), F y) + ∫ y in (1 / 4 : ℝ)..(1 / 2), F y
      = ∫ y in (0 : ℝ)..(1 / 2), F y :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (1 / 4) le_rfl (by norm_num) (by norm_num))
      (hint (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num))
  have hnn : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a ≤ b →
      0 ≤ ∫ y in a..b, F y := by
    intro a b ha hb hab
    apply intervalIntegral.integral_nonneg hab
    intro y hy
    exact hnonneg y ⟨ha.trans hy.1, hy.2.trans hb⟩
  -- pointwise bound on [1/4, 1/2]
  have hpt : ∀ y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2), (2 / 3 : ℝ) * (1 / 12) ^ n ≤ F y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have hkey : (1 / 12 : ℝ) * (1 + y) ≤ y * (1 - y) := by nlinarith
    have hpow : ((1 / 12 : ℝ) * (1 + y)) ^ n ≤ (y * (1 - y)) ^ n := by
      apply pow_le_pow_left₀ (by positivity) hkey
    have hnum : (1 / 12 : ℝ) ^ n * (1 + y) ^ n ≤ y ^ n * (1 - y) ^ n := by
      calc (1 / 12 : ℝ) ^ n * (1 + y) ^ n = ((1 / 12 : ℝ) * (1 + y)) ^ n := by
            rw [mul_pow]
        _ ≤ (y * (1 - y)) ^ n := hpow
        _ = y ^ n * (1 - y) ^ n := by rw [mul_pow]
    rw [hF]
    dsimp only
    rw [le_div_iff₀ (by positivity)]
    calc (2 / 3 : ℝ) * (1 / 12) ^ n * (1 + y) ^ (n + 1)
        = (1 / 12 : ℝ) ^ n * (1 + y) ^ n * ((2 / 3) * (1 + y)) := by ring
      _ ≤ (y ^ n * (1 - y) ^ n) * 1 := by
          apply mul_le_mul hnum (by nlinarith) (by nlinarith)
            (mul_nonneg (pow_nonneg (by linarith) n) (pow_nonneg (by linarith) n))
      _ = y ^ n * (1 - y) ^ n := by ring
  -- integrate the pointwise bound over [1/4, 1/2]
  have hmid : (1 / 4 : ℝ) * ((2 / 3) * (1 / 12) ^ n)
      ≤ ∫ y in (1 / 4 : ℝ)..(1 / 2), F y := by
    have hconst : (∫ _ in (1 / 4 : ℝ)..(1 / 2), (2 / 3 : ℝ) * (1 / 12) ^ n)
        = (1 / 4 : ℝ) * ((2 / 3) * (1 / 12) ^ n) := by
      simp
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by norm_num)
      intervalIntegrable_const
      (hint (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num))
    intro y hy
    exact hpt y hy
  calc (1 / 6 : ℝ) * (1 / 12) ^ n
      = (1 / 4 : ℝ) * ((2 / 3) * (1 / 12) ^ n) := by ring
    _ ≤ ∫ y in (1 / 4 : ℝ)..(1 / 2), F y := hmid
    _ ≤ (∫ y in (0 : ℝ)..(1 / 4), F y) + ∫ y in (1 / 4 : ℝ)..(1 / 2), F y := by
        linarith [hnn 0 (1 / 4) le_rfl (by norm_num) (by norm_num)]
    _ = ∫ y in (0 : ℝ)..(1 / 2), F y := hsplit2
    _ ≤ (∫ y in (0 : ℝ)..(1 / 2), F y) + ∫ y in (1 / 2 : ℝ)..1, F y := by
        linarith [hnn (1 / 2) 1 (by norm_num) le_rfl (by norm_num)]
    _ = ∫ y in (0 : ℝ)..1, F y := hsplit1

/-- **The packaged Legendre data for the `LnTwoExpSep` pairing argument.**
For every `n` there are integers `P, Q` with
* `|P + Q·log 2| ≤ lcm(1..n)·(1/5)ⁿ` (small),
* `lcm(1..n)·(1/6)·(1/12)ⁿ ≤ |P + Q·log 2|` (not too small — in particular
  nonzero), and
* `|Q| ≤ (n+1)·8ⁿ·lcm(1..n)` (bounded height).

Closes both honest gaps of the lane-2 target-4 brief on top of the vendored
backbone. -/
theorem legendre_log_two_package (n : ℕ) :
    ∃ P Q : ℤ,
      |(P : ℝ) + (Q : ℝ) * Real.log 2| ≤ (Nat.lcmUpto n : ℝ) * (1 / 5) ^ n ∧
      (Nat.lcmUpto n : ℝ) * ((1 / 6) * (1 / 12) ^ n)
        ≤ |(P : ℝ) + (Q : ℝ) * Real.log 2| ∧
      |Q| ≤ ((n : ℤ) + 1) * 8 ^ n * (Nat.lcmUpto n : ℤ) := by
  obtain ⟨P, Q, heq, hQb⟩ := legendre_log_two_int_linear_form_height n
  refine ⟨P, Q, ?_, ?_, hQb⟩ <;> rw [← heq]
  · -- upper bound: |lcm·(−1)ⁿ⁺¹·Λ| = lcm·|Λ| ≤ lcm·(1/5)ⁿ, as in the donor
    have hΛeq : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
        = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y) := by
      apply intervalIntegral.integral_congr
      intro y _; dsimp only; ring_nf
    have hform : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y))
        = (-(-1 : ℝ)) ^ n *
          ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - (-1 : ℝ) * y) ^ (n + 1) := by
      have hcongr : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y))
          = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - (-1 : ℝ) * y)) := by
        apply intervalIntegral.integral_congr; intro y _; dsimp only; rw [mul_one_div]
      rw [hcongr, legendre_mobius_integral (-1) n (by norm_num)]
    have hReq : (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - (-1 : ℝ) * y) ^ (n + 1))
        = ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      apply intervalIntegral.integral_congr; intro y _; dsimp only; ring_nf
    have hRnn : 0 ≤ ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro y hy; obtain ⟨hy0, hy1⟩ := hy; positivity
    have hΛabs : |∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y)|
        ≤ (1 / 5 : ℝ) ^ n := by
      rw [hΛeq, hform, hReq, abs_mul]
      have hone : |(-(-1 : ℝ)) ^ n| = 1 := by norm_num
      rw [hone, one_mul, abs_of_nonneg hRnn]
      exact legendre_remainder_neg_one_bound n
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ))]
    exact mul_le_mul_of_nonneg_left hΛabs (by positivity)
  · -- lower bound: |lcm·(−1)ⁿ⁺¹·Λ| = lcm·R ≥ lcm·(1/6)(1/12)ⁿ  (at a = −1,
    -- Λ = (+1)ⁿ·R = R with R the positive remainder integral)
    have hΛeq : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
        = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y) := by
      apply intervalIntegral.integral_congr
      intro y _; dsimp only; ring_nf
    have hform : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y))
        = (-(-1 : ℝ)) ^ n *
          ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - (-1 : ℝ) * y) ^ (n + 1) := by
      have hcongr : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (-1 : ℝ) * y))
          = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - (-1 : ℝ) * y)) := by
        apply intervalIntegral.integral_congr; intro y _; dsimp only; rw [mul_one_div]
      rw [hcongr, legendre_mobius_integral (-1) n (by norm_num)]
    have hReq : (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - (-1 : ℝ) * y) ^ (n + 1))
        = ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      apply intervalIntegral.integral_congr; intro y _; dsimp only; ring_nf
    have hRlow := legendre_remainder_neg_one_lower n
    have hΛval : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
        = ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      rw [hΛeq, hform, hReq]
      norm_num
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ)), hΛval,
      abs_of_nonneg (le_trans (by positivity) hRlow)]
    exact mul_le_mul_of_nonneg_left hRlow (by positivity)

end NormalNumbers.Legendre
