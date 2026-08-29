/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoExpSepProof

/-!
# Sharpening Tier-1: `β = 26` → `β = 9` (batch-2 target 3)

Lane-2 batch-2 target 3 (operator brief v2).  `lnTwoExpSep_holds` gave
`∃ N₀, LnTwoExpSep 26 N₀` from deliberately crude constants; this file
sharpens the rate to `β = 9`.  `lnTwoExpSep_holds`, its corollary, and the
vendored Legendre modules are LANDED — never edit or weaken them; this file
only copy-extends.

## The three sharpenings (vs `LegendreHeight.lean`'s crude constants)

1. **Coefficient height** (`sum_abs_legendreCoeff_le_six_pow`):
   `Σ_k C(ℓ,k)·C(ℓ+k,ℓ) ≤ 6^ℓ`, replacing the crude `(ℓ+1)·8^ℓ`.  Proof:
   `C(ℓ+k,ℓ) ≤ 2^{ℓ+k}`, so the sum is `≤ 2^ℓ·Σ C(ℓ,k)·2^k = 2^ℓ·3^ℓ`
   (binomial theorem).  The true value is the central Delannoy number
   `P_ℓ(3) ~ (3+2√2)^ℓ ≈ 5.83^ℓ`, so `6^ℓ` is within `(1.03)^ℓ` of sharp.
2. **Remainder upper bound** (`legendre_remainder_neg_one_upper_sharp`):
   the kernel `y(1−y)/(1+y)` on `[0,1]` has maximum `3−2√2 ≈ 0.17157`
   (at `y = √2−1`); the rational cap `429/2500 = 0.1716` satisfies the
   discriminant test (`2071² − 4·2500·429 = −959 < 0`), giving
   `∫ ≤ (429/2500)^ℓ` — replacing the crude `(1/5)^ℓ`.  This is the change
   that unlocks single digits: it relaxes the pairing ratio constraint from
   `ℓ/n > 1/log₂(5/4) ≈ 3.11` to `ℓ/n > 1/log₂(2500/1716) ≈ 1.842`.
3. **Remainder lower bound** (`legendre_remainder_neg_one_lower_sharp`):
   `y(1−y) ≥ (6/35)(1+y)` EXACTLY on `[2/5, 3/7]` (the quadratic
   `y² − (29/35)y + 6/35` has roots exactly `2/5, 3/7`), and
   `1/(1+y) ≥ 7/10` there, so `∫ ≥ (1/35)·(7/10)·(6/35)^ℓ = (1/50)(6/35)^ℓ`
   — base `6/35 ≈ 0.1714` vs the crude `1/12 ≈ 0.083`.

## The honest accounting for `β = 9` (ratio `c = ℓ/n = 15/8`, `ℓ := 15n/8+1`)

With `lcm(1..ℓ) ≤ 4^ℓ·e^{2√ℓ·log ℓ}` (Chebyshev, `lcmUpto_le`) and
sub-exponential factors suppressed:

* smallness: `2ⁿ·lcm·(429/2500)^ℓ → 0` needs `c·log₂(2500/1716) > 1`;
  `15/8·0.5429 = 1.018 > 1` ✓ (this is why `c` can drop below 2);
* nonzero case: `2H = 2·6^ℓ·lcm ≤ 2^{9n}` needs `c·log₂24 ≤ 9`;
  `15/8·4.585 = 8.60 ≤ 9` ✓;
* zero case: `2ⁿ·(1/50)·(6·lcm/35·6·lcm)^…` — the `6^ℓ` height cancels
  against the `(6/35)^ℓ` lower bound leaving `50·35^ℓ ≤ 2^{10n}`, i.e.
  `c·log₂35 − 1 ≤ 9`; `15/8·5.1293 − 1 = 8.62 ≤ 9` ✓.

The integer-arithmetic certificates (verified by `norm_num` in the proofs):
`2⁸·429¹⁵ < 625¹⁵` (smallness), `24¹⁵ < 2⁷²` (nonzero), `35¹⁵ < 2⁸⁰` (zero).

**`β = 8` is NOT reachable by this method**: it would need
`c ≤ min(8/log₂24, 9/log₂35) ≈ 1.75 < 1.842`, violating smallness — the
blocker is Chebyshev's `4^ℓ` for `lcm`; a PNT-strength `lcm ≤ e^{(1+ε)ℓ}`
would give `β ≈ 5`.  Hence the draft's `β = 8` moved to `9` (DRAFT clause;
still `< 26`).
-/

namespace NormalNumbers

open Filter Real Polynomial Finset intervalIntegral

namespace Legendre

/-! ### Sharpening 1: coefficient height `Σ|c_k| ≤ 6^ℓ` -/

/-- Sharp (no `(n+1)` factor) height for the shifted-Legendre coefficient sum:
`Σ_k C(n,k)·C(n+k,n) ≤ 6ⁿ`, via `C(n+k,n) ≤ 2^{n+k}` and the binomial
theorem `Σ C(n,k)·2^k = 3ⁿ`. -/
lemma sum_abs_legendreCoeff_le_six_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), |legendreCoeff n k| ≤ (6 : ℤ) ^ n := by
  have hN : ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose n ≤ 6 ^ n := by
    calc ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose n
        ≤ ∑ k ∈ Finset.range (n + 1), 2 ^ n * (2 ^ k * 1 ^ (n - k) * n.choose k) := by
          apply Finset.sum_le_sum
          intro k _
          have h := Nat.choose_le_two_pow (n + k) n
          calc n.choose k * (n + k).choose n
              ≤ n.choose k * 2 ^ (n + k) := Nat.mul_le_mul_left _ h
            _ = 2 ^ n * (2 ^ k * 1 ^ (n - k) * n.choose k) := by
                rw [pow_add, one_pow]; ring
      _ = 2 ^ n * ∑ k ∈ Finset.range (n + 1), 2 ^ k * 1 ^ (n - k) * n.choose k := by
          rw [Finset.mul_sum]
      _ = 2 ^ n * (2 + 1) ^ n := by rw [add_pow 2 1 n]; simp
      _ = 6 ^ n := by rw [show (2 + 1 : ℕ) = 3 from rfl, ← Nat.mul_pow]
  calc ∑ k ∈ Finset.range (n + 1), |legendreCoeff n k|
      = ∑ k ∈ Finset.range (n + 1), ((n.choose k * (n + k).choose n : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [legendreCoeff, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          one_mul, Int.abs_natCast, Int.abs_natCast]
        push_cast
        ring
    _ ≤ ((6 ^ n : ℕ) : ℤ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast hN
    _ = (6 : ℤ) ^ n := by push_cast; ring

/-- Height-tracked variant of `sum_int_linear`: a finite sum of terms
`p + q·L` with `|q| ≤ B k` is `P + Q·L` with `|Q| ≤ Σ B k`.  (Copy of the
private helper in `LegendreHeight.lean`; ADDITIVE-ONLY discipline.) -/
private lemma sum_int_linear_bound' {L : ℝ} (f : ℕ → ℝ) (B : ℕ → ℤ) :
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

/-- **Sharp height-tracked integer linear form at `a = −1`**: the cleared
Legendre–Möbius approximant is `P + Q·log 2` with `|Q| ≤ 6ⁿ·lcm(1..n)` —
per-`k` the log-coefficient is exactly `±c_k·lcm`, and the `Σ|c_k| ≤ 6ⁿ`
sum bound replaces `LegendreHeight.lean`'s per-term `8ⁿ` relaxation. -/
theorem legendre_log_two_form_height_sharp (n : ℕ) :
    ∃ P Q : ℤ, (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
        (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
      = (P : ℝ) + (Q : ℝ) * Real.log 2 ∧
      |Q| ≤ 6 ^ n * (Nat.lcmUpto n : ℤ) := by
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
      rw [hc, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp only [eval_mul, eval_intCast, eval_pow, eval_X]
      ring
    rw [intervalIntegral.integral_congr hintegrand,
      intervalIntegral.integral_finsetSum hInt]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul]
  -- per-moment integrality with the EXACT per-k log-coefficient |c k|·lcm
  have hden : ∀ y : ℝ, (1 : ℝ) - ((-1 : ℤ) : ℝ) * y = 1 + y := fun y => by
    push_cast; ring
  have hlog2 : Real.log (1 - ((-1 : ℤ) : ℝ)) = L := by
    rw [hLdef]; norm_num
  have per_k : ∀ k ∈ Finset.range (n + 1), ∃ p q : ℤ,
      (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
          ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y)))
        = (p : ℝ) + (q : ℝ) * L ∧
      |q| ≤ |c k| * (Nat.lcmUpto n : ℤ) := by
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
    · -- |q| = |c k| · w · lcmUpto k = |c k| · lcmUpto n, exactly
      have habs : |(-(c k * (w : ℤ) * (-1) ^ (n - k) * (Nat.lcmUpto k : ℤ)))|
          = |c k| * ((w : ℤ) * (Nat.lcmUpto k : ℤ)) := by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          mul_one, Int.abs_natCast, Int.abs_natCast]
        ring
      have hwl : (w : ℤ) * (Nat.lcmUpto k : ℤ) = (Nat.lcmUpto n : ℤ) := by
        rw [hw]; push_cast; ring
      rw [habs, hwl]
  rw [hΛ, Finset.mul_sum]
  obtain ⟨P, Q, hPQ, hQb⟩ := sum_int_linear_bound' (L := L)
    (fun k => (Nat.lcmUpto n : ℝ) * (-1 : ℝ) ^ (n + 1) *
      ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 + y))))
    (fun k => |c k| * (Nat.lcmUpto n : ℤ)) _ per_k
  refine ⟨P, Q, hPQ, hQb.trans ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_abs_legendreCoeff_le_six_pow n)
    (Int.natCast_nonneg _)

/-! ### Sharpening 2: remainder upper bound `(429/2500)^n` -/

/-- **Sharp upper bound on the `a = −1` remainder integral**: the kernel
`y(1−y)/(1+y)` on `[0,1]` is capped by `429/2500` (discriminant
`2071² − 4·2500·429 = −959 < 0`; the true max is `3−2√2 ≈ 0.171573`),
and `1/(1+y) ≤ 1`, so `∫₀¹ yⁿ(1−y)ⁿ/(1+y)ⁿ⁺¹ ≤ (429/2500)ⁿ`. -/
theorem legendre_remainder_neg_one_upper_sharp (n : ℕ) :
    (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1))
      ≤ (429 / 2500 : ℝ) ^ n := by
  set F : ℝ → ℝ := fun y => (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) with hF
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    have : (0 : ℝ) < 1 + y := by linarith [hy.1]
    positivity
  have hint : IntervalIntegrable F MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num)]
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 1, F y ≤ (429 / 2500 : ℝ) ^ n := by
    intro y hy
    obtain ⟨h0, h1⟩ := hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have hkey : y * (1 - y) ≤ (429 / 2500 : ℝ) * (1 + y) := by
      nlinarith [sq_nonneg (5000 * y - 2071)]
    have hpow : (y * (1 - y)) ^ n ≤ ((429 / 2500 : ℝ) * (1 + y)) ^ n :=
      pow_le_pow_left₀ (by nlinarith) hkey n
    rw [hF]
    dsimp only
    rw [div_le_iff₀ (by positivity)]
    calc y ^ n * (1 - y) ^ n = (y * (1 - y)) ^ n := by rw [mul_pow]
      _ ≤ ((429 / 2500 : ℝ) * (1 + y)) ^ n := hpow
      _ = (429 / 2500 : ℝ) ^ n * (1 + y) ^ n := by rw [mul_pow]
      _ ≤ (429 / 2500 : ℝ) ^ n * (1 + y) ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (1 + y) ^ n = (1 + y) ^ n * 1 := by ring
            _ ≤ (1 + y) ^ n * (1 + y) := by
                apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = (1 + y) ^ (n + 1) := by rw [pow_succ]
  calc (∫ y in (0 : ℝ)..1, F y)
      ≤ ∫ _ in (0 : ℝ)..1, (429 / 2500 : ℝ) ^ n :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          intervalIntegrable_const hpt
    _ = (429 / 2500 : ℝ) ^ n := by simp

/-! ### Sharpening 3: remainder lower bound `(1/50)·(6/35)^n` -/

/-- **Sharp lower bound on the `a = −1` remainder integral**: on
`[2/5, 3/7]` the kernel satisfies `y(1−y) ≥ (6/35)(1+y)` EXACTLY (the
quadratic `y² − (29/35)y + 6/35` has roots `2/5` and `3/7`), and
`1/(1+y) ≥ 7/10`, so `∫ ≥ (1/35)·(7/10)·(6/35)ⁿ = (1/50)·(6/35)ⁿ`. -/
theorem legendre_remainder_neg_one_lower_sharp (n : ℕ) :
    (1 / 50 : ℝ) * (6 / 35) ^ n
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
  -- split ∫₀¹ = ∫₀^{2/5} + ∫_{2/5}^{3/7} + ∫_{3/7}^1
  have hsplit1 : (∫ y in (0 : ℝ)..(3 / 7), F y) + ∫ y in (3 / 7 : ℝ)..1, F y
      = ∫ y in (0 : ℝ)..1, F y :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (3 / 7) le_rfl (by norm_num) (by norm_num))
      (hint (3 / 7) 1 (by norm_num) le_rfl (by norm_num))
  have hsplit2 : (∫ y in (0 : ℝ)..(2 / 5), F y) + ∫ y in (2 / 5 : ℝ)..(3 / 7), F y
      = ∫ y in (0 : ℝ)..(3 / 7), F y :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (2 / 5) le_rfl (by norm_num) (by norm_num))
      (hint (2 / 5) (3 / 7) (by norm_num) (by norm_num) (by norm_num))
  have hnn : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a ≤ b →
      0 ≤ ∫ y in a..b, F y := by
    intro a b ha hb hab
    apply intervalIntegral.integral_nonneg hab
    intro y hy
    exact hnonneg y ⟨ha.trans hy.1, hy.2.trans hb⟩
  -- pointwise bound on [2/5, 3/7]
  have hpt : ∀ y ∈ Set.Icc (2 / 5 : ℝ) (3 / 7), (7 / 10 : ℝ) * (6 / 35) ^ n ≤ F y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have hkey : (6 / 35 : ℝ) * (1 + y) ≤ y * (1 - y) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 2 / 5)
        (by linarith : (0 : ℝ) ≤ 3 / 7 - y)]
    have hpow : ((6 / 35 : ℝ) * (1 + y)) ^ n ≤ (y * (1 - y)) ^ n :=
      pow_le_pow_left₀ (by positivity) hkey n
    have hnum : (6 / 35 : ℝ) ^ n * (1 + y) ^ n ≤ y ^ n * (1 - y) ^ n := by
      calc (6 / 35 : ℝ) ^ n * (1 + y) ^ n = ((6 / 35 : ℝ) * (1 + y)) ^ n := by
            rw [mul_pow]
        _ ≤ (y * (1 - y)) ^ n := hpow
        _ = y ^ n * (1 - y) ^ n := by rw [mul_pow]
    rw [hF]
    dsimp only
    rw [le_div_iff₀ (by positivity)]
    calc (7 / 10 : ℝ) * (6 / 35) ^ n * (1 + y) ^ (n + 1)
        = (6 / 35 : ℝ) ^ n * (1 + y) ^ n * ((7 / 10) * (1 + y)) := by ring
      _ ≤ (y ^ n * (1 - y) ^ n) * 1 := by
          apply mul_le_mul hnum (by nlinarith) (by nlinarith)
            (mul_nonneg (pow_nonneg (by linarith) n) (pow_nonneg (by linarith) n))
      _ = y ^ n * (1 - y) ^ n := by ring
  -- integrate the pointwise bound over [2/5, 3/7] (length 1/35)
  have hmid : (1 / 35 : ℝ) * ((7 / 10) * (6 / 35) ^ n)
      ≤ ∫ y in (2 / 5 : ℝ)..(3 / 7), F y := by
    have hconst : (∫ _ in (2 / 5 : ℝ)..(3 / 7), (7 / 10 : ℝ) * (6 / 35) ^ n)
        = (1 / 35 : ℝ) * ((7 / 10) * (6 / 35) ^ n) := by
      simp
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by norm_num)
      intervalIntegrable_const
      (hint (2 / 5) (3 / 7) (by norm_num) (by norm_num) (by norm_num))
    intro y hy
    exact hpt y hy
  calc (1 / 50 : ℝ) * (6 / 35) ^ n
      = (1 / 35 : ℝ) * ((7 / 10) * (6 / 35) ^ n) := by ring
    _ ≤ ∫ y in (2 / 5 : ℝ)..(3 / 7), F y := hmid
    _ ≤ (∫ y in (0 : ℝ)..(2 / 5), F y) + ∫ y in (2 / 5 : ℝ)..(3 / 7), F y := by
        linarith [hnn 0 (2 / 5) le_rfl (by norm_num) (by norm_num)]
    _ = ∫ y in (0 : ℝ)..(3 / 7), F y := hsplit2
    _ ≤ (∫ y in (0 : ℝ)..(3 / 7), F y) + ∫ y in (3 / 7 : ℝ)..1, F y := by
        linarith [hnn (3 / 7) 1 (by norm_num) le_rfl (by norm_num)]
    _ = ∫ y in (0 : ℝ)..1, F y := hsplit1

/-! ### The sharp package -/

/-- **The sharp Legendre data for the sharpened pairing argument.**
For every `n` there are integers `P, Q` with
* `|P + Q·log 2| ≤ lcm(1..n)·(429/2500)ⁿ` (small — sharp kernel cap),
* `lcm(1..n)·(1/50)·(6/35)ⁿ ≤ |P + Q·log 2|` (not too small), and
* `|Q| ≤ 6ⁿ·lcm(1..n)` (sharp height, no `(n+1)` factor).

Sharp counterpart of `legendre_log_two_package`. -/
theorem legendre_log_two_package_sharp (n : ℕ) :
    ∃ P Q : ℤ,
      |(P : ℝ) + (Q : ℝ) * Real.log 2| ≤ (Nat.lcmUpto n : ℝ) * (429 / 2500) ^ n ∧
      (Nat.lcmUpto n : ℝ) * ((1 / 50) * (6 / 35) ^ n)
        ≤ |(P : ℝ) + (Q : ℝ) * Real.log 2| ∧
      |Q| ≤ 6 ^ n * (Nat.lcmUpto n : ℤ) := by
  obtain ⟨P, Q, heq, hQb⟩ := legendre_log_two_form_height_sharp n
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
  have hΛval : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 + y))
      = ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
    rw [hΛeq, hform, hReq]
    norm_num
  have hRlow := legendre_remainder_neg_one_lower_sharp n
  have hRnn : 0 ≤ ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) :=
    le_trans (by positivity) hRlow
  refine ⟨P, Q, ?_, ?_, hQb⟩ <;> rw [← heq]
  · -- upper: |lcm·(−1)ⁿ⁺¹·Λ| = lcm·R ≤ lcm·(429/2500)ⁿ
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ)), hΛval,
      abs_of_nonneg hRnn]
    exact mul_le_mul_of_nonneg_left (legendre_remainder_neg_one_upper_sharp n)
      (by positivity)
  · -- lower: |lcm·(−1)ⁿ⁺¹·Λ| = lcm·R ≥ lcm·(1/50)(6/35)ⁿ
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ)), hΛval,
      abs_of_nonneg hRnn]
    exact mul_le_mul_of_nonneg_left hRlow (by positivity)

end Legendre

open Legendre

/-! ### Asymptotics: master limit and the three eventual inequalities -/

/-- `exp x ^ 8 = exp (8x)` (numeral-friendly form of `exp_nat_mul`). -/
private lemma exp_pow_eight (x : ℝ) : Real.exp x ^ 8 = Real.exp (8 * x) := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- Chebyshev bound with the sub-exponential factor re-indexed to `2n`:
for `1 ≤ l ≤ 2n`, `lcm(1..l) ≤ 4^l·e^{2√(2n)·log(2n)}` (monotonicity of
`x ↦ √x·log x` on `[1, ∞)`). -/
private lemma lcm_le_subexp {n l : ℕ} (hl1 : 1 ≤ l) (hl2n : l ≤ 2 * n) :
    (Nat.lcmUpto l : ℝ) ≤ 4 ^ l *
      Real.exp (2 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)) := by
  have h := Legendre.lcmUpto_le l hl1
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hlle : (l : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hl2n
  have hlognn : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg hl1R
  have hexp : Real.exp (2 * Real.sqrt (l : ℝ) * Real.log (l : ℝ))
      ≤ Real.exp (2 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul _ (Real.log_le_log (by linarith) hlle) hlognn (by positivity)
    have := Real.sqrt_le_sqrt hlle
    linarith
  calc (Nat.lcmUpto l : ℝ)
      ≤ 4 ^ l * Real.exp (2 * Real.sqrt (l : ℝ) * Real.log (l : ℝ)) := h
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Master limit for the sharpened pairing (8th-power form): for `0 < r < 1`,
`rⁿ·e^{16√(2n)·log(2n)} → 0` — the geometric factor kills the 8th power of
the `lcmUpto` sub-exponential error. -/
private lemma tendsto_geom_subexp16 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
      (fun n : ℕ => r ^ n *
        Real.exp (16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  set ε : ℝ := -Real.log r / 64 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.log ((2 * n : ℕ) : ℝ) / Real.sqrt ((2 * n : ℕ) : ℝ) < ε :=
    (log_div_sqrt_tendsto_zero.comp h2).eventually (Iio_mem_nhds hεpos)
  have hg : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (Real.log r / 2)))
      atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards with n
    positivity
  · filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hm1 : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by linarith
    have hsqrtpos : (0 : ℝ) < Real.sqrt ((2 * n : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
    have hlog1 : Real.log ((2 * n : ℕ) : ℝ) < ε * Real.sqrt ((2 * n : ℕ) : ℝ) := by
      have := (div_lt_iff₀ hsqrtpos).mp hn
      linarith
    -- the sub-exponential exponent: 16·√(2n)·log(2n) ≤ 32εn
    have hs : 16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)
        ≤ 32 * ε * (n : ℝ) := by
      have h1 : 16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)
          ≤ 16 * Real.sqrt ((2 * n : ℕ) : ℝ) * (ε * Real.sqrt ((2 * n : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hlog1) (by positivity)
      have h2' : Real.sqrt ((2 * n : ℕ) : ℝ) * Real.sqrt ((2 * n : ℕ) : ℝ)
          = ((2 * n : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
      have h3 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
      nlinarith
    have hrpow : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr0]
    calc r ^ n *
          Real.exp (16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ))
        ≤ Real.exp ((n : ℝ) * Real.log r) * Real.exp (32 * ε * (n : ℝ)) := by
          rw [hrpow]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by positivity)
      _ = Real.exp ((n : ℝ) * Real.log r + 32 * ε * (n : ℝ)) := by
          rw [← Real.exp_add]
      _ = Real.exp ((n : ℝ) * (Real.log r / 2)) := by
          congr 1
          rw [hεdef]
          ring

/-- Eventual inequality (1), sharpened: the linear form is small against `2ⁿ`
at index `ℓ = 15n/8 + 1`.  Certificate: `2⁸·429¹⁵ < 625¹⁵`. -/
private lemma sharp_smallness : ∀ᶠ n : ℕ in atTop,
    (2 : ℝ) ^ n * ((Nat.lcmUpto (15 * n / 8 + 1) : ℝ) *
      (429 / 2500 : ℝ) ^ (15 * n / 8 + 1)) ≤ 1 / 2 := by
  have hr0 : (0 : ℝ) < 256 * (429 / 625) ^ 15 := by positivity
  have hr1 : (256 : ℝ) * (429 / 625) ^ 15 < 1 := by norm_num
  have hM := tendsto_geom_subexp16 hr0 hr1
  have hev := hM.eventually_lt_const
    (show (0 : ℝ) < (625 / 429) * (1 / 2) ^ 8 by norm_num)
  filter_upwards [hev, eventually_ge_atTop 8] with n hn hn8
  set l := 15 * n / 8 + 1 with hldef
  have hl1 : 1 ≤ l := by omega
  have hl2n : l ≤ 2 * n := by omega
  set E := Real.exp (2 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ))
    with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hES : E ^ 8
      = Real.exp (16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)) := by
    rw [hEdef, exp_pow_eight]
    congr 1
    ring
  have hlcm : (Nat.lcmUpto l : ℝ) ≤ 4 ^ l * E := lcm_le_subexp hl1 hl2n
  set X := (2 : ℝ) ^ n * ((Nat.lcmUpto l : ℝ) * (429 / 2500 : ℝ) ^ l) with hXdef
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have h8 : X ^ 8 ≤ (1 / 2 : ℝ) ^ 8 := by
    have hb : X ≤ (2 : ℝ) ^ n * ((429 / 625 : ℝ) ^ l * E) := by
      rw [hXdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (Nat.lcmUpto l : ℝ) * (429 / 2500 : ℝ) ^ l
          ≤ (4 ^ l * E) * (429 / 2500 : ℝ) ^ l :=
            mul_le_mul_of_nonneg_right hlcm (by positivity)
        _ = (429 / 625 : ℝ) ^ l * E := by
            rw [show (429 / 625 : ℝ) = 4 * (429 / 2500) by norm_num, mul_pow]
            ring
    calc X ^ 8 ≤ ((2 : ℝ) ^ n * ((429 / 625 : ℝ) ^ l * E)) ^ 8 :=
          pow_le_pow_left₀ hX0 hb 8
      _ = (2 : ℝ) ^ (n * 8) * ((429 / 625 : ℝ) ^ (l * 8) * E ^ 8) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (2 : ℝ) ^ (n * 8) * ((429 / 625 : ℝ) ^ (15 * n + 1) * E ^ 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (429 / 625 : ℝ) *
          ((256 * (429 / 625 : ℝ) ^ 15) ^ n * E ^ 8) := by
          rw [pow_mul', pow_add, pow_mul, pow_one, mul_pow,
            show ((2 : ℝ) ^ 8) = 256 by norm_num]
          ring
      _ ≤ (429 / 625 : ℝ) * ((625 / 429) * (1 / 2) ^ 8) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [hES]
          exact le_of_lt hn
      _ = (1 / 2 : ℝ) ^ 8 := by norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h8

/-- Eventual inequality (2), sharpened: twice the height `H = 6^ℓ·lcm(ℓ)` is
at most `2^{9n}` at `ℓ = 15n/8 + 1`.  Certificate: `24¹⁵ < 2⁷²`. -/
private lemma sharp_height_small : ∀ᶠ n : ℕ in atTop,
    2 * ((6 : ℝ) ^ (15 * n / 8 + 1) * (Nat.lcmUpto (15 * n / 8 + 1) : ℝ))
      ≤ (2 : ℝ) ^ (9 * n) := by
  have hr0 : (0 : ℝ) < (24 : ℝ) ^ 15 / 2 ^ 72 := by positivity
  have hr1 : (24 : ℝ) ^ 15 / 2 ^ 72 < 1 := by norm_num
  have hM := tendsto_geom_subexp16 hr0 hr1
  have hev := hM.eventually_lt_const
    (show (0 : ℝ) < 1 / (2 ^ 8 * 24 ^ 8) by norm_num)
  filter_upwards [hev, eventually_ge_atTop 8] with n hn hn8
  set l := 15 * n / 8 + 1 with hldef
  have hl1 : 1 ≤ l := by omega
  have hl2n : l ≤ 2 * n := by omega
  set E := Real.exp (2 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ))
    with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hES : E ^ 8
      = Real.exp (16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)) := by
    rw [hEdef, exp_pow_eight]
    congr 1
    ring
  have hlcm : (Nat.lcmUpto l : ℝ) ≤ 4 ^ l * E := lcm_le_subexp hl1 hl2n
  set X := 2 * ((6 : ℝ) ^ l * (Nat.lcmUpto l : ℝ)) with hXdef
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have h8 : X ^ 8 ≤ ((2 : ℝ) ^ (9 * n)) ^ 8 := by
    have hb : X ≤ 2 * ((24 : ℝ) ^ l * E) := by
      rw [hXdef]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc (6 : ℝ) ^ l * (Nat.lcmUpto l : ℝ)
          ≤ (6 : ℝ) ^ l * (4 ^ l * E) :=
            mul_le_mul_of_nonneg_left hlcm (by positivity)
        _ = (24 : ℝ) ^ l * E := by
            rw [show (24 : ℝ) = 6 * 4 by norm_num, mul_pow]
            ring
    calc X ^ 8 ≤ (2 * ((24 : ℝ) ^ l * E)) ^ 8 := pow_le_pow_left₀ hX0 hb 8
      _ = 2 ^ 8 * ((24 : ℝ) ^ (l * 8) * E ^ 8) := by
          rw [mul_pow, mul_pow, ← pow_mul]
      _ ≤ 2 ^ 8 * ((24 : ℝ) ^ (15 * n + 8) * E ^ 8) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (2 ^ 8 * 24 ^ 8) * (((24 : ℝ) ^ 15) ^ n * E ^ 8) := by
          rw [pow_add, pow_mul]
          ring
      _ = (2 ^ 8 * 24 ^ 8) *
          ((((24 : ℝ) ^ 15 / 2 ^ 72) ^ n * E ^ 8) * ((2 : ℝ) ^ 72) ^ n) := by
          have hsplit : ((24 : ℝ) ^ 15) ^ n
              = ((24 : ℝ) ^ 15 / 2 ^ 72) ^ n * ((2 : ℝ) ^ 72) ^ n := by
            rw [← mul_pow, div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) ^ 72) ≠ 0)]
          rw [hsplit]
          ring
      _ ≤ (2 ^ 8 * 24 ^ 8) * ((1 / (2 ^ 8 * 24 ^ 8)) * ((2 : ℝ) ^ 72) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hES]
          exact le_of_lt hn
      _ = ((2 : ℝ) ^ 72) ^ n := by
          field_simp
      _ = ((2 : ℝ) ^ (9 * n)) ^ 8 := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h8

/-- Eventual inequality (3), sharpened (zero case): `H·2^{−9n}` is at most
`2ⁿ` times the lower bound — the `6^ℓ` height cancels against the `(6/35)^ℓ`
remainder base, leaving `50·35^ℓ ≤ 2^{10n}`.  Certificate: `35¹⁵ < 2⁸⁰`. -/
private lemma sharp_zero_case : ∀ᶠ n : ℕ in atTop,
    (6 : ℝ) ^ (15 * n / 8 + 1) * (Nat.lcmUpto (15 * n / 8 + 1) : ℝ) *
        ((2 : ℝ) ^ (9 * n))⁻¹
      ≤ (2 : ℝ) ^ n * ((Nat.lcmUpto (15 * n / 8 + 1) : ℝ) *
        ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ (15 * n / 8 + 1))) := by
  have hr0 : (0 : ℝ) < (35 : ℝ) ^ 15 / 2 ^ 80 := by positivity
  have hr1 : (35 : ℝ) ^ 15 / 2 ^ 80 < 1 := by norm_num
  have hM := tendsto_geom_subexp16 hr0 hr1
  have hev := hM.eventually_lt_const
    (show (0 : ℝ) < 1 / (50 ^ 8 * 35 ^ 8) by norm_num)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  set l := 15 * n / 8 + 1 with hldef
  set S := Real.exp (16 * Real.sqrt ((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ))
    with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hSdef, show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have hm1 : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * n := by omega
      exact_mod_cast this
    have := Real.log_nonneg hm1
    positivity
  -- core: 50·35^ℓ ≤ 2^{10n}, via 8th powers
  have hcore8 : (50 * (35 : ℝ) ^ l) ^ 8 ≤ ((2 : ℝ) ^ (10 * n)) ^ 8 := by
    calc (50 * (35 : ℝ) ^ l) ^ 8 = 50 ^ 8 * (35 : ℝ) ^ (l * 8) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ 50 ^ 8 * (35 : ℝ) ^ (15 * n + 8) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (50 ^ 8 * 35 ^ 8) * (((35 : ℝ) ^ 15) ^ n) := by
          rw [pow_add, pow_mul]
          ring
      _ = (50 ^ 8 * 35 ^ 8) *
          ((((35 : ℝ) ^ 15 / 2 ^ 80) ^ n) * ((2 : ℝ) ^ 80) ^ n) := by
          have hsplit : ((35 : ℝ) ^ 15) ^ n
              = ((35 : ℝ) ^ 15 / 2 ^ 80) ^ n * ((2 : ℝ) ^ 80) ^ n := by
            rw [← mul_pow, div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) ^ 80) ≠ 0)]
          rw [hsplit]
      _ ≤ (50 ^ 8 * 35 ^ 8) *
          (((((35 : ℝ) ^ 15 / 2 ^ 80) ^ n) * S) * ((2 : ℝ) ^ 80) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [pow_pos hr0 n]
      _ ≤ (50 ^ 8 * 35 ^ 8) * ((1 / (50 ^ 8 * 35 ^ 8)) * ((2 : ℝ) ^ 80) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right (le_of_lt hn) (by positivity)
      _ = ((2 : ℝ) ^ 80) ^ n := by field_simp
      _ = ((2 : ℝ) ^ (10 * n)) ^ 8 := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring
  have hcore : 50 * (35 : ℝ) ^ l ≤ (2 : ℝ) ^ (10 * n) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hcore8
  -- fraction shape (no lcm): 6^ℓ·2^{−9n} ≤ 2ⁿ·(1/50)(6/35)^ℓ
  have hfrac : (6 : ℝ) ^ l * ((2 : ℝ) ^ (9 * n))⁻¹
      ≤ (2 : ℝ) ^ n * ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l) := by
    rw [← div_eq_mul_inv,
      show (1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l = 6 ^ l / (50 * (35 : ℝ) ^ l) by
        rw [div_pow]; ring,
      mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    calc (6 : ℝ) ^ l * (50 * (35 : ℝ) ^ l)
        = (50 * (35 : ℝ) ^ l) * 6 ^ l := by ring
      _ ≤ (2 : ℝ) ^ (10 * n) * 6 ^ l :=
          mul_le_mul_of_nonneg_right hcore (by positivity)
      _ = (2 : ℝ) ^ n * 6 ^ l * (2 : ℝ) ^ (9 * n) := by
          rw [show 10 * n = n + 9 * n by ring, pow_add]
          ring
  calc (6 : ℝ) ^ l * (Nat.lcmUpto l : ℝ) * ((2 : ℝ) ^ (9 * n))⁻¹
      = ((6 : ℝ) ^ l * ((2 : ℝ) ^ (9 * n))⁻¹) * (Nat.lcmUpto l : ℝ) := by ring
    _ ≤ ((2 : ℝ) ^ n * ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l)) * (Nat.lcmUpto l : ℝ) :=
        mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = (2 : ℝ) ^ n * ((Nat.lcmUpto l : ℝ) *
        ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l)) := by ring

/-- **Tier-1, sharpened**: exponential dyadic separation for `ln 2` at the
single-digit rate `β = 9`, via the sharp Legendre coefficient and remainder
estimates (`legendre_log_two_package_sharp`) and the rebalanced index
`ℓ = 15n/8 + 1`.  See the module docstring for the honest accounting; the
draft's `β = 8` moved to `9` per its DRAFT clause (`β = 8` is out of reach
while `lcm(1..ℓ)` is only known ≤ `4^ℓ`). -/
theorem lnTwoExpSep_sharp : ∃ N₀ : ℕ, LnTwoExpSep 9 N₀ := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((sharp_smallness.and (sharp_height_small.and sharp_zero_case)).and
      (eventually_ge_atTop 1))
  refine ⟨N₀, ?_⟩
  rw [LnTwoExpSep, lnTwoDyadicSep_iff_int]
  intro n hn p
  obtain ⟨⟨h1, h2, h3⟩, hn1⟩ := hN₀ n hn
  -- the sharp Legendre package at ℓ = 15n/8 + 1
  obtain ⟨P, Q, hup, hlow, hQ⟩ := Legendre.legendre_log_two_package_sharp (15 * n / 8 + 1)
  set l := 15 * n / 8 + 1 with hldef
  set L : ℝ := Real.log 2 with hLdef
  set d : ℝ := |L * 2 ^ n - (p : ℝ)| with hddef
  have hd0 : 0 ≤ d := abs_nonneg _
  set form : ℝ := (P : ℝ) + (Q : ℝ) * L with hformdef
  set H : ℝ := (6 : ℝ) ^ l * (Nat.lcmUpto l : ℝ) with hHdef
  have hH0 : 0 < H := by
    rw [hHdef]
    have : (0 : ℝ) < (Nat.lcmUpto l : ℝ) := by
      exact_mod_cast Nat.lcmUpto_pos l
    positivity
  have hQle : |(Q : ℝ)| ≤ H := by
    rw [hHdef]
    exact_mod_cast hQ
  -- the pairing integer
  set N : ℤ := P * 2 ^ n + Q * p with hNdef
  have hNid : (N : ℝ) = 2 ^ n * form - (Q : ℝ) * (L * 2 ^ n - (p : ℝ)) := by
    rw [hNdef, hformdef]
    push_cast
    ring
  -- goal in inverse-power form
  have hgoal_eq : (2 : ℝ) ^ (-((9 : ℝ) * (n : ℝ))) = ((2 : ℝ) ^ (9 * n))⁻¹ := by
    rw [show -((9 : ℝ) * (n : ℝ)) = -(((9 * n : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [show (2 : ℝ) ^ (-(9 * (n : ℝ))) = (2 : ℝ) ^ (-((9 : ℝ) * (n : ℝ))) by norm_num,
    hgoal_eq]
  by_cases hNz : N = 0
  · -- zero case: |Q|·d = 2ⁿ·|form| ≥ 2ⁿ·lcm·(1/50)(6/35)^ℓ; the lcm cancels
    -- against the height via sharp_zero_case.
    have hid : (Q : ℝ) * (L * 2 ^ n - (p : ℝ)) = 2 ^ n * form := by
      have := hNid
      rw [hNz] at this
      push_cast at this
      linarith
    have habs : |(Q : ℝ)| * d = 2 ^ n * |form| := by
      rw [hddef, ← abs_mul, hid, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
    have hlow2 : (2 : ℝ) ^ n *
        ((Nat.lcmUpto l : ℝ) * ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l))
        ≤ H * d := by
      calc (2 : ℝ) ^ n *
            ((Nat.lcmUpto l : ℝ) * ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l))
          ≤ 2 ^ n * |form| := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hlow
        _ = |(Q : ℝ)| * d := habs.symm
        _ ≤ H * d := mul_le_mul_of_nonneg_right hQle hd0
    have hchain : H * ((2 : ℝ) ^ (9 * n))⁻¹ ≤ H * d := by
      calc H * ((2 : ℝ) ^ (9 * n))⁻¹
          ≤ (2 : ℝ) ^ n *
            ((Nat.lcmUpto l : ℝ) * ((1 / 50 : ℝ) * (6 / 35 : ℝ) ^ l)) := h3
        _ ≤ H * d := hlow2
    exact le_of_mul_le_mul_left hchain hH0
  · -- nonzero case: 1 ≤ |N| ≤ 2ⁿ·|form| + |Q|·d ≤ 1/2 + H·d, so d ≥ 1/(2H).
    have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hNz
    have hNle : |(N : ℝ)| ≤ 2 ^ n * |form| + |(Q : ℝ)| * d := by
      rw [hNid]
      calc |2 ^ n * form - (Q : ℝ) * (L * 2 ^ n - (p : ℝ))|
          ≤ |2 ^ n * form| + |(Q : ℝ) * (L * 2 ^ n - (p : ℝ))| := abs_sub _ _
        _ = 2 ^ n * |form| + |(Q : ℝ)| * d := by
            rw [abs_mul, abs_mul, hddef,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
    have hsmall : 2 ^ n * |form| ≤ 1 / 2 := by
      calc (2 : ℝ) ^ n * |form|
          ≤ 2 ^ n * ((Nat.lcmUpto l : ℝ) * (429 / 2500 : ℝ) ^ l) := by
            apply mul_le_mul_of_nonneg_left hup (by positivity)
        _ ≤ 1 / 2 := h1
    have hHd : 1 / 2 ≤ H * d := by
      have : |(Q : ℝ)| * d ≤ H * d := mul_le_mul_of_nonneg_right hQle hd0
      linarith
    have h2H : 2 * H ≤ (2 : ℝ) ^ (9 * n) := by
      calc 2 * H = 2 * ((6 : ℝ) ^ l * (Nat.lcmUpto l : ℝ)) := by rw [hHdef]
        _ ≤ (2 : ℝ) ^ (9 * n) := h2
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) ≤ 2 * (H * d) := by linarith
      _ = d * (2 * H) := by ring
      _ ≤ d * (2 : ℝ) ^ (9 * n) := mul_le_mul_of_nonneg_left h2H hd0


/-- **The sharp unconditional run cap**: past a threshold, every run of
zeros or ones in the binary expansion of `ln 2` at position `n` has
length at most `9·n` — hypothesis-free.  Wiring: `lnTwoExpSep_sharp`
into `run_le_of_expSep`. -/
theorem lnTwoRun_le_unconditional_sharp :
    ∃ N₀ : ℕ, ∀ n k : ℕ, N₀ ≤ n →
      (OccursAt 2 (Real.log 2) (List.replicate k 0) n ∨
        OccursAt 2 (Real.log 2) (List.replicate k 1) n) →
      (k : ℝ) ≤ 9 * n := by
  obtain ⟨N₀, hsep⟩ := lnTwoExpSep_sharp
  exact ⟨N₀, fun n k hn hr => run_le_of_expSep hsep hn hr⟩

end NormalNumbers
