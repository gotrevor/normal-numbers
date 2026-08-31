/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiSqBBP
import NormalNumbers.PiBBPProof

/-!
# Lane-2 discharge of the frozen node `PiSqBBP` (batch 3)

The one obligation of this file is `piSqBBP_proved : PiSqBBP` — Bailey's
compendium Formula 29, `HasSum piSqTerm (π²)` (probe green to 88 digits).

## Route chosen: degree-2 roots-of-unity filter (the `PiBBPProof` trick)

The `PiBBPProof.lean` file discharged `PiBBP` by writing the BBP summand as
the mod-8 regrouping of a single filtered series `∑ w n` with
`w n = (linear combo of pⁿ)/n`, `p ∈ {x, −x, z₁, z̄₁}`, `x = 1/√2`,
`z₁ = (1+i)/2`; each geometric-log piece summed via
`Complex.hasSum_taylorSeries_neg_log` (`∑ zⁿ/n = −log(1−z)`).

For π² the ONLY structural change is the extra `1/n`: the filtered series is
`w2 n = (−16·xⁿ + 16·z₁ⁿ − 16·(−x)ⁿ + 16·z̄₁ⁿ)/n²` — the SAME four points
(the DFT of the Formula-29 coefficient vector `[0,16,−16,−8,−16,−4,−4,2]`
weighted by `(√2)ʳ` is supported on exactly frequencies `s ∈ {0,1,4,7}`
with the real integer weights `−16, 16, −16, 16`; verified numerically in
`experiments/pi_sq_bbp.py`).  The fiber algebra
(`hasSum_fiber2 : ∑_{r<8} w2 (8j+r) = piSqTerm j`) is pure `linear_combination`
over `I²=−1`, `x²=½`, exactly as in `PiBBPProof`, and is proved here.

## The remaining crux: `hasSum_w2`

The one deep leaf is the analytic master identity
`hasSum_w2 : HasSum w2 (π² : ℂ)`, i.e.
`−16·Li₂(x) + 16·Li₂(z₁) − 16·Li₂(−x) + 16·Li₂(z̄₁) = π²`, where
`Li₂(z) = ∑ zⁿ/n²` is the dilogarithm.  Via the **series-provable**
duplication `Li₂(z)+Li₂(−z) = ½·Li₂(z²)` (a term reindexing, no special
functions — see `dilog_add_neg` below), `−16·Li₂(x)−16·Li₂(−x)`
collapses to `−8·Li₂(x²) = −8·Li₂(½)`, and pairing the conjugates
`z̄₁ = conj z₁` gives `16·(Li₂(z₁)+Li₂(z̄₁)) = 32·Re Li₂((1+i)/2)`.  The
identity is then the classical dilog special-value combination
`−8·Li₂(½) + 32·Re Li₂((1+i)/2) = π²` with
`Li₂(½) = π²/12 − ½log²2` and `Re Li₂((1+i)/2) = 5π²/96 − ⅛log²2`
(the `log²2` terms cancel: `−8·(−½) + 32·(−⅛) = 0`).

**Obstruction (recorded 2026-08-31):** mathlib has NO dilogarithm — `grep`
for `dilog`/`Li₂`/`polylog` over `Mathlib/` is empty.  Both special values
are individually theorems requiring the dilog reflection/inversion
functional equations, which need the dilog defined as
`Li₂(z) = −∫₀^z log(1−t)/t dt` plus its derivative theory — a genuine
project.  This lap DECOMPOSES the node: the summability foundation
(`dilogSummable`), the four-point series plumbing (`hasSum_w2_of_tsums`),
the duplication identity (`dilog_add_neg`), and the entire fiber algebra
are proved in-kernel; `hasSum_w2` is left as a single disclosed `sorry`
whose content is precisely the two special values above.  Next attack:
build `Li₂` and its reflection formula, or import the two special values
as cited nodes and discharge the `log²2` cancellation.
-/

namespace NormalNumbers

namespace PiSqBBPProof

open Complex Real PiBBPProof

/-- The degree-2 filtered series: `w2 n = (−16·xⁿ + 16·z₁ⁿ − 16·(−x)ⁿ +
16·z̄₁ⁿ)/n²`, whose mod-8 fiber sums are the Formula-29 terms. -/
noncomputable def w2 (n : ℕ) : ℂ :=
  ((-16) * (x : ℂ) ^ n + 16 * z1 ^ n + (-16) * (-(x : ℂ)) ^ n + 16 * z2 ^ n)
    / (n : ℂ) ^ 2

/-! ### Summability foundation (special-value-free, reusable) -/

/-- **The dilog series is summable on the open unit disk.**  Dominated by
the geometric series `‖z‖ⁿ` since `‖zⁿ/n²‖ ≤ ‖z‖ⁿ`. -/
theorem dilogSummable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n / (n : ℂ) ^ 2) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖z‖ ^ n)
    (summable_geometric_of_lt_one (norm_nonneg _) hz)
  intro n
  rcases n with _ | m
  · simp
  · rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      nlinarith
    nlinarith [pow_nonneg (norm_nonneg z) (m + 1), h1]

/-- The dilogarithm as the tsum of its defining series (value = `Li₂ z`
on the open unit disk; `0`-indexed term `z⁰/0² = 0`, so it starts at
`n = 1`). -/
noncomputable def Li2 (z : ℂ) : ℂ := ∑' n : ℕ, z ^ n / (n : ℂ) ^ 2

theorem hasSum_Li2 {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / (n : ℂ) ^ 2) (Li2 z) :=
  (dilogSummable hz).hasSum

/-- **Duplication identity for the dilogarithm** (special-value-free):
`Li₂ z + Li₂ (−z) = ½·Li₂ (z²)`.  Proved purely by the even/odd split of
the series `∑ (zⁿ + (−z)ⁿ)/n²` — odd terms cancel, even terms `n = 2k`
give `2·z^{2k}/(2k)² = ½·(z²)ᵏ/k²`.  This is the first step collapsing the
`hasSum_w2` crux: `−16·Li₂(x) − 16·Li₂(−x) = −8·Li₂(x²) = −8·Li₂(½)`. -/
theorem dilog_add_neg {z : ℂ} (hz : ‖z‖ < 1) :
    Li2 z + Li2 (-z) = (1 / 2) * Li2 (z ^ 2) := by
  have hzn : ‖(-z)‖ < 1 := by rwa [norm_neg]
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  set f : ℕ → ℂ := fun n => z ^ n / (n : ℂ) ^ 2 + (-z) ^ n / (n : ℂ) ^ 2 with hf
  have hsum1 : HasSum f (Li2 z + Li2 (-z)) := (hasSum_Li2 hz).add (hasSum_Li2 hzn)
  have hEven : HasSum (fun k : ℕ => f (2 * k)) ((1 / 2) * Li2 (z ^ 2)) := by
    have hbase := (hasSum_Li2 hz2).mul_left (1 / 2)
    have hfun : (fun k : ℕ => f (2 * k))
        = fun k : ℕ => (1 / 2) * ((z ^ 2) ^ k / (k : ℂ) ^ 2) := by
      funext k
      rcases k with _ | m
      · simp [hf]
      · have h2k : ((2 * (m + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hk : (((m : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp only [hf]
        rw [Even.neg_pow ⟨m + 1, two_mul (m + 1)⟩, ← pow_mul]
        push_cast
        field_simp
        ring
    rw [hfun]; exact hbase
  have hOdd : HasSum (fun k : ℕ => f (2 * k + 1)) 0 := by
    have : (fun k : ℕ => f (2 * k + 1)) = fun _ => 0 := by
      funext k
      simp only [hf]
      rw [Odd.neg_pow ⟨k, rfl⟩]
      ring
    rw [this]
    exact hasSum_zero
  have hsum2 : HasSum f ((1 / 2) * Li2 (z ^ 2) + 0) := hEven.even_add_odd hOdd
  rw [add_zero] at hsum2
  exact hsum1.unique hsum2

/-- **Term-wise derivative of the dilogarithm.**  On the open unit disk,
`Li₂` is differentiable and `Li₂' w = ∑' n, n·wⁿ⁻¹/n²` (the derivative of
the series, summed term by term).  Proved on the sub-ball `‖·‖ < r`,
`r = (‖w‖+1)/2 < 1`, where the derivative series has a summable geometric
bound.  (The closed form `−log(1−w)/w` follows for `w ≠ 0`; see
`tsum_Li2_deriv`.) -/
theorem hasDerivAt_Li2 {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt Li2 (∑' n : ℕ, ((n : ℂ) * w ^ (n - 1)) / (n : ℂ) ^ 2) w := by
  set r : ℝ := (‖w‖ + 1) / 2 with hr
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hwr : ‖w‖ < r := by rw [hr]; linarith
  set t : Set ℂ := Metric.ball 0 r with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htconn : IsPreconnected t := (Metric.isConnected_ball (by positivity)).isPreconnected
  have hwt : w ∈ t := by rw [ht, Metric.mem_ball, dist_zero_right]; exact hwr
  -- per-term derivative
  have hg : ∀ (n : ℕ) (y : ℂ), y ∈ t →
      HasDerivAt (fun z : ℂ => z ^ n / (n : ℂ) ^ 2)
        (((n : ℂ) * y ^ (n - 1)) / (n : ℂ) ^ 2) y := by
    intro n y _
    exact (hasDerivAt_pow n y).div_const _
  -- summable geometric bound on the derivatives over the ball
  have hu : Summable (fun n : ℕ => r ^ n * r⁻¹) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_right _
  have hg' : ∀ (n : ℕ) (y : ℂ), y ∈ t →
      ‖((n : ℂ) * y ^ (n - 1)) / (n : ℂ) ^ 2‖ ≤ r ^ n * r⁻¹ := by
    intro n y hy
    rw [ht, Metric.mem_ball, dist_zero_right] at hy
    rcases n with _ | m
    · simp; positivity
    · have hmn : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      simp only [Nat.add_sub_cancel, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
      push_cast
      rw [show ((m : ℝ) + 1) * ‖y‖ ^ m / ((m : ℝ) + 1) ^ 2
          = ‖y‖ ^ m / ((m : ℝ) + 1) by field_simp]
      calc ‖y‖ ^ m / ((m : ℝ) + 1) ≤ ‖y‖ ^ m := by
            rw [div_le_iff₀ hmn]; nlinarith [pow_nonneg (norm_nonneg y) m]
        _ ≤ r ^ m := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hy) m
        _ ≤ r ^ (m + 1) * r⁻¹ := by
            rw [pow_succ, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]
  -- convergence at the centre
  have hg0 : Summable (fun n : ℕ => (0 : ℂ) ^ n / (n : ℂ) ^ 2) := by
    have : (fun n : ℕ => (0 : ℂ) ^ n / (n : ℂ) ^ 2) = fun _ => 0 := by
      funext n; rcases n with _ | m <;> simp
    rw [this]; exact summable_zero
  have h0t : (0 : ℂ) ∈ t := by rw [ht, Metric.mem_ball, dist_zero_right]; simpa using hr0
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu htopen htconn hg hg' h0t hg0 hwt
  exact hderiv

/-- The derivative series of `Li₂` has the closed form `−log(1−w)/w`
(for `w ≠ 0`): term-by-term `n·wⁿ⁻¹/n² = (wⁿ/n)/w`, and
`∑ wⁿ/n = −log(1−w)` (`Complex.hasSum_taylorSeries_neg_log`). -/
theorem tsum_Li2_deriv {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    (∑' n : ℕ, ((n : ℂ) * w ^ (n - 1)) / (n : ℂ) ^ 2)
      = -Complex.log (1 - w) / w := by
  have hts : (fun n : ℕ => ((n : ℂ) * w ^ (n - 1)) / (n : ℂ) ^ 2)
      = fun n : ℕ => (w ^ n / (n : ℂ)) / w := by
    funext n
    rcases n with _ | m
    · simp
    · have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  rw [hts]
  exact ((Complex.hasSum_taylorSeries_neg_log hw).div_const w).tsum_eq

/-- **Clean derivative of the dilogarithm**: `Li₂' w = −log(1−w)/w` for
`0 < ‖w‖ < 1`. -/
theorem hasDerivAt_Li2' {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    HasDerivAt Li2 (-Complex.log (1 - w) / w) w := by
  rw [← tsum_Li2_deriv hw hw0]
  exact hasDerivAt_Li2 hw

/-! ### Fiber algebra: eight consecutive terms make one Formula-29 term -/

/-- Power-block decomposition of `w2` along `n = 8j + r`.  Every point
satisfies `p⁸ = 1/16`, so the `j`-power factors out uniformly. -/
lemma w2_block (j r : ℕ) :
    w2 (j * 8 + r) = ((16⁻¹ : ℂ) ^ j *
      ((-16) * (x : ℂ) ^ r + 16 * z1 ^ r + (-16) * (-(x : ℂ)) ^ r + 16 * z2 ^ r))
      / ((j * 8 + r : ℕ) : ℂ) ^ 2 := by
  rw [w2, pow_add, pow_add, pow_add, pow_add, pow_mul', pow_mul', pow_mul', pow_mul',
    z1_pow8, z2_pow8, cx_pow8, neg_cx_pow8]
  ring

/-- The residue numerators reproduce the Formula-29 coefficient vector
`[0,16,−16,−8,−16,−4,−4,2]`.  Each is a `linear_combination` over
`I² = −1` (`Complex.I_sq`) and `x² = ½` (`cx_sq`), cofactors derived by
polynomial division. -/
lemma num0 : (-16) * (x : ℂ) ^ 0 + 16 * z1 ^ 0 + (-16) * (-(x : ℂ)) ^ 0 + 16 * z2 ^ 0
    = (0 : ℂ) := by rw [z1, z2]; ring

lemma num1 : (-16) * (x : ℂ) ^ 1 + 16 * z1 ^ 1 + (-16) * (-(x : ℂ)) ^ 1 + 16 * z2 ^ 1
    = (16 : ℂ) := by rw [z1, z2]; ring

lemma num2 : (-16) * (x : ℂ) ^ 2 + 16 * z1 ^ 2 + (-16) * (-(x : ℂ)) ^ 2 + 16 * z2 ^ 2
    = (-16 : ℂ) := by
  rw [z1, z2]; linear_combination (8 : ℂ) * Complex.I_sq + (-32 : ℂ) * cx_sq

lemma num3 : (-16) * (x : ℂ) ^ 3 + 16 * z1 ^ 3 + (-16) * (-(x : ℂ)) ^ 3 + 16 * z2 ^ 3
    = (-8 : ℂ) := by
  rw [z1, z2]; linear_combination (12 : ℂ) * Complex.I_sq

lemma num4 : (-16) * (x : ℂ) ^ 4 + 16 * z1 ^ 4 + (-16) * (-(x : ℂ)) ^ 4 + 16 * z2 ^ 4
    = (-16 : ℂ) := by
  rw [z1, z2]
  linear_combination (10 + 2 * Complex.I ^ 2) * Complex.I_sq
    + (-16 - 32 * (x : ℂ) ^ 2) * cx_sq

lemma num5 : (-16) * (x : ℂ) ^ 5 + 16 * z1 ^ 5 + (-16) * (-(x : ℂ)) ^ 5 + 16 * z2 ^ 5
    = (-4 : ℂ) := by
  rw [z1, z2]
  linear_combination (5 + 5 * Complex.I ^ 2) * Complex.I_sq

lemma num6 : (-16) * (x : ℂ) ^ 6 + 16 * z1 ^ 6 + (-16) * (-(x : ℂ)) ^ 6 + 16 * z2 ^ 6
    = (-4 : ℂ) := by
  rw [z1, z2]
  linear_combination (1/2 + 7 * Complex.I ^ 2 + (1/2) * Complex.I ^ 4) * Complex.I_sq
    + (-8 - 16 * (x : ℂ) ^ 2 - 32 * (x : ℂ) ^ 4) * cx_sq

lemma num7 : (-16) * (x : ℂ) ^ 7 + 16 * z1 ^ 7 + (-16) * (-(x : ℂ)) ^ 7 + 16 * z2 ^ 7
    = (2 : ℂ) := by
  rw [z1, z2]
  linear_combination (-7/4 + 7 * Complex.I ^ 2 + (7/4) * Complex.I ^ 4) * Complex.I_sq

/-- **Fiber identity**: `∑_{r<8} w2 (8j + r) = piSqTerm j`. -/
lemma hasSum_fiber2 (j : ℕ) :
    HasSum (fun r : Fin 8 => w2 (j * 8 + (r : ℕ))) ((piSqTerm j : ℝ) : ℂ) := by
  have h := hasSum_fintype (fun r : Fin 8 => w2 (j * 8 + (r : ℕ)))
  have hsum : ∑ r : Fin 8, w2 (j * 8 + (r : ℕ)) = ((piSqTerm j : ℝ) : ℂ) := by
    rw [Fin.sum_univ_eight]
    simp only [show ((0 : Fin 8) : ℕ) = 0 from rfl, show ((1 : Fin 8) : ℕ) = 1 from rfl,
      show ((2 : Fin 8) : ℕ) = 2 from rfl, show ((3 : Fin 8) : ℕ) = 3 from rfl,
      show ((4 : Fin 8) : ℕ) = 4 from rfl, show ((5 : Fin 8) : ℕ) = 5 from rfl,
      show ((6 : Fin 8) : ℕ) = 6 from rfl, show ((7 : Fin 8) : ℕ) = 7 from rfl]
    rw [w2_block, w2_block, w2_block, w2_block, w2_block, w2_block, w2_block, w2_block,
      num0, num1, num2, num3, num4, num5, num6, num7, piSqTerm, piSqKick]
    push_cast
    simp only [one_div, inv_pow]
    ring
  rwa [hsum] at h

/-! ### The analytic crux (single disclosed leaf) -/

/-- **Dilog reflection formula (frozen crux).**  For `z` and `1−z` both
in the open unit disk,
`Li₂ z + Li₂ (1−z) = π²/6 − log z · log(1−z)`.

This is the ONE deep fact the π² BBP node now rests on.  Standard proof:
the local `Li2` satisfies `Li₂' w = −log(1−w)/w` (term-wise derivative of
the series), so `F z := Li₂ z + Li₂(1−z) + log z·log(1−z)` has `F' ≡ 0`
on the disk minus `{0,1}`, hence is constant `= π²/6` (limit `z→0`,
`Li₂ 0 = 0`, `Li₂ 1 = π²/6`).  Needs `HasDerivAt` of a `tsum`
(`Mathlib/Analysis/Calculus/SmoothSeries.lean`), connectedness, and the
`z→0` limit — a multi-lap build.  Disclosed 2026-08-31. -/
theorem dilog_reflection {z : ℂ} (hz : ‖z‖ < 1) (hz1 : ‖1 - z‖ < 1) :
    Li2 z + Li2 (1 - z)
      = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) - Complex.log z * Complex.log (1 - z) := by
  sorry

/-- The π² special-value combination, DERIVED from `dilog_reflection`
at `z = ½` (self-dual) and `z = z₁` (`1 − z₁ = z̄₁`), using the log
values `log z₁ = −½log2 + (π/4)i`, `log z₂ = −½log2 − (π/4)i` (from
`PiBBPProof`) and `log ½ = −log 2`.  All arithmetic machine-checked. -/
theorem dilog_special_values :
    (-8) * Li2 (2⁻¹ : ℂ) + 16 * (Li2 z1 + Li2 z2) = ((Real.pi ^ 2 : ℝ) : ℂ) := by
  have hhalf : ‖(2⁻¹ : ℂ)‖ < 1 := by rw [norm_inv]; norm_num
  have hh1 : (1 : ℂ) - 2⁻¹ = 2⁻¹ := by ring
  have r1 := dilog_reflection (z := (2⁻¹ : ℂ)) hhalf (by rw [hh1]; exact hhalf)
  rw [hh1] at r1
  have h1z1 : (1 : ℂ) - z1 = z2 := by rw [z1, z2]; ring
  have r2 := dilog_reflection (z := z1) norm_z1_lt (by rw [h1z1]; exact norm_z2_lt)
  rw [h1z1] at r2
  have log_z1 : Complex.log z1
      = ((-(Real.log 2 / 2) : ℝ) : ℂ) + ((π / 4 : ℝ) : ℂ) * I := by
    have := log_one_sub_z2; rwa [show (1 : ℂ) - z2 = z1 by rw [z1, z2]; ring] at this
  have log_z2 : Complex.log z2
      = ((-(Real.log 2 / 2) : ℝ) : ℂ) + ((-(π / 4) : ℝ) : ℂ) * I := by
    have := log_one_sub_z1; rwa [show (1 : ℂ) - z1 = z2 by rw [z1, z2]; ring] at this
  have log_half : Complex.log (2⁻¹ : ℂ) = -((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2⁻¹ : ℂ) = (((2⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by norm_num), Real.log_inv]
    push_cast; ring
  rw [log_half] at r1
  rw [log_z1, log_z2] at r2
  push_cast at r1 r2 ⊢
  linear_combination (-4 : ℂ) * r1 + 16 * r2 + ((Real.pi : ℂ) ^ 2) * Complex.I_sq

/-- **The master dilog sum.**  The analytic convergence is fully proved
here (each of the four points lies in the open unit disk, so `w2` is a
finite combination of convergent dilog series); the value is reduced via
`dilog_add_neg` to `dilog_special_values`, the sole remaining crux. -/
theorem hasSum_w2 : HasSum w2 (((Real.pi ^ 2 : ℝ)) : ℂ) := by
  have h1 := (hasSum_Li2 norm_cx_lt).mul_left (-16)
  have h2 := (hasSum_Li2 norm_z1_lt).mul_left 16
  have h3 := (hasSum_Li2 norm_neg_cx_lt).mul_left (-16)
  have h4 := (hasSum_Li2 norm_z2_lt).mul_left 16
  have h := ((h1.add h2).add h3).add h4
  have hfun : (fun n : ℕ => -16 * (((x : ℝ) : ℂ) ^ n / (n : ℂ) ^ 2)
      + 16 * (z1 ^ n / (n : ℂ) ^ 2) + -16 * ((-((x : ℝ) : ℂ)) ^ n / (n : ℂ) ^ 2)
      + 16 * (z2 ^ n / (n : ℂ) ^ 2)) = w2 := by
    funext n; rw [w2]; ring
  rw [hfun] at h
  -- reduce the value: −16·Li₂(x) − 16·Li₂(−x) = −8·Li₂(x²) = −8·Li₂(½)
  have hd := dilog_add_neg (z := ((x : ℝ) : ℂ)) norm_cx_lt
  rw [cx_sq] at hd
  have hval : -16 * Li2 ((x : ℝ) : ℂ) + 16 * Li2 z1 + -16 * Li2 (-((x : ℝ) : ℂ))
      + 16 * Li2 z2 = ((Real.pi ^ 2 : ℝ) : ℂ) := by
    have := dilog_special_values
    linear_combination (-16) * hd + this
  rw [hval] at h
  exact h

end PiSqBBPProof

open PiSqBBPProof in
/-- **Lane-2 discharge of the frozen node `PiSqBBP`** (Formula 29):
the π² BBP series sums to π².  Rests on the single analytic crux
`hasSum_w2` (the dilog special-value combination — see file header). -/
theorem piSqBBP_proved : PiSqBBP := by
  rw [PiSqBBP, ← Complex.hasSum_ofReal]
  have h : HasSum (w2 ∘ (Nat.divModEquiv 8).symm) (((Real.pi ^ 2 : ℝ)) : ℂ) :=
    ((Nat.divModEquiv 8).symm.hasSum_iff).mpr hasSum_w2
  exact HasSum.prod_fiberwise h hasSum_fiber2

end NormalNumbers
