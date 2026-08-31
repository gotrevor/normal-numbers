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

**STATUS (2026-08-31): FULLY PROVED, axiom-clean.**  mathlib has no
dilogarithm, so the whole theory was built from scratch here:
* `Li2 z := ∑' zⁿ/n²` with `dilogSummable`;
* term-wise derivative `hasDerivAt_Li2` / closed form `hasDerivAt_Li2'`
  (`Li₂' w = −log(1−w)/w`);
* the duplication `dilog_add_neg` (even/odd split, no special functions);
* the **reflection formula** `dilog_reflection`
  (`Li₂ z + Li₂(1−z) = π²/6 − log z·log(1−z)`), proved by `F' ≡ 0` on the
  lens `ball 0 1 ∩ ball 1 1` (`hasDerivAt_dilogRefl` + `dilogF_const`)
  with the constant pinned to `π²/6` by the `t→0⁺` boundary limit
  (`dilogF_value`: `Li₂ 0 = 0`, `Li₂ 1 = π²/6` via Abel + `hasSum_zeta_two`,
  `log t·log(1−t) → 0`);
* `dilog_special_values` (`−8·Li₂(½) + 16·(Li₂ z₁ + Li₂ z̄₁) = π²`) from
  reflection at `½` and `z₁`;
* `hasSum_w2` (analytic convergence) + `hasSum_fiber2` (fiber algebra) →
  `piSqBBP_proved` via `divModEquiv` + `HasSum.prod_fiberwise`.

`#print axioms piSqBBP_proved` = `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`).
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

/-- **Derivative cancellation for the reflection identity.**  On the
region where `z`, `1−z` are both in the open unit disk and both in the
slit plane, the function `F w = Li₂ w + Li₂(1−w) + log w·log(1−w)` has
zero derivative: `−log(1−z)/z + log z/(1−z) + [log(1−z)/z − log z/(1−z)]
= 0`.  This is the analytic core of the reflection formula. -/
theorem hasDerivAt_dilogRefl {z : ℂ} (hz : ‖z‖ < 1) (hz1 : ‖1 - z‖ < 1)
    (hzs : z ∈ Complex.slitPlane) (hz1s : (1 - z) ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Li2 w + Li2 (1 - w) + Complex.log w * Complex.log (1 - w))
      0 z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hz1_0 : (1 - z) ≠ 0 := Complex.slitPlane_ne_zero hz1s
  have inner : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have d1 := hasDerivAt_Li2' hz hz0
  have d2 := (hasDerivAt_Li2' hz1 hz1_0).comp z inner
  have dlog1 := Complex.hasDerivAt_log hzs
  have dlog2 := (Complex.hasDerivAt_log hz1s).comp z inner
  have d3 := dlog1.mul dlog2
  have hsum := (d1.add d2).add d3
  simp only [Function.comp] at hsum
  have hV : (-Complex.log (1 - z) / z + -Complex.log (1 - (1 - z)) / (1 - z) * -1)
      + (z⁻¹ * Complex.log (1 - z) + Complex.log z * ((1 - z)⁻¹ * -1)) = 0 := by
    rw [show (1 : ℂ) - (1 - z) = z by ring]
    field_simp
    ring
  rw [hV] at hsum
  exact hsum

/-- The reflection function `F w = Li₂ w + Li₂(1−w) + log w·log(1−w)`. -/
noncomputable def dilogF (w : ℂ) : ℂ :=
  Li2 w + Li2 (1 - w) + Complex.log w * Complex.log (1 - w)

/-- The reflection lens `{‖z‖<1 ∧ ‖1−z‖<1} = ball 0 1 ∩ ball 1 1` — the
region where both dilog series converge; convex, open, and (crucially)
contained in the slit plane. -/
def lensL : Set ℂ := Metric.ball 0 1 ∩ Metric.ball 1 1

lemma mem_lensL {z : ℂ} : z ∈ lensL ↔ ‖z‖ < 1 ∧ ‖1 - z‖ < 1 := by
  simp only [lensL, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Complex.dist_eq]
  rw [norm_sub_rev]

lemma lensL_open : IsOpen lensL := Metric.isOpen_ball.inter Metric.isOpen_ball

lemma lensL_convex : Convex ℝ lensL := (convex_ball _ _).inter (convex_ball _ _)

lemma mem_slitPlane_of_mem_lensL {z : ℂ} (hz : z ∈ lensL) : z ∈ Complex.slitPlane := by
  rw [mem_lensL] at hz
  by_contra h
  rw [Complex.slitPlane, Set.mem_ofPred_eq, not_or, not_lt, not_not] at h
  obtain ⟨hre, him⟩ := h
  have hz0 : z = ((z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hz0] at hz
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  rw [show (1 : ℂ) - ((z.re : ℝ) : ℂ) = ((1 - z.re : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs] at h2
  rw [abs_lt] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

lemma one_sub_mem_lensL {z : ℂ} (hz : z ∈ lensL) : (1 - z) ∈ lensL := by
  rw [mem_lensL] at hz ⊢
  rw [show (1 : ℂ) - (1 - z) = z by ring, norm_sub_rev] at *
  exact ⟨hz.2, hz.1⟩

lemma hasDerivAt_dilogF {z : ℂ} (hz : z ∈ lensL) : HasDerivAt dilogF 0 z := by
  rw [mem_lensL] at hz
  exact hasDerivAt_dilogRefl hz.1 hz.2 (mem_slitPlane_of_mem_lensL (mem_lensL.mpr hz))
    (mem_slitPlane_of_mem_lensL (one_sub_mem_lensL (mem_lensL.mpr hz)))

/-- **F is constant on the lens.**  Immediate from `F' ≡ 0`
(`hasDerivAt_dilogF`) on the open convex (hence preconnected) lens. -/
lemma dilogF_const {z w : ℂ} (hz : z ∈ lensL) (hw : w ∈ lensL) : dilogF z = dilogF w := by
  refine IsOpen.is_const_of_fderiv_eq_zero (𝕜 := ℂ) lensL_open
    (lensL_convex.isPreconnected) ?_ ?_ hz hw
  · intro x hx
    exact (hasDerivAt_dilogF hx).differentiableAt.differentiableWithinAt
  · intro x hx
    have h : HasFDerivAt dilogF (0 : ℂ →L[ℂ] ℂ) x := by
      simpa using (hasDerivAt_dilogF hx).hasFDerivAt
    simpa using h.fderiv

open Filter Topology in
/-- `Li₂ 0 = 0`. -/
lemma Li2_zero : Li2 (0 : ℂ) = 0 := by
  rw [Li2]
  have : (fun n : ℕ => (0 : ℂ) ^ n / (n : ℂ) ^ 2) = fun _ => 0 := by
    funext n; rcases n with _ | m <;> simp
  rw [this]; exact tsum_zero

open Filter Topology in
/-- `Li₂ (↑t) → 0` as `t → 0⁺`. -/
lemma tendsto_Li2_zero :
    Tendsto (fun t : ℝ => Li2 (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hcont : ContinuousAt Li2 0 :=
    (hasDerivAt_Li2 (by rw [norm_zero]; norm_num)).continuousAt
  have hofR : Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left nhdsWithin_le_nhds
  have := (hcont.tendsto).comp hofR
  rwa [Li2_zero] at this

open Filter Topology in
/-- `Li₂ (↑s) → π²/6` as `s → 1⁻` — Abel's limit theorem applied to the
`ζ(2)` series. -/
lemma tendsto_Li2_one :
    Tendsto (fun s : ℝ => Li2 (s : ℂ)) (𝓝[<] 1) (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
  have hps : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (1 / (i : ℝ) ^ 2))
      atTop (𝓝 (Real.pi ^ 2 / 6)) := hasSum_zeta_two.tendsto_sum_nat
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hps
  have hcast := (Complex.continuous_ofReal.tendsto (Real.pi ^ 2 / 6)).comp habel
  refine hcast.congr ?_
  intro s
  rw [Function.comp_apply, Complex.ofReal_tsum]
  rw [Li2]
  congr 1
  funext n
  push_cast
  ring

open Filter Topology in
/-- `Real.log t · Real.log (1−t) → 0` as `t → 0⁺`:
`= (t·log t)·(log(1−t)/t) → 0·(−1)`. -/
lemma tendsto_reallogprod :
    Tendsto (fun t : ℝ => Real.log t * Real.log (1 - t)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    have hc := continuous_negMulLog.tendsto (0 : ℝ)
    rw [negMulLog_zero] at hc
    simpa [negMulLog] using (hc.mono_left nhdsWithin_le_nhds).neg
  have inner : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have outer : HasDerivAt Real.log (1 : ℝ)⁻¹ (1 - (0 : ℝ)) := by
    rw [sub_zero]; exact Real.hasDerivAt_log (by norm_num)
  have hd : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1) 0 := by
    have h := outer.comp 0 inner
    simpa [Function.comp_def] using h
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have h2 : Tendsto (fun t : ℝ => Real.log (1 - t) / t) (𝓝[>] 0) (𝓝 (-1)) := by
    refine ((hasDerivAt_iff_tendsto_slope.mp hd).mono_left hsub).congr ?_
    intro t
    simp [slope_def_field, Real.log_one]
  have hprod : Tendsto (fun t : ℝ => t * Real.log t * (Real.log (1 - t) / t))
      (𝓝[>] 0) (𝓝 0) := by simpa using h1.mul h2
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp

open Filter Topology in
/-- `log t · log(1−t) → 0` (complex logs of the real approach) as `t→0⁺`. -/
lemma tendsto_logprod :
    Tendsto (fun t : ℝ => Complex.log (t : ℂ) * Complex.log (1 - (t : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  have hcast : Tendsto (fun t : ℝ => (((Real.log t * Real.log (1 - t) : ℝ)) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).comp tendsto_reallogprod
    simpa only [Function.comp_def] using this
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine hcast.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
  have hpos : (0 : ℝ) ≤ t := le_of_lt ht
  have hpos2 : (0 : ℝ) ≤ 1 - t := by simp only [Set.mem_Ioi] at ht; linarith
  rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log hpos, ← Complex.ofReal_log hpos2, ← Complex.ofReal_mul]

open Filter Topology in
theorem dilogF_value : dilogF (2⁻¹ : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  -- as `t → 0⁺`, `1 − t → 1⁻`
  have hmap : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Iio]; simp only [Set.mem_Ioi] at ht; linarith
  -- `Li₂(1 − ↑t) → π²/6`
  have hLi2one : Tendsto (fun t : ℝ => Li2 (1 - (t : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
    refine (tendsto_Li2_one.comp hmap).congr ?_
    intro t
    simp only [Function.comp_apply]
    congr 1
    push_cast; ring
  -- assemble the three limits: `dilogF ↑t → 0 + π²/6 + 0`
  have hlim : Tendsto (fun t : ℝ => dilogF (t : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
    have h := (tendsto_Li2_zero.add hLi2one).add tendsto_logprod
    simpa [dilogF] using h
  -- `dilogF ↑t` is eventually constant `= dilogF ½` (constancy on the lens)
  have hhalf : (2⁻¹ : ℂ) ∈ lensL := by
    rw [mem_lensL, show (1 : ℂ) - 2⁻¹ = 2⁻¹ by ring, norm_inv]
    norm_num [Complex.norm_ofNat]
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hconst : Tendsto (fun t : ℝ => dilogF (t : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (dilogF (2⁻¹ : ℂ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
    simp only [Set.mem_Ioi] at ht
    have htL : (t : ℂ) ∈ lensL := by
      rw [mem_lensL]
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]; exact ht1
      · rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    exact (dilogF_const htL hhalf).symm
  exact tendsto_nhds_unique hconst hlim

/-- **Dilog reflection formula (frozen crux).**  For `z` and `1−z` both
in the open unit disk,
`Li₂ z + Li₂ (1−z) = π²/6 − log z · log(1−z)`.

The derivative-cancellation (`hasDerivAt_dilogF`) and constancy on the
lens (`dilogF_const`) are PROVED; this theorem is now `dilogF_const` at
`z` versus `½`, closed by `dilogF_value` (the pinned constant `= π²/6`).
Disclosed 2026-08-31. -/
theorem dilog_reflection {z : ℂ} (hz : ‖z‖ < 1) (hz1 : ‖1 - z‖ < 1) :
    Li2 z + Li2 (1 - z)
      = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) - Complex.log z * Complex.log (1 - z) := by
  have hzL : z ∈ lensL := mem_lensL.mpr ⟨hz, hz1⟩
  have hhalf : (2⁻¹ : ℂ) ∈ lensL := by
    rw [mem_lensL, show (1 : ℂ) - 2⁻¹ = 2⁻¹ by ring, norm_inv]
    norm_num [Complex.norm_ofNat]
  have hconst := dilogF_const hzL hhalf
  rw [dilogF_value, dilogF] at hconst
  linear_combination hconst

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
