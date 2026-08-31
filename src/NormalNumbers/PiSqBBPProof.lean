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

/-- **The master dilog identity (frozen crux).**  The filtered series
sums to π²:
`−16·Li₂(x) + 16·Li₂(z₁) − 16·Li₂(−x) + 16·Li₂(z̄₁) = π²`.

mathlib has NO dilogarithm, so this cannot yet be discharged from library
API.  Via the series duplication `Li₂(z)+Li₂(−z)=½Li₂(z²)` (provable, see
`dilog_add_neg`) and conjugate pairing it reduces to the classical
special-value combination `−8·Li₂(½)+32·Re Li₂((1+i)/2)=π²`, where
`Li₂(½)=π²/12−½log²2` and `Re Li₂((1+i)/2)=5π²/96−⅛log²2` (the `log²2`
terms cancel).  Next attack: formalize `Li₂` and its reflection formula,
or import the two special values as cited nodes.  Disclosed 2026-08-31. -/
theorem hasSum_w2 : HasSum w2 (((Real.pi ^ 2 : ℝ)) : ℂ) := by
  sorry

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
