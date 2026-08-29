/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# log² 2 through the summed-kick machine (target 5, optional dessert)

Lane-2 target 5 (2026-08-29 operator brief): instantiate the summed-kick
machine (`KickedOrbit.lean`) for a second constant.  `log² 2` is chosen
over `π²` because its series is elementary: the classical generating-
function identity (integrate `Σ Hₙ xⁿ = −log(1−x)/(1−x)`) gives at
`x = 1/2`

  `log² 2 = Σ_{m≥1} (2·H_{m−1}/m) · 2^{−m}`   (`H₀ = 0`, so the `m = 1`
  kick vanishes),

i.e. base `b = 2` with kick numerators `r m = 2·H_{m−1}/m`.

## Obligations (mirror `PiBBP.lean`)

1. ⚠️ PROBE FIRST: an `experiments/` script verifying the identity
   numerically to high precision (the node discipline — every frozen
   node carries a refutation probe).  If the probe FAILS, stop and
   record the failure: the identity as stated is wrong, do not freeze it.
2. The node `LogTwoSqSeries` below (CITED-class, hypothesis-not-axiom;
   the in-house Cauchy-product derivation is a later lane-2 discharge,
   like `PiBBP` was).
3. Elementary kick bounds: `r` is eventually `< 1` (base 2 makes the
   constant cap `A = 1` VACUOUS — the sliver `1 − A/(b−1)` empties — so
   the cap must be position-dependent: for `m > n` use an explicit
   decreasing bound like `A n = 2·(1 + Real.log (n+1))/(n+1)`, from
   `H_{m−1} ≤ 1 + log (m−1)`; the floor uses `H` monotone:
   `r (n+1) ≥ 2·H_n/(n+1) > 0` for `n ≥ 1`).
4. The sliver headline below via `top_sliver_of_zeroRun_kicked`; a
   `_maxRun` twin via `top_sliver_of_maxRun_kicked` once `A n ≤ 1/2`.

⚠️ DRAFT STATEMENT — the headline's thresholds and the explicit cap are
first guesses; restate to what the machine honestly yields (keep the
name, keep the conditional-on-node shape, ADDITIVE ONLY elsewhere).
-/

namespace NormalNumbers

/-- Harmonic number `H_m = Σ_{k=1}^{m} 1/k` (real-valued). -/
noncomputable def harmonicR (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1)

/-- The kick numerators of `log² 2`: `r m = 2·H_{m−1}/m` (`r 0 = r 1 = 0`). -/
noncomputable def logTwoSqKick (m : ℕ) : ℝ :=
  2 * harmonicR (m - 1) / m

/-- **Node (frozen, CITED-class): the `log² 2` series** —
`log² 2 = Σ_{m≥1} (2·H_{m−1}/m)·2^{−m}`, classical (integrated harmonic
generating function at `x = 1/2`), stated in the summed-kick machine's
indexing.  Lane-2 discharge owed, like `PiBBP` was. -/
def LogTwoSqSeries : Prop :=
  HasSum (fun m : ℕ => logTwoSqKick (m + 1) / (2 : ℝ) ^ (m + 1))
    (Real.log 2 ^ 2)

/-! ### Elementary kick bounds

Base 2 makes any constant cap vacuous (`1 − A/(b−1)` empties at `A = 1`),
so the cap is position-dependent: past position `n` every kick is at most
`A n = 2·(1 + log (n+1))/(n+1)`, from `H_{m−1} ≤ 1 + log (m−1)` (mathlib's
`harmonic_le_one_add_log`) plus antitonicity of `x ↦ (1 + log x)/x` on
`[1, ∞)`.  The floor is the first omitted kick itself,
`r (n+1) = 2·H_n/(n+1)`. -/

lemma harmonicR_nonneg (m : ℕ) : 0 ≤ harmonicR m :=
  Finset.sum_nonneg fun k _ => by positivity

lemma harmonicR_eq_harmonic (m : ℕ) : harmonicR m = (harmonic m : ℝ) := by
  unfold harmonicR harmonic
  push_cast
  simp [one_div]

lemma logTwoSqKick_nonneg (m : ℕ) : 0 ≤ logTwoSqKick m :=
  div_nonneg (mul_nonneg (by norm_num) (harmonicR_nonneg _)) (Nat.cast_nonneg m)

/-- Antitonicity of `x ↦ (1 + log x)/x` on `[1, ∞)`: for `1 ≤ a ≤ b`,
`(1 + log b)/b ≤ (1 + log a)/a`.  Elementary from `log (b/a) ≤ b/a − 1`. -/
lemma one_add_log_div_le_of_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 + Real.log b) / b ≤ (1 + Real.log a) / a := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  rw [div_le_div_iff₀ hb0 ha0]
  have hlog : Real.log b - Real.log a ≤ b / a - 1 := by
    have h1 : Real.log (b / a) ≤ b / a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rwa [Real.log_div hb0.ne' ha0.ne'] at h1
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have f1 : a * (Real.log b - Real.log a) ≤ b - a := by
    have h2 := mul_le_mul_of_nonneg_left hlog ha0.le
    have h3 : a * (b / a - 1) = b - a := by field_simp
    linarith [h3 ▸ h2]
  have f2 : a * Real.log a ≤ b * Real.log a :=
    mul_le_mul_of_nonneg_right hab hla
  nlinarith [f1, f2]

/-- **Position-dependent cap**: every kick past position `n` is at most
`2·(1 + log (n+1))/(n+1)`. -/
lemma logTwoSqKick_le_cap (n : ℕ) : ∀ m, n + 1 ≤ m →
    logTwoSqKick m ≤ 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  intro m hm
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hcap0 : 0 ≤ 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by positivity
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- `m ∈ {0, 1}`: the kick vanishes (`H₀ = 0`, and `r 0 = 0/0 = 0`)
    interval_cases m <;>
      simpa [logTwoSqKick, harmonicR] using hcap0
  · -- `m ≥ 2`: `H_{m−1} ≤ 1 + log (m−1) ≤ 1 + log m`, then antitonicity
    have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
    have hm1R : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      have : 1 ≤ m - 1 := by omega
      exact_mod_cast this
    have hH : harmonicR (m - 1) ≤ 1 + Real.log ((m : ℝ)) := by
      calc harmonicR (m - 1) = (harmonic (m - 1) : ℝ) := harmonicR_eq_harmonic _
        _ ≤ 1 + Real.log ((m - 1 : ℕ) : ℝ) := harmonic_le_one_add_log _
        _ ≤ 1 + Real.log (m : ℝ) := by
            have hle : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
              exact_mod_cast Nat.sub_le m 1
            linarith [Real.log_le_log (by linarith : (0 : ℝ) < ((m - 1 : ℕ) : ℝ)) hle]
    have step1 : logTwoSqKick m ≤ 2 * ((1 + Real.log (m : ℝ)) / (m : ℝ)) := by
      unfold logTwoSqKick
      have hd : harmonicR (m - 1) / (m : ℝ) ≤ (1 + Real.log (m : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hH hm0.le
      calc 2 * harmonicR (m - 1) / (m : ℝ)
          = 2 * (harmonicR (m - 1) / (m : ℝ)) := by ring
        _ ≤ 2 * ((1 + Real.log (m : ℝ)) / (m : ℝ)) := by linarith
    have step2 : (1 + Real.log (m : ℝ)) / (m : ℝ)
        ≤ (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      apply one_add_log_div_le_of_le (by linarith)
      exact_mod_cast Nat.succ_le_of_lt (by omega : n < m)
    calc logTwoSqKick m ≤ 2 * ((1 + Real.log (m : ℝ)) / (m : ℝ)) := step1
      _ ≤ 2 * ((1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)) := by linarith
      _ = 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by ring

/-- **Headline**: conditional on the series node, a zero-run of binary
`log² 2` at position `n` deeper than the kick floor (`2⁻ᵏ < H_n/(n+1)`)
forces the truncated-series surrogate into the explicit top sliver
`[1 − 2(1 + log (n+1))/(n+1), 1)`, via `top_sliver_of_zeroRun_kicked`.
(The draft's `6 ≤ n` was unnecessary: `hk` already forces `H_n > 0`.) -/
theorem logTwoSq_top_sliver_of_zeroRun (hs : LogTwoSqSeries) {n k : ℕ}
    (hk : (1 : ℝ) / 2 ^ k < harmonicR n / ((n : ℝ) + 1))
    (h : OccursAt 2 (Real.log 2 ^ 2) (List.replicate k 0) n) :
    1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)
      ≤ Int.fract ((2 : ℝ) ^ n * kickedPartial 2 logTwoSqKick n) := by
  have hs' : HasSum (fun m : ℕ => logTwoSqKick (m + 1) / (2 : ℝ) ^ (m + 1))
      (Real.log 2 ^ 2) := hs
  have hsum : HasSum
      (fun m : ℕ => logTwoSqKick (m + 1) / ((2 : ℕ) : ℝ) ^ (m + 1))
      (Real.log 2 ^ 2) := by
    simpa using hs'
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcore := top_sliver_of_zeroRun_kicked (b := 2) le_rfl
    (x := Real.log 2 ^ 2)
    (A := 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1))
    (L := 2 * harmonicR n / ((n : ℝ) + 1)) (n := n) (k := k) hsum
    (fun m _ => logTwoSqKick_nonneg m)
    (fun m hm => logTwoSqKick_le_cap n m hm)
    (le_of_eq (by simp [logTwoSqKick]))
    (by
      push_cast
      calc (1 : ℝ) / 2 ^ k < harmonicR n / ((n : ℝ) + 1) := hk
        _ = 2 * harmonicR n / ((n : ℝ) + 1) / 2 := by ring)
    h
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hcore
  calc 1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)
      = 1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) / ((2 : ℝ) - 1) := by
        norm_num
    _ ≤ Int.fract ((2 : ℝ) ^ n * kickedPartial 2 logTwoSqKick n) := hcore

/-- **Cap decay discharge**: the position-dependent cap is at most `1/2`
for all `n ≥ 56`, from `log x ≤ 2(√x − 1)` and the quadratic
`x − 8√x + 4 ≥ 0` for `√x ≥ 4 + √12` (`x ≥ 57` suffices).  (Numerically
the cap crosses `1/2` already at `n = 14`; this elementary route is
deliberately lossy.) -/
lemma logTwoSqCap_le_half {n : ℕ} (hn : 56 ≤ n) :
    2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) ≤ 1 / 2 := by
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx57 : (57 : ℝ) ≤ x := by
    have : (56 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [hx]; linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set s : ℝ := Real.sqrt x with hsdef
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs754 : (754 : ℝ) / 100 ≤ s := by
    rw [hsdef]
    rw [show (754 : ℝ) / 100 = Real.sqrt (((754 : ℝ) / 100) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hlog : Real.log x ≤ 2 * (s - 1) := by
    have h1 : Real.log s ≤ s - 1 :=
      Real.log_le_sub_one_of_pos (by rw [hsdef]; positivity)
    have h2 : Real.log s = Real.log x / 2 := by
      rw [hsdef]; exact Real.log_sqrt hx0.le
    linarith [h2 ▸ h1]
  have hquad : x - 8 * s + 4 ≥ 0 := by nlinarith [hs754, hs2]
  rw [div_le_iff₀ hx0]
  linarith

/-- **Max-run twin**: once the position-dependent cap has decayed to `1/2`
(`hhalf`; true for all large `n`, see `logTwoSqCap_le_half`), a run of `k`
ones forces the surrogate into `[1 − A n − 2⁻ᵏ, 1)`, via
`top_sliver_of_maxRun_kicked`. -/
theorem logTwoSq_top_sliver_of_maxRun (hs : LogTwoSqSeries) {n k : ℕ}
    (hhalf : 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) ≤ 1 / 2)
    (hk : (1 : ℝ) / 2 ^ k < harmonicR n / ((n : ℝ) + 1))
    (h : OccursAt 2 (Real.log 2 ^ 2) (List.replicate k 1) n) :
    1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) - 1 / 2 ^ k
      ≤ Int.fract ((2 : ℝ) ^ n * kickedPartial 2 logTwoSqKick n) := by
  have hs' : HasSum (fun m : ℕ => logTwoSqKick (m + 1) / (2 : ℝ) ^ (m + 1))
      (Real.log 2 ^ 2) := hs
  have hsum : HasSum
      (fun m : ℕ => logTwoSqKick (m + 1) / ((2 : ℕ) : ℝ) ^ (m + 1))
      (Real.log 2 ^ 2) := by
    simpa using hs'
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcore := top_sliver_of_maxRun_kicked (b := 2) le_rfl
    (x := Real.log 2 ^ 2)
    (A := 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1))
    (L := 2 * harmonicR n / ((n : ℝ) + 1)) (n := n) (k := k) hsum
    (fun m _ => logTwoSqKick_nonneg m)
    (fun m hm => logTwoSqKick_le_cap n m hm)
    (le_of_eq (by simp [logTwoSqKick]))
    (by
      calc 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) / (((2 : ℕ) : ℝ) - 1)
          = 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by norm_num
        _ ≤ 1 / 2 := hhalf)
    (by
      push_cast
      calc (1 : ℝ) / 2 ^ k < harmonicR n / ((n : ℝ) + 1) := hk
        _ = 2 * harmonicR n / ((n : ℝ) + 1) / 2 := by ring)
    h
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hcore
  calc 1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) - 1 / 2 ^ k
      = 1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) / ((2 : ℝ) - 1)
        - 1 / 2 ^ k := by norm_num
    _ ≤ Int.fract ((2 : ℝ) ^ n * kickedPartial 2 logTwoSqKick n) := hcore

end NormalNumbers
