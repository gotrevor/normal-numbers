/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-GR: the stall clock is dominated by the slack, linearly

S7-DB bounded the height below by `fib(stallAge + 1)`; S7-SK made the slack
`slack n = log d_{n+2} − log √(|det Φ|/6)` the single scalar the width leg runs on.  To use the
first inside the second one needs the Fibonacci growth in *log* form, i.e. a linear — not
logarithmic — comparison.  That is this module:

* `two_pow_le_fib` — `2^k ≤ fib (2k+1)`, by the two-step induction `fib(2k+3) ≥ 2·fib(2k+1)`.
  (Enough: any exponential base beats the `log` and the constant is irrelevant.  Avoiding the
  golden ratio here keeps the proof to four lines.)
* `stallAge_le_slack` — **`stallAge n ≤ 1 + 2·slack n / log 2`**, so the stall clock is at most
  an affine function of the slack, pointwise.

Consequence, recorded for the next step: `Σ_{n<q} stallAge (n+2) ≤ 3q + (2/log 2)·Σ_{n<q} slack n`,
so `MeanSlack` bounds the *mean stall age*.  With the reset-counting bound
`#{n < q : stallAge n < K} ≤ K·(runClock q + 1)` this forces `runClock q ≥ δ·q` — i.e.
**`ClockLinear` is a CONSEQUENCE of `MeanSlack`**, and the §7 front (S7-FT) drops from three
hypotheses to two.
-/
import NormalNumbers.VandeheyS7Slack

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

/-- `2^k ≤ fib (2k+1)`. -/
theorem two_pow_le_fib : ∀ k : ℕ, 2 ^ k ≤ Nat.fib (2 * k + 1)
  | 0 => by norm_num
  | k + 1 => by
      have ih := two_pow_le_fib k
      have hstep : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) :=
        Nat.fib_add_two
      have hmono : Nat.fib (2 * k + 1) ≤ Nat.fib (2 * k + 2) :=
        Nat.fib_mono (by omega)
      have : 2 * (2:ℕ) ^ k ≤ Nat.fib (2 * k + 3) := by omega
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ Nat.fib (2 * k + 3) := this
        _ = Nat.fib (2 * (k + 1) + 1) := by ring_nf

namespace MapState

/-- **The stall clock is affine in the slack.** -/
theorem stallAge_le_slack (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    ((min (stallAge Φ x (n + 2)) n : ℕ) : ℝ) ≤ 1 + 2 * slack Φ x n / Real.log 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set a := min (stallAge Φ x (n + 2)) n with ha
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hs : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  have hdpos : (0:ℝ) < (runState Φ x (n + 2)).d := (runState Φ x (n + 2)).hd
  have hfibpos : (0:ℝ) < (Nat.fib (a + 1) : ℝ) := by
    have : 0 < Nat.fib (a + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  -- the height bound, in log form
  have hd := sqrt_mul_fib_stallAge_le_d Φ hx n
  rw [← ha] at hd
  have hlog := Real.log_le_log (by positivity) hd
  rw [Real.log_mul hs.ne' hfibpos.ne'] at hlog
  have hslack : Real.log (Nat.fib (a + 1) : ℝ) ≤ slack Φ x n := by
    simp only [slack]; linarith
  -- Fibonacci grows at least like `2^(a/2)`
  have hpow : (2:ℕ) ^ (a / 2) ≤ Nat.fib (a + 1) :=
    le_trans (two_pow_le_fib (a / 2)) (Nat.fib_mono (by omega))
  have hpowR : ((2:ℝ)) ^ (a / 2) ≤ (Nat.fib (a + 1) : ℝ) := by
    exact_mod_cast hpow
  have hlogpow : ((a / 2 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (Nat.fib (a + 1) : ℝ) := by
    have h := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at h
  have hhalf : ((a : ℝ) - 1) / 2 ≤ ((a / 2 : ℕ) : ℝ) := by
    have h := Nat.div_add_mod a 2
    have hmod : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have : (a : ℝ) = 2 * ((a / 2 : ℕ) : ℝ) + ((a % 2 : ℕ) : ℝ) := by exact_mod_cast h.symm
    have hm : ((a % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hmod
    linarith
  have hchain : ((a : ℝ) - 1) / 2 * Real.log 2 ≤ slack Φ x n := by
    calc ((a : ℝ) - 1) / 2 * Real.log 2 ≤ ((a / 2 : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hhalf hlog2.le
      _ ≤ Real.log (Nat.fib (a + 1) : ℝ) := hlogpow
      _ ≤ slack Φ x n := hslack
  have hfin : (a:ℝ) - 1 ≤ 2 * slack Φ x n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    linarith
  linarith

end MapState

section Audit

#print axioms two_pow_le_fib
#print axioms MapState.stallAge_le_slack

end Audit

end NormalNumbers.VandeheyS7
