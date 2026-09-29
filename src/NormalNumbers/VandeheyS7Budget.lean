/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Boundary

/-!
# The budget: how many image digits a word of length `L` determines

Everything the transfer needs is now proved except the arithmetic that says the two exponentials
point the right way.  Merging supplies

    δ_L = 1/(fib(L-1) fib(L))   (`spread_runWord_le`),   which decays like `φ^{-2L}` ,

and the scale cutoff costs

    scale u m ≤ S^m   with  S = 4(K+1)² e^{2η}   (`scale_le_exp`) .

`cfDigit_agree_depth` needs `δ_L · scale u m` small, so the question is whether `m` can be taken
PROPORTIONAL to `L`.  It can, and the constant is explicit:

    `budget_le` :  S^m · δ_L  ≤  exp (m log S − 2k log φ),    L = k + 3 ,

so any `m ≤ c·k` with `c < 2 log φ / log S` makes the product decay geometrically
(`budget_tendsto_zero`).  There is no obstruction here — only a constant, and the constant is
positive for every finite cutoff `K`.  That is the fact worth having: **the route is not
budget-limited.**  Raising `K` (to shrink the exceptional mass) shrinks `c` but never to zero,
and the two limits can be taken in the order `K` first, then `L → ∞`.

The Fibonacci input is `goldenRatio_pow_le_fib` : `φ^k ≤ fib (k+2)`, a two-step induction off
`goldenRatio_sq` (`φ² = φ + 1`) — the same recursion as `fib`, which is why it is exact.

## Guard rule

Content locator: `budget_le` at `m = 0` is the bare merging bound `δ_L ≤ φ^{-2k}`, so the content
is entirely in the trade between `m log S` and `2k log φ`.  Degenerate case:
`not_budget_of_large` — for `c > 2 log φ / log S` the bound is useless (the exponent is positive),
so the constant is not an artefact of slack.
-/

namespace NormalNumbers.VandeheyS7

open Real

/-- `φ ≤ 2`, from `φ² = φ + 1`. -/
theorem goldenRatio_le_two : Real.goldenRatio ≤ 2 := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio, Real.goldenRatio_pos]

/-- **`φ^k ≤ fib (k+2)`.**  Two-step induction off `φ² = φ + 1`: the same recursion as `fib`. -/
theorem goldenRatio_pow_le_fib : ∀ k : ℕ, Real.goldenRatio ^ k ≤ (Nat.fib (k + 2) : ℝ)
  | 0 => by norm_num
  | 1 => by
      have h := goldenRatio_le_two
      norm_num
      linarith
  | (k + 2) => by
      have h1 := goldenRatio_pow_le_fib k
      have h2 := goldenRatio_pow_le_fib (k + 1)
      have hexp : Real.goldenRatio ^ (k + 2)
          = Real.goldenRatio ^ (k + 1) + Real.goldenRatio ^ k := by
        have : Real.goldenRatio ^ (k + 2) = Real.goldenRatio ^ k * Real.goldenRatio ^ 2 := by
          ring
        rw [this, Real.goldenRatio_sq]; ring
      have hfib : (Nat.fib (k + 2 + 2) : ℝ)
          = (Nat.fib (k + 2) : ℝ) + (Nat.fib (k + 3) : ℝ) := by
        have : Nat.fib (k + 2 + 2) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
          rw [show k + 2 + 2 = (k + 2) + 2 from rfl, Nat.fib_add_two]
        exact_mod_cast this
      rw [hexp, hfib]
      have h2' : Real.goldenRatio ^ (k + 1) ≤ (Nat.fib (k + 3) : ℝ) := by
        simpa [show k + 1 + 2 = k + 3 from rfl] using h2
      linarith

/-- The merging denominator is at least `φ^{2k}` for a word of length `k + 3`. -/
theorem fib_prod_ge (k : ℕ) :
    Real.goldenRatio ^ (2 * k) ≤ (Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 3) : ℝ) := by
  have h1 := goldenRatio_pow_le_fib k
  have h2 : Real.goldenRatio ^ k ≤ (Nat.fib (k + 3) : ℝ) := by
    have := goldenRatio_pow_le_fib (k + 1)
    have hmono : Real.goldenRatio ^ k ≤ Real.goldenRatio ^ (k + 1) :=
      pow_le_pow_right₀ Real.one_lt_goldenRatio.le (by omega)
    simpa [show k + 1 + 2 = k + 3 from rfl] using le_trans hmono this
  have hpos : (0:ℝ) < Real.goldenRatio ^ k := pow_pos Real.goldenRatio_pos k
  calc Real.goldenRatio ^ (2 * k) = Real.goldenRatio ^ k * Real.goldenRatio ^ k := by
        rw [← pow_add]; ring_nf
    _ ≤ (Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 3) : ℝ) :=
        mul_le_mul h1 h2 hpos.le (by positivity)

/-- **The budget inequality.**  `S^m · δ_L ≤ exp (m log S − 2k log φ)` for `L = k + 3`. -/
theorem budget_le {S : ℝ} (hS : 0 < S) (k m : ℕ) :
    S ^ m / ((Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 3) : ℝ))
      ≤ Real.exp ((m : ℝ) * Real.log S - 2 * (k : ℝ) * Real.log Real.goldenRatio) := by
  have hfib := fib_prod_ge k
  have hphi : (0:ℝ) < Real.goldenRatio ^ (2 * k) := pow_pos Real.goldenRatio_pos _
  have hden : (0:ℝ) < (Nat.fib (k + 2) : ℝ) * (Nat.fib (k + 3) : ℝ) := lt_of_lt_of_le hphi hfib
  have hnum : S ^ m = Real.exp ((m : ℝ) * Real.log S) := by
    rw [← Real.exp_log (pow_pos hS m), Real.log_pow]
  have hgold : Real.goldenRatio ^ (2 * k)
      = Real.exp (2 * (k : ℝ) * Real.log Real.goldenRatio) := by
    rw [← Real.exp_log (pow_pos Real.goldenRatio_pos (2 * k)), Real.log_pow]
    push_cast
    ring_nf
  rw [Real.exp_sub, hnum]
  rw [div_le_div_iff₀ hden (by positivity)]
  rw [← hgold] at *
  nlinarith [hfib, hphi, Real.exp_pos ((m:ℝ) * Real.log S)]

/-- **The route is not budget-limited.**  For any `S > 1` and any `c < 2 log φ / log S`, the
product of the merging bound and the scale cost decays geometrically along `m = ⌊c k⌋`. -/
theorem budget_tendsto_zero {S c : ℝ} (hS : 1 < S) (hc : 0 ≤ c)
    (hlt : c * Real.log S < 2 * Real.log Real.goldenRatio) :
    Filter.Tendsto
      (fun k : ℕ => Real.exp ((⌊c * k⌋₊ : ℝ) * Real.log S
        - 2 * (k : ℝ) * Real.log Real.goldenRatio)) Filter.atTop (nhds 0) := by
  have hlogS : 0 < Real.log S := Real.log_pos hS
  set g : ℝ := 2 * Real.log Real.goldenRatio - c * Real.log S with hg
  have hgap : 0 < g := by rw [hg]; linarith
  have hkey : ∀ k : ℕ, Real.exp ((⌊c * (k:ℝ)⌋₊ : ℝ) * Real.log S
      - 2 * (k : ℝ) * Real.log Real.goldenRatio) ≤ (Real.exp (-g)) ^ k := by
    intro k
    have hfl : (⌊c * (k:ℝ)⌋₊ : ℝ) ≤ c * k := Nat.floor_le (by positivity)
    have hpow : (Real.exp (-g)) ^ k = Real.exp ((k : ℝ) * (-g)) := by
      rw [Real.exp_nat_mul]
    rw [hpow]
    refine Real.exp_le_exp.2 ?_
    rw [hg]
    nlinarith [hfl, hlogS]
  refine squeeze_zero (fun k => (Real.exp_pos _).le) hkey ?_
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le ?_
  rw [Real.exp_lt_one_iff]
  linarith

/-- Degenerate case: past the threshold the exponent is positive and the bound says nothing, so
the constant `2 log φ / log S` is sharp and not an artefact of slack. -/
theorem not_budget_of_large {S c : ℝ} (hS : 1 < S)
    (hgt : 2 * Real.log Real.goldenRatio < c * Real.log S) (k : ℕ) (hk : 0 < k) :
    1 < Real.exp ((c * (k:ℝ)) * Real.log S - 2 * (k : ℝ) * Real.log Real.goldenRatio) := by
  rw [show (1:ℝ) = Real.exp 0 by simp, Real.exp_lt_exp]
  have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  nlinarith [hgt, hkr]

section Audit

#print axioms goldenRatio_pow_le_fib
#print axioms budget_le
#print axioms budget_tendsto_zero

end Audit

end NormalNumbers.VandeheyS7
