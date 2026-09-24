/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Period

/-!
# REFUTATION: no clever prime subset reaches into the window

Lap 7 pinned `ConjC3` to the window `log N ≪ K ≪ N`: the complete-period cancellation
(`sum_addChar_tailTrunc_eq_zero`) is only *usable* over a range `N` when the period
`∏_{P<p≤K} p ≈ e^K` is `≤ N`, forcing `K ≲ log N`; while the discarded mass
`∑_{K<p≤2N} b^{n mod p}/(b^p−1)` has mean `≍ loglog N − loglog K`, which needs `K` almost as
large as `N` to be small.

The obvious escape is to stop using *all* primes up to `K` and instead pick a clever finite set
`S` of primes: use the complete-period cancellation for the period `∏_{p∈S} p ≤ N`, and hope
`S` captures most of the harmonic weight `∑_{p∈S} 1/p` (which is what controls the discarded
mass, since the `p`-term has mean `1/((b−1)p)` over its period).

**This file refutes that escape, unconditionally.**  If every element of `S` is `≥ m` and
`∏_{p∈S} p ≤ N`, then `|S| ≤ log N / log m` and hence

    ∑_{p ∈ S} 1/p  ≤  log N / (m · log m).

So the captured harmonic weight is `o(1)` unless `m ≲ log N` — i.e. `S` must contain primes as
small as `log N`, which is exactly the regime lap 7 already has.  A subset cannot buy anything:
the product constraint and the harmonic weight are in direct, unavoidable tension.

(Sharpness: `S` = all primes in `(m, 2m]` has `∏ ≈ e^{2m}` and `∑ 1/p ≈ log 2 / log m`, matching
`log N/(m log m)` at `m ≈ log N` up to the constant.)
-/

open Finset

namespace NormalNumbers

/-- The product of a set of integers all `≥ m` is at least `m ^ |S|`. -/
theorem pow_card_le_prod_of_le {S : Finset ℕ} {m : ℕ} (hS : ∀ p ∈ S, m ≤ p) :
    m ^ S.card ≤ ∏ p ∈ S, p := by
  classical
  calc m ^ S.card = ∏ _p ∈ S, m := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' hS

/-- **Cardinality bound.**  A set of integers `≥ m ≥ 2` whose product is `≤ N` has at most
`log N / log m` elements. -/
theorem card_le_of_prod_le {S : Finset ℕ} {m N : ℕ} (hm : 2 ≤ m) (hN : 0 < N)
    (hS : ∀ p ∈ S, m ≤ p) (hprod : ∏ p ∈ S, p ≤ N) :
    (S.card : ℝ) ≤ Real.log N / Real.log m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hpow : (m : ℝ) ^ S.card ≤ (N : ℝ) := by
    have := pow_card_le_prod_of_le hS
    have h2 : (m ^ S.card : ℕ) ≤ N := le_trans this hprod
    exact_mod_cast h2
  rw [le_div_iff₀ hlogm]
  have hlog : Real.log ((m : ℝ) ^ S.card) ≤ Real.log N :=
    Real.log_le_log (by positivity) hpow
  rwa [Real.log_pow] at hlog

/-- **THE SUBSET REFUTATION.**  Any finite set `S` of integers `≥ m ≥ 2` whose product stays
below `N` — i.e. whose period is usable over a range of length `N` — captures harmonic weight at
most `log N / (m · log m)`.  Taking `m` beyond `log N` drives this to `0`, so no choice of prime
subset escapes the window `log N ≪ K ≪ N`. -/
theorem sum_inv_le_of_prod_le {S : Finset ℕ} {m N : ℕ} (hm : 2 ≤ m) (hN : 0 < N)
    (hS : ∀ p ∈ S, m ≤ p) (hprod : ∏ p ∈ S, p ≤ N) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log N / ((m : ℝ) * Real.log m) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hcard := card_le_of_prod_le hm hN hS hprod
  have hterm : ∀ p ∈ S, (1 : ℝ) / p ≤ 1 / (m : ℝ) := by
    intro p hp
    have hpm : (m : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
    exact one_div_le_one_div_of_le hm0 hpm
  calc ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1 : ℝ) / (m : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / (m : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (Real.log N / Real.log m) / (m : ℝ) := by gcongr
    _ = Real.log N / ((m : ℝ) * Real.log m) := by rw [div_div]; ring_nf

/-- The refutation in the form it is used: the captured weight tends to `0` along any choice of
subsets whose smallest element grows faster than `log N`. -/
theorem sum_inv_lt_of_prod_le {S : Finset ℕ} {m N : ℕ} (hm : 2 ≤ m) (hN : 0 < N)
    (hS : ∀ p ∈ S, m ≤ p) (hprod : ∏ p ∈ S, p ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hgrow : Real.log N < ε * ((m : ℝ) * Real.log m)) :
    ∑ p ∈ S, (1 : ℝ) / p < ε := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < (m : ℝ) * Real.log m := by positivity
  refine lt_of_le_of_lt (sum_inv_le_of_prod_le hm hN hS hprod) ?_
  rw [div_lt_iff₀ hpos]
  exact hgrow

end NormalNumbers
