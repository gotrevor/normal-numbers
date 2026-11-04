/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertFrequencies
import NormalNumbers.PowerLambertRich
import NormalNumbers.PowerLambertNearZero

/-!
# Every word frequency of a perfect-power Lambert constant exists

Gate file of `KICKOFF-2026-11-04-power-lambert-frequencies.md`.  Both theorems are FROZEN.

`S = powerLambert b r = Σ_{n≥1} 1/(b^{n^r} − 1) = Σ_m c(m) b^{−m}` with `c = powerDivisorCount r`
(`c(m) ≥ 1` for `m ≥ 1`, mean `ζ(r) < 2`).  The base-`b` orbit is `u_n = {b^n S} = {T_n}`,
`T_n = Σ_{j≥1} c(n+j) b^{−j}`.

* `powerLambert_nearZero_density`: the orbit has vanishing upper density near `0`, i.e. long
  constant runs (of `0` or of `b − 1`) have density `→ 0` in the run length.  Mechanism: a run of
  length `L` ending at `n + L` forces the window sum `Σ_{m=n+1}^{n+L} c(m)` to be at least
  `(b−1)(L−1) − ⌊T_{n+L}⌋` (carry chain), while window sums are rigid, `≤ L + (11/12) L + √L +`
  (roots `d > √L`), and the big-root count and `⌊T⌋` are `O(√L)` and `O(1)` on average.
* `powerLambertFrequenciesExist`: every word frequency exists.  Near-zero density transports to
  every `b`-adic rational (`u_{n+L} = {b^L u_n}`); the `Q_D`-periodic approximant
  `{periodicTail}` is within `aperiodicTail ≥ 0` of `u_n`, with mean `≤ 2/(D+1)`; so the word
  counts are Cauchy.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

open Classical in
/-- **Frozen (2026-11-04).**  The orbit of `Σ_{n≥1} 1/(b^{n^r} − 1)` has vanishing upper density
near `0`: for every `ε > 0` there is a run length `L` such that, eventually in `N`, fewer than
`ε N` of the positions `n < N` start a run of `L` zeros or of `L` digits `b − 1`. -/
theorem powerLambert_nearZero_density (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ᶠ N : ℕ in atTop,
      (((range N).filter fun n =>
        orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L ∨
          1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n).card : ℝ) ≤ ε * N :=
  powerLambert_nearZero_density_aux b r hb hr

/-- **Headline (frozen, 2026-11-04).**  For `b, r ≥ 2`, every base-`b` word has a limiting
frequency in the expansion of `Σ_{n≥1} 1/(b^{n^r} − 1)`: the first explicit arithmetic constant
with a complete (non-uniform: `not_isNormal_powerLambert`) word-frequency law. -/
@[blueprint (title := "Perfect-power Lambert constants have a word-frequency law")]
theorem powerLambertFrequenciesExist (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    PowerLambertFrequenciesExist b r := by
  sorry

end NormalNumbers.ArithmeticDisjunctivity
