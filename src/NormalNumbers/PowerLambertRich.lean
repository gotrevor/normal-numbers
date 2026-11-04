/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertNonNormal
import NormalNumbers.CastingOut

/-!
# Perfect-power Lambert constants are rich (every word has positive lower frequency)

`S_{b,r} = Σ_{n≥1} 1/(b^{n^r} − 1)`, `r ≥ 2`, is disjunctive (`isDisjunctive_powerLambert`) and not
normal (`not_isNormal_powerLambert`) in base `b`.  This file freezes the rung in between:
**richness** (`NormalNumbers.CastingOut.IsRich`): every base-`b` word occurs at a set of positions
of positive lower density.

## Mechanism (paper, 2026-11-03, Ren)

Write `S_{b,r} = q + Y` with `q` rational and `Y = coefficientValue c b`,
`c m = #{d > 8 : d^r ∣ m}` (`exists_rat_powerLambert_tail`).  The orbit is
`{b^n S} = {b^n q + Σ_{j≥1} c(n+j) b^{−j}}`, and `b^n q mod 1` is periodic in `n` with period
`T = lcm(1..8)^r` (each `1/(b^m − 1)` has period `m`).

1. **Witness with guard digits.**  For a word `w` of length `L`, disjunctivity gives a position
   `n₁` at which the longer word `w ++ [1] ++ replicate m 0` occurs, so `{b^{n₁} S}` lies in the
   `w`-cylinder with two-sided margin `δ := b^{−(L+1)} − b^{−(L+1+m)} > 0`.
2. **Freeze the small structure.**  Choose `J₀` with `Σ_{j>J₀} c(n₁+j) b^{−j} (1 + C_r) < δ/8`
   (the sum converges since `c m ≤ m`), then `D ≥ 8` larger than every `d` with `d^r ∣ n₁ + j`,
   `j ≤ J₀`.  Put `Q := (lcm(1..D))^{2r}` (a multiple of `T`).
3. **The shifted class.**  For `n = n₁ + kQ`, `k ≥ 0`: `{b^n q} = {b^{n₁} q}`, and the coefficients
   split as `c = c_Q + c_⊥`, where `c_Q m := #{d > 8 : d^r ∣ Q ∧ d^r ∣ m}` is `Q`-periodic, so
   `c_Q(n+j) = c_Q(n₁+j)` for all `j`.  Hence
   `|{b^n S} − {b^{n₁} S}| ≤ Σ_j c_⊥(n+j) b^{−j} + Σ_j c_⊥(n₁+j) b^{−j}` (mod-1 distance), and the
   second sum is `< δ/8` by the choice of `D` (for `j ≤ J₀`, `c_⊥(n₁+j) = 0`).
4. **Averaging over `k`.**  For `j ≤ J₀`: `d^r ∣ n₁ + kQ + j` with `d^r ∤ Q` forces a prime power
   `p^a ∥ d` with `p^a > D`; if `p ≤ D` the congruence is incompatible with the valuation of
   `n₁ + j` (which is `< 2⌊log_p D⌋ r`), and if `p > D` it has density `≤ 1/p^r` in `k`.  So
   `avg_{k<K} c_⊥(n₁+kQ+j) ≤ a_r(n₁+j) · Σ_{p>D} p^{−r} + o(1)`.  For `j > J₀` use the crude
   `avg_{k<K} c(n₁+kQ+j) ≤ (1 + C_r) a_r(n₁+j) + o(1)` with `C_r = Σ_p p^{−r}/(1 − p^{−r})`.
   The `o(1)` terms are the `+1` errors of counting `k < K` with `d^r ∣ n₁+kQ+j`, summed over
   `d ≤ (KQ + J)^{1/r}`: `O((KQ)^{1/r}) = o(K)` because `r ≥ 2`.  (For `r = 1` this fails, which
   is where `E_b` differs.)
5. **Markov.**  Hence for `K` large, at least `K/2` of the `k < K` have
   `Σ_j c_⊥(n₁+kQ+j) b^{−j} < δ/2`, and each such `n = n₁ + kQ` is an occurrence of `w`.  So the
   occurrence count below `N` is `≥ (N − n₁)/(2Q) − O(1)`: lower density `≥ 1/(4Q) > 0`.

The constant `1/(4Q)` depends on `w` through `n₁`, `J₀`, `D` — exactly what `IsRich` allows.

## Status

`isRich_powerLambert` is the frozen headline (sorry, confidence 92%).  Its statement must not be
weakened or restated; split it into named lemmas instead.  `powerLambert_rich_not_normal` is the
rung summary and needs no further proof once the headline lands.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open NormalNumbers.CastingOut

/-- **Headline (frozen, 2026-11-03).**  Every finite base-`b` word occurs in the expansion of
`Σ_{n≥1} 1/(b^{n^r} − 1)`, `r ≥ 2`, at a set of positions of positive lower density.
Confidence 92%; mechanism in the module docstring (shifted residue class `n₁ + kQ` with
`Q = lcm(1..D)^{2r}` reproduces the witness's small-divisor structure; the non-periodic divisor
mass averages to `o(1)` because `r ≥ 2`). -/
@[blueprint (title := "Perfect-power Lambert constants are rich")]
theorem isRich_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) := by
  sorry

/-- The rung between disjunctive and normal, inhabited by an explicit arithmetic family:
rich (every word has positive lower frequency) and nonnormal (frequencies are not uniform). -/
@[blueprint (title := "Perfect-power Lambert constants are rich and nonnormal")]
theorem powerLambert_rich_not_normal (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) ∧ ¬ IsNormal b (powerLambert b r) :=
  ⟨isRich_powerLambert b r hb hr, not_isNormal_powerLambert b r hb hr⟩

end NormalNumbers.ArithmeticDisjunctivity
