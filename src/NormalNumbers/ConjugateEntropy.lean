/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.QSpanNormal
import NormalNumbers.ConjugateDet
import Architect

/-!
# The entropy triangle on a Galois orbit

Quantitative form of `ConjugateDet`.  If `x + y + z` is rational (the three real conjugates of
a cubic algebraic number, or their `n`-th powers, or `σᵢ(β)` for any `β` in a totally real cubic
field: the trace is rational), the finite-state dimensions of `x, y, z` satisfy the triangle
inequalities:

* `fsDimUpper_le_of_sum_rat`: `Dim x ≤ Dim y + Dim z` (all upper).
* `fsDim_le_of_sum_rat`: `dim x ≤ dim y + Dim z` (one lower, one upper).
* `half_of_normal_of_sum_rat`: if one member is normal, another has `Dim ≥ 1/2`.  Proved from
  Wall (`isNormal_rat_mul_add`) and the span budget (`QSpan.span_dimension_budget`).
* `exists_sum_zero_normal_half`: the `1/2` is sharp for abstract triples (base 4, split each digit
  as `d = 2u + v`).  Whether actual conjugates can reach it is open; conjecturally every
  algebraic irrational is normal and all three dimensions are `1`.

So the dimension vector of a Galois orbit lies in the triangle cone, and the deterministic case
(`ConjugateDet.not_exactly_one_nondet`) is its zero face.

**Prior art (2026-10-05, Ren).**  The two-term inequalities are Bergelson–Downarowicz
arXiv:2506.12929v1 Prop. 4.9 for their lower/upper point entropies (upper case (d) is due to
Kamae), and §4.4 gives invariance under rational multiplication.  Two web searches found no
statement aimed at Galois conjugates.  The application is a corollary; its novelty is the
pointing, not the proof.  The bridge between B-D's point entropies and `fsDim`/`fsDimUpper` is
not formalized, so the first two statements carry their own English proofs in the
`span_dimension_budget` style rather than citing B-D.
-/

namespace NormalNumbers.ConjugateEntropy

open NormalNumbers.QSpan FiniteState
open scoped ENNReal

/-- **Upper triangle inequality.**  Confidence 85%.

English proof.  `x = q - y - z`.  A length-`ℓ` block of `x` at position `i` is determined by the
length-`ℓ` blocks of `y` and `z` at `i`, the digit block of `q` at `i` (eventually periodic, so
`O(1)` choices once `ℓ` exceeds the period) and the borrow into `i + ℓ` (at most three values).
So for every `N` the empirical block entropies satisfy `H_ℓ^N(x) ≤ H_ℓ^N(y) + H_ℓ^N(z) + O(1)`.
Take `limsup` in `N` (the `limsup` of a sum is at most the sum of the `limsup`s).  Each
`f(ℓ) = limsup_N H_ℓ^N / ℓ` is a limit in `ℓ` by Fekete (block entropy is subadditive up to the
non-stationarity of empirical laws, which vanishes as `N → ∞`), so the inequality passes to
`ℓ → ∞`.  Finish with the upper block-entropy characterization of `Dim_FS`
(Bourke–Hitchcock–Vinodchandran 2005; decompression form Doty–Moser 2006), as in
`span_dimension_budget`. -/
@[blueprint (title := "Finite-state dimension triangle on a rational-sum triple")]
theorem fsDimUpper_le_of_sum_rat (b : ℕ) (hb : 2 ≤ b) {x y z : ℝ} (q : ℚ)
    (hsum : x + y + z = q) :
    fsDimUpper (digitSeq b (by omega) x) ≤
      fsDimUpper (digitSeq b (by omega) y) + fsDimUpper (digitSeq b (by omega) z) := by
  sorry

/-- **Lower triangle inequality.**  Confidence 85%.  Same block inequality as
`fsDimUpper_le_of_sum_rat`; take `liminf` in `N` with the `z` term bounded by its `limsup`
(`liminf (a + c) ≤ liminf a + limsup c`), then `ℓ → ∞`.  Both lower on the right is false:
alternating sparse blocks of a normal number (`span_dimension_budget` docstring). -/
theorem fsDim_le_of_sum_rat (b : ℕ) (hb : 2 ≤ b) {x y z : ℝ} (q : ℚ)
    (hsum : x + y + z = q) :
    fsDim (digitSeq b (by omega) x) ≤
      fsDim (digitSeq b (by omega) y) + fsDimUpper (digitSeq b (by omega) z) := by
  sorry

/-- **A normal conjugate drags another up to dimension `1/2`.**  If `x + y + z` is rational and
`x` is normal, then `y + z` is normal (Wall), so the span budget gives
`1 ≤ dim y + Dim z`, and one of `Dim y, Dim z` is at least `1/2`. -/
@[blueprint (title := "A normal conjugate forces another to upper FS dimension at least 1/2")]
theorem half_of_normal_of_sum_rat (b : ℕ) (hb : 2 ≤ b) {x y z : ℝ} (q : ℚ)
    (hsum : x + y + z = q) (hx : IsNormal b x) :
    1 / 2 ≤ fsDimUpper (digitSeq b (by omega) y) ∨
      1 / 2 ≤ fsDimUpper (digitSeq b (by omega) z) := by
  have hyz : IsNormal b (((1 : ℚ) : ℝ) * y + ((1 : ℚ) : ℝ) * z) := by
    have h := isNormal_rat_mul_add b hb x (-1) q (by norm_num) hx
    have he : ((-1 : ℚ) : ℝ) * x + (q : ℝ) = ((1 : ℚ) : ℝ) * y + ((1 : ℚ) : ℝ) * z := by
      push_cast; linarith
    rwa [he] at h
  have h1 := span_dimension_budget b hb y z 1 1 hyz
  have h2 := h1.trans (add_le_add_left (fsDim_le_fsDimUpper (digitSeq b (by omega) y)) _)
  by_contra hc
  push Not at hc
  have := ENNReal.add_lt_add hc.1 hc.2
  rw [ENNReal.add_halves] at this
  exact absurd (h2.trans_lt this) (lt_irrefl _)

/-- **Sharpness sibling.**  Confidence 80%.

English construction.  Let `c` be normal in base 4 with digits `dᵢ = 2uᵢ + vᵢ`, `uᵢ, vᵢ ∈ {0,1}`.
Put `y = Σ 2uᵢ 4^{-i-1}`, `z = Σ vᵢ 4^{-i-1}` and `x = -c`, so `x + y + z = 0` with no carries.
`x` is normal (Wall).  Base-4 normality of `d` makes `u` and `v` normal binary sequences (a
length-`ℓ` block of `u` is a union of `2^ℓ` equally frequent `d`-blocks), so `y` and `z` have
block entropy `ℓ log 2` in base 4, i.e. finite-state dimension exactly `log 2 / log 4 = 1/2`,
lower and upper. -/
theorem exists_sum_zero_normal_half :
    ∃ x y z : ℝ, x + y + z = 0 ∧ IsNormal 4 x ∧
      fsDimUpper (digitSeq 4 (by omega) y) = 1 / 2 ∧
      fsDimUpper (digitSeq 4 (by omega) z) = 1 / 2 := by
  sorry

/-- **Why a currency must be weak: anything invariant under the maps that build a constant is
zero on it.**  Let `D` never increase under the maps in `𝓕`, vanish at `0`, and let `𝓕` contain
the constant map to `x`.  Then `D x = 0`.  Reading: take `𝓕` = computable maps and `D` =
effective (Kolmogorov) dimension, which respects `x ^ y`, `exp`, `x ^ k` and every other
computable operation.  Every computable real (`π`, `e`, `√2`, `φ`) then has `D = 0`, so that
currency cannot tell natural constants apart, and "one of these is complex" statements are
false in it.  Finite-state dimension escapes because constant maps to irrationals are not
finite-state, at the price of respecting only finite-state operations. -/
theorem invariant_vanishes_of_const_mem {D : ℝ → ℝ≥0∞} (𝓕 : Set (ℝ → ℝ))
    (hmono : ∀ f ∈ 𝓕, ∀ y, D (f y) ≤ D y) (h0 : D 0 = 0) {x : ℝ}
    (hx : (fun _ => x) ∈ 𝓕) : D x = 0 :=
  le_antisymm (by simpa [h0] using hmono _ hx 0) bot_le

end NormalNumbers.ConjugateEntropy
