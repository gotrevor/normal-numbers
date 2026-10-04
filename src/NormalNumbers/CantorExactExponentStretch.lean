/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponent

/-!
# Stretch: exact exponent `μ₀` for every `μ₀ > 2`, in `K`, normal to every base prime to 3

`CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal` covers
`μ₀ > 2 + log₂ 3 ≈ 3.585`.  This file freezes the full range `μ₀ > 2` (Bugeaud's Theorem 7.21
range, `μ ≥ 2`, minus the endpoint, which is the literature control below).

## Why the main mechanism stops at `2 + log₂ 3`

The Borel–Cantelli bound counts `O(2^{F(m)})` numerators per denominator `q ≈ 3ᵐ` near the
support.  Where the window `(m, τm]` enters a forced run (`m ≈ a_{k+1}/(τ−1)`), only
`a_{k+1} − m` places are free (`CantorExactExponent.freeCount_window_le_of_run`), and the block
cost `3ᵐ 2^{−(τ−2)m}` does not decay for `τ ≤ 2 + log₂ 3` (kernel control
`CantorExactExponent.bcTerm_red_mu_three`).  The heuristic count (rationals equidistributed
against the coin measure) predicts a cost `q^{2−τ}` per dyadic block, summable for every `τ > 2`.

## Candidate mechanism (none known to the repo)

An effective count of rationals near the truncations `P/3^a` of Cantor points.  Best proved
input found: He–Liao, arXiv 2602.01307, Cor. 6.5 (local equidistribution of `A_Q(η)` against
the Cantor measure on balls of radius `≥ Q^{−β}`, `η ∈ [Q^{−α}, Q^{−1}]`, `α − 1 > 0` small and
not explicit), and He–Liao 2608.15686.  The Broderick–Fishman–Reich count and Bugeaud–Durand
conjecture (18) are open for `K`.  So the gap `1 + α < μ₀ ≤ 2 + log₂ 3` has no mechanism; the
end near `2` might follow from He–Liao after a transfer from the self-similar measure to the
forced-run measure (not checked).

Confidence 10%.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExactExponentStretch

open CantorLiouville CantorExactExponent Derandomize

namespace Literature

/-- **Weiss 2001** (B. Weiss, *Almost no points on a Cantor set are very well approximable*,
Proc. R. Soc. Lond. A 457 (2001) 949–952; Bugeaud 2012, Thm 7.16 states `v₁(ξ) = 1` for
`μ_K`-a.e. `ξ`, i.e. exponent `2`): for the Cantor measure (law of `pt (fun _ => true)` under fair
coins), almost every point is `τ`-approximable for no `τ > 2`.  Cited for the `μ₀ = 2` control
only. -/
def Weiss2001 : Prop :=
  ∀ᵐ ω ∂coins, ∀ τ : ℝ, 2 < τ → ¬ LiouvilleWith τ (pt (fun _ => true) ω)

/-- **Bugeaud 2008, Theorem 7.21 of the 2012 book** (Y. Bugeaud, *Diophantine approximation and
Cantor sets*, Math. Ann. 341 (2008) 677–684): "Let μ ≥ 2.  The middle third Cantor set K contains
uncountably many elements whose irrationality exponent is equal to μ."  Weakened to existence.
Cited as the pairwise intersection `K ∩ {μ(x) = μ}`; nothing here uses it. -/
def Bugeaud2008Thm721 : Prop :=
  ∀ μ : ℝ, 2 ≤ μ → ∃ x ∈ cantorSet, HasIrrExponent x μ

end Literature

/-- **Control at `μ₀ = 2`: the triple is literature.**  Confidence 90%.

English proof.  Weiss 2001 gives `¬ LiouvilleWith τ` for `τ > 2`, a.e.; Cassels 1959
(`CantorLiouvilleAll.Literature.Cassels1959`) gives normality to base 2 a.e., hence
irrationality, hence `LiouvilleWith 2` by Dirichlet (Mathlib:
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`), and `LiouvilleWith p` for `p < 2`
by `LiouvilleWith.mono`.  Intersect the two full-measure sets. -/
theorem exists_mem_cantorSet_irrExponent_two_of_literature (hW : Literature.Weiss2001)
    (hC : CantorLiouvilleAll.Literature.Cassels1959) :
    ∃ x ∈ cantorSet, HasIrrExponent x 2 ∧ IsNormal 2 x := by
  sorry

/-- **Stretch crux: the exponent upper bound for every `μ₀ > 2`.**  Confidence 15%.

English proof (heuristic only).  As `CantorExactExponent.ae_not_liouvilleWith`, with the trivial
numerator count replaced by an equidistribution count of rationals `p/q`, `q ≈ 3ᵐ`, near the
prefix rationals `P/3^{a_{k+1}}`: expected hits `≈ q^{1−τ}` per `q`, so `3^{m(2−τ)}` per block,
summable for `τ > 2`.  No proved count of this strength is known for `K` (see module doc). -/
theorem ae_not_liouvilleWith_all (μ₀ : ℚ) (hμ : 2 < μ₀) (τ : ℝ) (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  sorry

/-- **Stretch headline.**  For every rational `μ₀ > 2` a computable `x ∈ K` with irrationality
exponent exactly `μ₀`, normal to every base `b ≥ 2` with `3 ∤ b`, not normal to base 3.
Confidence 10%. -/
theorem exists_computable_mem_cantorSet_irrExponent_normal_all (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ¬ IsNormal 3 (cantorExpReal μ₀ e) := by
  sorry

end NormalNumbers.CantorExactExponentStretch
