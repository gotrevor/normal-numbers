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
conjecture (18) are open for `K`.

## He–Liao does not transfer (checked 2026-10-05)

`Literature.HeLiao2026Cor65` is the upper half of their Cor. 6.5, for cylinders of the Cantor
measure.  Conditioned on a prefix that ends where a free stretch starts, our coin measure is
exactly such a branch down to the next run start `b`, so the measure-level transfer itself is
fine.  It fails for two independent reasons:

* **Scale.**  The trivial count only fails in run-entering windows, `(τ−1)m ≤ b < τm` with
  `q ≈ 3ᵐ`.  There the point is `P/3^b` up to `3^{−E}`, and every other rational is at least
  `1/(q·3^b)` from `P/3^b` (`endpoint_sep`).  So the event lives below the cylinder scale
  `3^{−b}`, and no measure-level count sees it.  Thickening to `3^{−b}` costs `Q·η = 3^{2m−b}`
  per window, which is `≥ 1` for every `τ ≤ 3` (`thickening_cost_ge_one`).  A
  Bugeaud–Durand-strength *measure* count would therefore reach at best `μ₀ > 3`, not `μ₀ > 2`.
* **Range.**  Cor. 6.5's main term needs `η ≥ Q^{−α}` with `α − 1 > 0` small and not explicit.
  The thickened windows need `η = 3^{m−b} ≤ Q^{2−τ}`, so `α ≥ τ − 2`, which is greater than 1
  for every `τ > 3`.  The two regimes never overlap.

What would reopen it is a count of rationals near the *discrete* endpoints `P/3^b` at the
heuristic density `Q^{2−τ}`, uniformly over cylinders (`EndpointRationalCount`).  That is a
Broderick–Fishman–Reich-type count, open for `K`.  He–Liao 2608.15686 (the Bugeaud–Durand
formula for `τ` near 1) has the same small-`α` regime.

Confidence 10%.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExactExponentStretch

open CantorLiouville CantorExactExponent CantorExpGeneric Derandomize

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

/-- **He–Liao 2026, Corollary 6.5, upper half** (Y. He, L. Liao, *Jarník-type theorem for
self-similar sets*, arXiv 2602.01307, built on Bénard–He–Zhang and Khalil–Luethi): for the Cantor
measure there are `α > 1` and `β > 0` such that, for large `Q`, every cylinder `K_w` of length
`≥ Q^{−β}` and every `η ∈ [Q^{−α}, Q^{−1}]`,
`μ(K_w ∩ A_Q(η)) ≪ μ(K_w) · Q η`, where `A_Q(η) = {x : ‖qx‖ < η for some Q ≤ q < 2Q}`.
Their statement is two-sided and for balls; the ball case reduces to cylinders by the open set
condition (their proof of 6.5).  `α` and `β` are not explicit (`κ` of Bénard–He–Zhang).  Cited,
unused: it records why the transfer fails (module doc). -/
def HeLiao2026Cor65 : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    ∀ (n : ℕ) (w : ℕ → Bool), (Q : ℝ) ^ (-β) ≤ (3 : ℝ)⁻¹ ^ n →
    ∀ η : ℝ, (Q : ℝ) ^ (-α) ≤ η → η ≤ (Q : ℝ)⁻¹ →
      coins.real {ω | (∀ i < n, ω i = w i) ∧ ∃ q : ℕ, Q ≤ q ∧ q < 2 * Q ∧
          ∃ p : ℤ, |(q : ℝ) * pt (fun _ => true) ω - p| < η} ≤
        C * Q * η * coins.real {ω | ∀ i < n, ω i = w i}

end Literature

/-- **Endpoint separation.**  A rational `p/q` other than `P/3^b` is at least `1/(q·3^b)` from
it.  So in a run-entering window (`q^{−τ} < 3^{−b}/q`), only the endpoint's own triadic
rationals are within `q^{−τ}`, and the stretch event is a question about the discrete endpoints
`P/3^b`, below the cylinder scale. -/
theorem endpoint_sep (P b q : ℕ) (p : ℤ) (hq : 0 < q)
    (hne : (p : ℝ) / q ≠ (P : ℝ) / 3 ^ b) :
    1 / ((q : ℝ) * 3 ^ b) ≤ |(P : ℝ) / 3 ^ b - p / q| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ b := by positivity
  have key : (P : ℝ) / 3 ^ b - p / q = (((P : ℤ) * q - p * 3 ^ b : ℤ) : ℝ) / ((q : ℝ) * 3 ^ b) := by
    push_cast
    field_simp
  have hz : (P : ℤ) * q - p * 3 ^ b ≠ 0 := by
    intro h
    apply hne
    have h' : ((P : ℤ) * q : ℝ) = (p * 3 ^ b : ℤ) := by
      exact_mod_cast sub_eq_zero.mp h
    push_cast at h'
    rw [div_eq_div_iff hq'.ne' h3.ne']
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * 3 ^ b)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (1 : ℤ) ≤ |(P : ℤ) * q - p * 3 ^ b| := Int.one_le_abs hz
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- **Thickening cost.**  Pushing the endpoint event up to the cylinder scale `3^{−b}` costs
`Q·η = 3^{2m−b}` in a window with `(τ−1)m ≤ b`; at the window's first denominator scale
(`b ≤ (τ−1)m`) this is `≥ 1` whenever `τ ≤ 3`.  So a measure-level count, even of
Bugeaud–Durand strength, cannot certify `μ₀ ≤ 3`. -/
theorem thickening_cost_ge_one (τ : ℝ) (hτ : τ ≤ 3) (m b : ℕ) (hb : (b : ℝ) ≤ (τ - 1) * m) :
    1 ≤ (3 : ℝ) ^ (2 * m) / 3 ^ b := by
  have hbm : b ≤ 2 * m := by
    have h2 : (τ - 1) * (m : ℝ) ≤ 2 * m :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg m)
    exact_mod_cast hb.trans h2
  rw [le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_right₀ (by norm_num) hbm

/-- **Reopen condition for the He–Liao wall** (`Maze`: "He–Liao local count on the forced-run
measure").  Rationals `p/q`, `q ∈ [3ᵐ, 2·3ᵐ)`, within `q^{−τ}` of the depth-`b` Cantor endpoint
`P/3^b` (other than `P/3^b` itself) have conditional probability `O(Q^{2−τ})` on every cylinder
of depth `a ≤ 2m`: the heuristic density (per endpoint, `Σ_q 2q^{1−τ}`).  A statement, not a
belief: a Broderick–Fishman–Reich-type count on the discrete endpoints.  That it suffices for
`ae_not_liouvilleWith_all` is believed, not checked (60%). -/
def EndpointRationalCount : Prop :=
  ∀ τ : ℝ, 2 < τ → ∃ C : ℝ, ∀ (a b m : ℕ) (w : ℕ → Bool), a ≤ b → a ≤ 2 * m →
    (b : ℝ) < τ * m →
    coins.real {ω | (∀ i < a, ω i = w i) ∧ ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 2 * 3 ^ m ∧ ∃ p : ℤ,
        (p : ℝ) / q ≠ (hd (fun _ => true) ω b : ℝ) / 3 ^ b ∧
        |(hd (fun _ => true) ω b : ℝ) / 3 ^ b - p / q| < (q : ℝ) ^ (-τ)} ≤
      C * (3 : ℝ) ^ ((2 - τ) * m) * coins.real {ω | ∀ i < a, ω i = w i}

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
