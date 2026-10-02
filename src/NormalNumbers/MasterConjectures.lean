/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwo
import NormalNumbers.PiBBP

/-!
# Normality's master conjectures as hypothesis `Prop`s (campaign launched 2026-10-02)

The Schanuel pattern from lean-formalizations, for normality: state the big believed conjectures
once, as named `Prop`s, and derive what follows from each.  Proposal:
`docs/proposal-normality-master-conjectures-2026-09-29.md`; kickoff:
`KICKOFF-2026-10-02-master-conjectures.md`.

* `BorelConjecture` (Borel 1950): every irrational algebraic real is normal in every base.
* `BaileyCrandallHypA` (Bailey–Crandall, *On the random character of fundamental constant
  expansions*, Experimental Math. 10 (2001), Hypothesis A, with Definitions 2.3 and 2.5).  Tier P
  for the wording, read from the paper on 2026-10-02.  Faithful-or-weaker: the attractor uses
  distance on the circle (the paper's `‖·‖`), which only makes the attractor alternative easier,
  and equidistribution is the repo's `Equidistributed` (all `[a, c) ⊆ [0, 1]`), which is the
  paper's Definition 2.3.

## Frozen statements (do not edit; prove them)

* `hypA_lnTwo`: Hypothesis A ⇒ `ln 2` normal in base 2 (Bailey–Crandall Thm 1.1, via the repo's
  reduction `LnTwo.lean`).
* `hypA_pi_base16`: Hypothesis A + the BBP formula ⇒ `π` normal in base 16.
* `borel_sqrt_two`: Borel ⇒ `√2` normal in base 2.

## Guard rule

**Content locator.**  `r_n = 1/n`, `b = 2` is `lnTwoOrbit`; there Hypothesis A's content is
exactly `Equidistributed lnTwoOrbit` (Maze "Hypothesis A as weaker": a restatement for `ln 2`).
The new content is the general form: one `Prop` with many consequences.

**Degenerate cases.**  `p = 0` would give `x ≡ 0`, a finite attractor; Bailey–Crandall exclude it
by `0 ≤ deg p`, here `p ≠ 0`.  `deg p ≥ deg q` is excluded (the perturbation must tend to `0`).
A rational `α = Σ r_n/bⁿ` is the finite-attractor branch (their Thm 2.10), so the disjunction is
load-bearing.  For Borel: rationals are excluded by `Irrational`, and `√2` is the first instance.
-/

namespace NormalNumbers.MasterConjectures

open Polynomial Filter

/-- Distance on the circle `ℝ/ℤ`: `‖x − w‖ = |(x − w) − round(x − w)|`. -/
noncomputable def circDist (x w : ℝ) : ℝ := |(x - w) - round (x - w)|

/-- The Bailey–Crandall orbit: `x₀ = 0`, `xₙ = (b·xₙ₋₁ + p(n)/q(n)) mod 1`. -/
noncomputable def bcOrbit (p q : ℤ[X]) (b : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract (b * bcOrbit p q b n
      + ((p.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) / ((q.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ))

/-- Bailey–Crandall Definition 2.5: `x` has a finite attractor `W` if for every `ε > 0` there is
`K` such that every `x_{K+k}` is within `ε` (on the circle) of some element of `W`. -/
def HasFiniteAttractor (x : ℕ → ℝ) : Prop :=
  ∃ W : Finset ℝ, W.Nonempty ∧ ∀ ε > 0, ∃ K : ℕ, ∀ k : ℕ, ∃ w ∈ W, circDist (x (K + k)) w < ε

/-- **Bailey–Crandall Hypothesis A.**  For `p, q ∈ ℤ[X]` with `p ≠ 0`, `deg p < deg q` and
`q(n) ≠ 0` for every positive integer `n`, and every base `b ≥ 2`, the orbit `bcOrbit p q b`
either has a finite attractor or is equidistributed.  Open (believed). -/
def BaileyCrandallHypA : Prop :=
  ∀ (p q : ℤ[X]) (b : ℕ), p ≠ 0 → p.natDegree < q.natDegree →
    (∀ n : ℕ, 1 ≤ n → q.eval (n : ℤ) ≠ 0) → 2 ≤ b →
      HasFiniteAttractor (bcOrbit p q b) ∨ Equidistributed (bcOrbit p q b)

/-- **Borel's conjecture (1950).**  Every irrational algebraic real is normal in every base.
Open (believed). -/
def BorelConjecture : Prop :=
  ∀ x : ℝ, Irrational x → IsAlgebraic ℚ x → ∀ b : ℕ, 2 ≤ b → IsNormal b x

/-- Hypothesis A gives the normality of `ln 2` in base 2 (Bailey–Crandall Thm 1.1). -/
theorem hypA_lnTwo (hA : BaileyCrandallHypA) : IsNormal 2 (Real.log 2) := by
  sorry

/-- Hypothesis A and the BBP formula give the normality of `π` in base 16. -/
theorem hypA_pi_base16 (hA : BaileyCrandallHypA) (hπ : PiBBP) : IsNormal 16 Real.pi := by
  sorry

/-- Borel's conjecture gives the normality of `√2` in base 2. -/
theorem borel_sqrt_two (hB : BorelConjecture) : IsNormal 2 (Real.sqrt 2) := by
  sorry

end NormalNumbers.MasterConjectures
