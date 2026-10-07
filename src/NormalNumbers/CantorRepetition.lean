/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentProfile

/-!
# Is the profile cut forced?  Repetitions instead of zero runs

Ren, 2026-10-06 (`/create`, after the profile theorem).  In
`CantorExactExponentProfile`, a point of `K` whose exponent comes from forced **zero runs**
(approximations `P/3^a`) is normal to `3ˢt` only when `t > 3^{s(μ₀−1)}`.  In particular no
Cantor–Liouville point of the repo is normal to base 6 (`CantorLiouvilleAll.not_isNormal_six`).
Cassels–Schmidt-typical points of `K` are normal to every base that is not a power of 3, but
their exponent is 2.

**Question: is the cut a property of the exponent, or of zero runs?**  The approximations made
by zero runs have denominators divisible by `3^a`, and that divisibility is what produces the
base-`3ˢt` zero runs.  A **repetition** gives approximations with denominators *prime to 3*.
Take a free block `W` of length `ℓ` and copy it `M` times: then `x ≈ W/(3^ℓ − 1)` to within
`3^{−Mℓ}`, and `3^ℓ − 1` is prime to 3.  The digits stay in `{0, 2}`, so `x ∈ K`.  With `M → ∞`,
`x` is Liouville.

**Conjecture (frozen).**  There is a Liouville number in `K` that is normal to every base that is
not a power of 3 (`LiouvilleCantorFullProfile`); in particular one normal to base 6.  More
strongly, for every rational `μ₀ > 2` there is such a point with exponent exactly `μ₀`
(`ExponentCantorFullProfile`).  The profile cut would then belong to the zero-run construction,
not to the exponent.

**Why the zero-run obstruction is absent.**  In base `b = 3ˢt`, `bʲ·W/(3^ℓ − 1)` is never close
to an integer unless `3^ℓ − 1` divides it.  `gcd(b, 3^ℓ − 1)` divides `t`, so the base-`b`
expansion of the approximant is periodic with period `ord(b mod (3^ℓ−1)/gcd)`, typically
`≍ 3^ℓ`, which is far longer than the agreement window.  No forced base-`b` block appears.

**Why normality is plausible (mechanism).**  The copies are not free coins, but the law of `x`
is still a product over the free coins.  Coin `i` enters with the weight
`w_i = 2·Σ_c 3^{−(i+cℓ)−1}`, so `𝔼 e(ξx) = Π_i (1 + e(ξ w_i))/2`, and a Cassels second moment
needs `‖ξ w_i‖` to stay away from 0 on many coins.  For a frequency `ξ = h bⁿ` whose ternary
window lies in a copy region, the copy at `i + cℓ` plays the role of a free place.

**Known-false sibling.**  The same copies with base `b = 9` must fail, since base-9 digits of a
`{0,2}`-ternary point lie in `{0,2,6,8}`.  Any proof must use `t > 1` somewhere (in the
digit-change counting, as `CantorLiouvilleAll.secondMoment_le_b` uses `3 ∤ b`).

**What is hard.**  The Liouville version needs only the lower bound on the exponent, so the
whole difficulty is normality with copied digits (the fraction of copied digits tends to 1 along
the repetitions).  The exact-exponent version also needs an upper bound.  The approximants
`p/(3^ℓ−1)` are prime to 3, so the 3-adic count `hit_mass_padic` does not apply, and a new
count is needed.
-/

open MeasureTheory Filter

namespace NormalNumbers.CantorRepetition

/-- **A Liouville number in `K` with the full Cassels–Schmidt profile.**  Normal to `b` exactly
when `b` is not a power of 3.  Confidence 60%. -/
def LiouvilleCantorFullProfile : Prop :=
  ∃ x ∈ cantorSet, Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ∀ s : ℕ, b ≠ 3 ^ s)

/-- **Exact exponent `μ₀` in `K` with the full profile.**  Confidence 40% (the exponent upper
bound for repetition approximants is a new count). -/
def ExponentCantorFullProfile (μ₀ : ℚ) : Prop :=
  ∃ x ∈ cantorSet, CantorExactExponent.HasIrrExponent x μ₀ ∧
    ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ∀ s : ℕ, b ≠ 3 ^ s)

/-- **The cut is not forced (Liouville case).**  Open node; see the module doc for the mechanism. -/
theorem liouvilleCantorFullProfile : LiouvilleCantorFullProfile := by
  sorry

end NormalNumbers.CantorRepetition
