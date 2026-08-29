/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoExpSepProof

/-!
# Sharpening Tier-1: `β = 26` → single digits (batch-2 target 3)

Lane-2 batch-2 target 3 (operator brief v2).  `lnTwoExpSep_holds` gave
`∃ N₀, LnTwoExpSep 26 N₀` from deliberately crude constants; this file
sharpens the rate.  `lnTwoExpSep_holds`, its corollary, and the vendored
Legendre modules are LANDED — never edit or weaken them; copy-extend.

The two lossy spots (recorded in `LnTwoExpSepProof.lean`'s docstring):

1. **Coefficient height**: the crude bound took each Legendre coefficient
   `|c_k| = C(ℓ,k)·C(ℓ+k,ℓ) ≤ 8^ℓ` and summed to `(ℓ+1)·8^ℓ`.  Sharp:
   `Σ_k C(ℓ,k)·C(ℓ+k,ℓ) = P_ℓ(3)` (Legendre value at 3, the central
   Delannoy-type sum) `≤ (3+2√2)^ℓ ≈ 5.83^ℓ`; even the cheap
   `Σ ≤ 2^ℓ·C(2ℓ,ℓ) ≤ 8^ℓ` (no `(ℓ+1)` factor) helps.  The height of
   `Q` then improves from `(ℓ+1)·8^ℓ·lcm ℓ` accordingly.
2. **Zero-case remainder lower bound**: crude `(1/6)·(1/12)^ℓ` from the
   integrand on `[1/4, 1/2]`.  The kernel `y(1−y)/(1+y)` on `(0,1)` has
   maximum `3−2√2 ≈ 0.1716` (at `y = √2−1`), so an interval around the
   max gives a lower bound with base approaching `3−2√2 ≈ (1/5.83)`
   — vastly better than `1/12`, at the cost of an explicit
   sub-interval estimate.

Rebalance `ℓ = c·n` (`c` need not stay 4: the constraint is
`2ⁿ·lcm(ℓ)·(1/5)^ℓ → 0`, i.e. `c·log₂(5/4) > 1`, roughly `c > 3.11`;
smaller `c` shrinks every ℓ-exponent in β).  Track the final accounting
in the docstring like `LnTwoExpSepProof.lean` did.

⚠️ DRAFT STATEMENT — `β = 8` is a target guess; the lap may adjust the
numeral to what the honest sharp constants yield, in either direction,
as long as it is strictly below 26 (record the accounting); `N₀` free;
keep the theorem name.  Decomposing into named height/remainder lemmas
across laps is expected — leave a sharp HANDOFF between laps.
-/

namespace NormalNumbers

/-- **Tier-1, sharpened (DRAFT)**: exponential dyadic separation for
`ln 2` at a single-digit rate, via sharp Legendre coefficient and
remainder estimates. -/
theorem lnTwoExpSep_sharp : ∃ N₀ : ℕ, LnTwoExpSep 8 N₀ := by
  sorry

end NormalNumbers
