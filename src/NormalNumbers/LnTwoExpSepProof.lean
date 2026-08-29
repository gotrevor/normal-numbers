/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# Tier-1 discharge: `LnTwoExpSep` via the shifted-Legendre package

Lane-2 target 4 (2026-08-29 operator brief; blueprint §5 item 6).  The
donor machinery is `~/src/collatz-moonshot` `CollatzMoonshot/FrontA/Legendre.lean`
(+ `Gelfond.lean` for `Nat.lcmUpto` bounds), same toolchain/mathlib pin
(v4.33.1) — vendor the needed files here with provenance headers (re-home
by copy, never axioms).  Its headline `legendre_log_two_small` gives, for
every `ℓ`, nonzero integers `P, Q` with
`|P + Q·log 2| ≤ lcmUpto ℓ · (1/5)^ℓ`.

## The two honest gaps (the real work)

1. **Coefficient height**: the donor deliberately proves no bound on
   `|Q|`; the ExpSep derivation needs `|Q| ≤ H ℓ` with `H` explicit
   (extract from `legendre_mobius_int_linear_form`'s construction —
   `Q` is `lcmUpto ℓ` times a bounded integer sum).
2. **The pairing argument**: from `‖2ⁿ·ln 2‖ = |2ⁿ·ln 2 − m|` small,
   the integer `P·2ⁿ + Q·m` satisfies
   `|P·2ⁿ + Q·m| ≤ |Q|·‖2ⁿ·ln 2‖ + 2ⁿ·|P + Q·log 2|`; the nonzero case
   gives the separation, and the zero case needs its own elementary
   handling (nonvanishing of the form + the height data).

⚠️ DRAFT STATEMENT — `β = 4` is a first guess above the Alladi–Robinson
rate `≈ 3.63`.  The lap may adjust `β` upward to any explicit numeral the
honest constants yield (record why), and picks `N₀` freely; keep the
name, keep `LnTwoExpSep` itself untouched (frozen in `LnTwoRuns.lean`).
Discharging this lights the run tower: `run_le_of_expSep` then caps every
zero/one run of binary `ln 2` at `βn + O(log n)`, unconditionally.
-/

namespace NormalNumbers

/-- **Tier-1 discharge (DRAFT)**: effective exponential dyadic separation
for `ln 2`, in-house via shifted-Legendre linear forms. -/
theorem lnTwoExpSep_holds : ∃ N₀ : ℕ, LnTwoExpSep 4 N₀ := by
  sorry

end NormalNumbers
