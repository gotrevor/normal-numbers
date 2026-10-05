/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Computability.Partrec
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Computable reals: the computability axis of `docs/how-irregular-is-a-number.html`

Mathlib's `Computable` lives on `Primcodable` types, and `ℝ` is not one, so mathlib has no
computable-real predicate.  `IsComputableReal x` is Turing's notion in its dyadic form: a
computable `g : ℕ → ℤ` with `|x - g n / 2ⁿ| ≤ 2⁻ⁿ` for every `n`.  The dyadic form keeps every
approximant an integer, so the eventual proofs run on `ℕ`/`ℤ` combinators (`nat_mul`, `nat_rec`,
`list_foldl`) and never need rational arithmetic to be `Primrec` under `ℚ`'s renumbered encoding.

The one implication linking this axis to the arithmetic one is `isComputableReal_of_isAlgebraic`
(algebraic ⇒ computable), whose contrapositive `transcendental_of_not_isComputableReal`
(uncomputable ⇒ transcendental) is the doc table's row.

The randomness ladder's bottom rung enters as `IsKurtzRandom` (in no null `Π⁰₁` class), with
the ceiling theorem `not_isKurtzRandom_of_isComputableReal`: no computable real is even Kurtz
random.  It does not depend on `isComputableReal_of_isAlgebraic`; that one only supplies named
instances (`not_isKurtzRandom_of_isAlgebraic`).
-/

namespace NormalNumbers.ComputableReal

/-- `x` is a **computable real**: some computable `g : ℕ → ℤ` has `g n / 2ⁿ` within `2⁻ⁿ` of `x`
for every `n`. -/
def IsComputableReal (x : ℝ) : Prop :=
  ∃ g : ℕ → ℤ, Computable g ∧ ∀ n : ℕ, |x - (g n : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n

/-- Non-vacuity check on the definition's shape: `0` is computable, by the constant `0`. -/
theorem isComputableReal_zero : IsComputableReal 0 :=
  ⟨fun _ => 0, Computable.const 0, fun n => by simp⟩

/-- **Every algebraic real is computable.**

Believed, confidence 99%: a textbook result (Turing 1936 §10 lists the real algebraic numbers
among the computable numbers).  Not yet proved here; the obstacle is the `Primrec` bookkeeping,
not the mathematics.

English proof.  Let `p ∈ ℤ[X]` be the minimal polynomial of `x` over `ℚ` with denominators
cleared.  It is irreducible over a field of characteristic 0, so separable, so `x` is a simple
root and `p` changes sign at `x`.  Classically fix integers `a`, `k` with `x` the only root of
`p` in `[a/2ᵏ, (a+1)/2ᵏ]` and `p(a/2ᵏ)·p((a+1)/2ᵏ) < 0`; these need only exist, since they
are hard-coded into the program.  Bisect: at depth `n ≥ k` keep the dyadic half on which the
sign change persists.  The sign of `p` at `m/2ⁿ` is the sign of the integer `2^{n·deg p}·p(m/2ⁿ)`,
computed by splitting `p` into its positive and negative coefficient parts and comparing two
`ℕ`-valued polynomial evaluations (`list_foldl`); the bisection is a `nat_rec`.  The IVT
(`intermediate_value_Icc`) keeps a root in each kept interval, and uniqueness of the root in
`[a/2ᵏ, (a+1)/2ᵏ]` makes it `x`, so the left endpoint `gₙ/2ⁿ` is within `2⁻ⁿ` of `x`; for
`n < k` output `⌊2ⁿ·a/2ᵏ⌋`, a fixed finite table.

Flatter route (no recursion): with `s` the sign of `p` at the left end of the isolating interval,
a dyadic `d` in it satisfies `d ≤ x ↔ sign p(d) ∈ {s, 0}`, so `gₙ` is a bounded `nat_findGreatest`
over offsets.  Hard-code a shift `c` with `x + c > 0` and use the shifted polynomial so every test
is a `nat_le` between two `ℕ` evaluations; the only `ℤ` step left is the final `- c·2ⁿ`.  Mathlib
proves `Primrec` for `ℕ` arithmetic only (`nat_add`/`nat_sub`/`nat_mul`/`nat_le`/
`nat_findGreatest`), not for `ℤ`, so that last subtraction is the step that needs plumbing.

Evidence: the standard literature proof; no new mechanism.  Estimated 200-400 lines via the flat
route, 300-600 via bisection, mostly `Primrec` combinators. -/
theorem isComputableReal_of_isAlgebraic {x : ℝ} (hx : IsAlgebraic ℤ x) : IsComputableReal x := by
  sorry

/-- **Uncomputable ⇒ transcendental**: the contrapositive of `isComputableReal_of_isAlgebraic`. -/
theorem transcendental_of_not_isComputableReal {x : ℝ} (hx : ¬ IsComputableReal x) :
    Transcendental ℤ x :=
  fun ha => hx (isComputableReal_of_isAlgebraic ha)

open MeasureTheory

/-- `U` is **effectively open**: the union of a computable list of open dyadic intervals
`(a/2ᵏ, b/2ᵏ)` (empty when `a ≥ b`, so finitely many intervals and `∅` are covered). -/
def IsEffectivelyOpen (U : Set ℝ) : Prop :=
  ∃ f : ℕ → (ℤ × ℤ) × ℕ, Computable f ∧
    U = ⋃ n, Set.Ioo (((f n).1.1 : ℝ) / 2 ^ (f n).2) (((f n).1.2 : ℝ) / 2 ^ (f n).2)

/-- `x` is **Kurtz random** (weakly 1-random): `x` lies in no null `Π⁰₁` class, i.e. every
effectively open set whose complement is Lebesgue-null contains `x`.  Stated on `ℝ` with
`volume`; the usual Cantor-space form agrees on `[0,1]` via binary expansion. -/
def IsKurtzRandom (x : ℝ) : Prop :=
  ∀ U : Set ℝ, IsEffectivelyOpen U → volume Uᶜ = 0 → x ∈ U

/-- **No computable real is Kurtz random**, so absolute normality is the ceiling for computable
numbers (Champernowne, Becher–Figueira 2002).

Believed, confidence 97%: textbook (Downey–Hirschfeldt, *Algorithmic Randomness and Complexity*,
2010, §7.2; Kurtz 1981).  The 3% is faithfulness of the `ℝ`/dyadic encoding above, not the
mathematics.

English proof.  Take `g` from `IsComputableReal x`.  Then `{x} = ⋂ₙ [(gₙ-1)/2ⁿ, (gₙ+1)/2ⁿ]`, so
`U := {x}ᶜ` is the union over `n` of the two open rays outside the `n`-th closed interval.  List,
for each `(n, m)`, the intervals `((gₙ-1-2ᵐ)/2ⁿ, (gₙ-1)/2ⁿ)` and `((gₙ+1)/2ⁿ, (gₙ+1+2ᵐ)/2ⁿ)`;
over `m` they exhaust the two rays, and the list is a computable function of `(n, m, side)` via
`Nat.unpair`.  Their union is `{x}ᶜ`, effectively open,
with complement `{x}` of measure zero, and `x ∉ U`.

Evidence: the standard proof; no new mechanism.  Cost is `Primrec` bookkeeping for the
enumeration (`Nat.unpair`, `Bool` case split) plus a set-extensionality argument. -/
theorem not_isKurtzRandom_of_isComputableReal {x : ℝ} (hx : IsComputableReal x) :
    ¬ IsKurtzRandom x := by
  sorry

/-- **No algebraic real is Kurtz random** (e.g. `√2`): wiring of the two theorems above. -/
theorem not_isKurtzRandom_of_isAlgebraic {x : ℝ} (hx : IsAlgebraic ℤ x) : ¬ IsKurtzRandom x :=
  not_isKurtzRandom_of_isComputableReal (isComputableReal_of_isAlgebraic hx)

end NormalNumbers.ComputableReal
