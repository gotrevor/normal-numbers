/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableReal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Kurtz randomness: the bottom rung of the randomness ladder

`IsKurtzRandom x` says `x` lies in no null `Π⁰₁` class.  The ceiling theorem
`not_isKurtzRandom_of_isComputableReal` says no computable real is even Kurtz random, so absolute
normality is the most a computable number reaches.  It does not depend on
`isComputableReal_of_isAlgebraic`; that one only supplies named instances
(`not_isKurtzRandom_of_isAlgebraic`).
-/

namespace NormalNumbers.ComputableReal

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
