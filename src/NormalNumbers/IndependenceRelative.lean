/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Independence-relative digit disjunctions

Ren, 2026-10-05, `/create`.  The two-track adder theorems
(`Adder.adder_sixfold_disjunction_universal`) hold for every pair not both rational: their carry
automaton *collapses* (every live component is a simple cycle).  Most families do not collapse.
A family that fails can still hold for every pair off finitely many rational lines: it is enough
that each non-cycle live component is **degenerate**, i.e. some combination `aX + bY` has an
eventually periodic digit stream on every path through it (`experiments/independence_relative.py`,
a product-with-carry-transducer phase check; known-answer controls in
`test_independence_relative.py`).  Of 3621 random base-3 families (three single-digit channels,
coefficients in `[-2, 2]`, seed 20261005), 1033 are of this kind and 131 have a witness line that
is not a channel direction (the rest restate "an irrational number has some digit").  The
universal engine certifies none of them.

This is the first place where the constants matter to the carry engine, and it is in the shape of
the `π + e` / `π e` theorem: for `(π, e)` the statement reads "a digit disjunction holds, **or**
`e − 2π` is rational", and both halves are open (`pi_e_disjunction`).

The cleanest member (hand-proved below in English, found by the probe):

> base 3: if `Y − 2X` is irrational, then `X` has the digit `2` infinitely often, or `Y` has `1`,
> or `Y − X` has `2`.

It fails on the line: `X` with digits in `{0, 1}` and `Y = 2X` satisfy all three avoidances
(`exists_counterexample_on_line`).  Read as Cantor-set arithmetic: if `a ∈ C₀₁`, `b ∈ C₀₂` and
`b − a ∈ C₀₁` (tails), then `b = 2a` up to a rational.
-/

namespace NormalNumbers.IndependenceRelative

open NormalNumbers

/-- Digit `d` occurs infinitely often in the base-`b` expansion of `x`. -/
def DigitIO (b : ℕ) (x : ℝ) (d : ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ OccursAt b x [d] n

/-- **The ternary line theorem.**  Confidence 90% (statement faithfulness to the hand proof;
the hand proof itself is short and checked against the automaton verdict).

English proof.  Suppose all three avoidances hold past some position.  Then the tails have
`xᵢ ∈ {0,1}`, `yᵢ = 2uᵢ` with `uᵢ ∈ {0,1}`.  Subtract digitwise: `eᵢ = 2uᵢ − xᵢ ∈ {−1,0,1,2}`,
and the digits of `Y − X` come from `eᵢ + cᵢ₊₁` with borrows `c ∈ {−1, 0}` flowing from deep to
shallow.  Avoiding the digit `2` forbids `(e, c) = (2, 0), (0, −1), (−1, 0)`.  So `c = 0` forces
`e ∈ {0,1}` and the next shallower borrow `0`; `c = −1` forces `e ∈ {−1, 1, 2}`, staying at `−1`
only on `e = −1`.  A `0` borrow therefore propagates to every shallower position.  If borrows are
eventually `−1`, then `e ≡ −1`, i.e. `x ≡ 1`, `u ≡ 0`, and `X, Y` are rational, so `Y − 2X` is
too.  Otherwise the borrow is `0` throughout the tail and `eᵢ ∈ {0,1}`, which forces `uᵢ = xᵢ`:
the tails of `Y` and `2X` agree with no carries, so `Y − 2X` is rational.  Contradiction. -/
theorem ternary_line (X Y : ℝ) (h : Irrational (Y - 2 * X)) :
    DigitIO 3 X 2 ∨ DigitIO 3 Y 1 ∨ DigitIO 3 (Y - X) 2 := by
  sorry

/-- **The line is a real obstruction.**  Confidence 90%.  Take `X = Σ 3^{-k!}` (digits in
`{0,1}`, irrational: not eventually periodic) and `Y = 2X` (digits in `{0,2}`, no carries).
Then `Y − X = X` has digits in `{0,1}`.  None of the three digits recurs. -/
theorem exists_counterexample_on_line :
    ∃ X Y : ℝ, Irrational X ∧ Irrational Y ∧ Y = 2 * X ∧
      ¬ DigitIO 3 X 2 ∧ ¬ DigitIO 3 Y 1 ∧ ¬ DigitIO 3 (Y - X) 2 := by
  sorry

/-- **The `π + e` shape.**  Either `e − 2π` is rational, or ternary `π` has infinitely many `2`s,
or ternary `e` has infinitely many `1`s, or ternary `e − π` has infinitely many `2`s.  Every
disjunct is open.  Proved from `ternary_line`. -/
theorem pi_e_disjunction :
    (∃ q : ℚ, Real.exp 1 - 2 * Real.pi = q) ∨
      DigitIO 3 Real.pi 2 ∨ DigitIO 3 (Real.exp 1) 1 ∨ DigitIO 3 (Real.exp 1 - Real.pi) 2 := by
  by_cases h : Irrational (Real.exp 1 - 2 * Real.pi)
  · exact Or.inr (ternary_line _ _ h)
  · left
    unfold Irrational at h
    push Not at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq.symm⟩

/-- `S` is a **relative product block** in base `g`: for every pair with `1, X, Y` linearly
independent over `ℚ`, some combination `aX + bY`, `(a, b) ∈ S`, has every digit infinitely
often.  The two-track, independence-relative analogue of `Adder.IsProductBlock` (C2's `{2, 11}`
is a single-track block). -/
def IsRelativeBlock (g : ℕ) (S : List (ℤ × ℤ)) : Prop :=
  ∀ X Y : ℝ, (∀ c₀ c₁ c₂ : ℚ, (c₁ : ℝ) * X + c₂ * Y = c₀ → c₁ = 0 ∧ c₂ = 0) →
    ∃ p ∈ S, ∀ d < g, DigitIO g ((p.1 : ℝ) * X + p.2 * Y) d

/-- **No small relative block in base 3.**  Confidence 65%.

Evidence (`independence_relative.py blocksearch`, 2026-10-05): every direction set with at most
four directions and coefficients in `[-2, 2]` (2500 sets), at most three with coefficients in
`[-3, 3]` (5984), and every pair with coefficients in `[-6, 6]` (7140) has an assignment of
avoided digits whose live automaton keeps a component not certified degenerate.  Negating a
direction complements digits, so all-nonpositive directions add nothing.  Why it is only 65%: a
live component is a set of real avoiding pairs, but "not certified degenerate" is a failure of a
sound, incomplete phase test with witness coefficients up to 3, not a proof of positive
dimension off every line.  Reading: product-block counterexamples are two-dimensional (X and Y
vary separately), and a relative certificate only discards one-dimensional failure loci. -/
theorem not_isRelativeBlock_small (S : List (ℤ × ℤ)) (hlen : S.length ≤ 4)
    (hco : ∀ p ∈ S, |p.1| ≤ 2 ∧ |p.2| ≤ 2) : ¬ IsRelativeBlock 3 S := by
  sorry

end NormalNumbers.IndependenceRelative
