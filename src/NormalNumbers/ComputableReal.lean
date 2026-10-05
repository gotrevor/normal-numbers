/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Computability.Partrec
import NormalNumbers.ComputableAlgebraic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

The randomness ladder's bottom rung (`IsKurtzRandom`) lives in `NormalNumbers.KurtzRandom`.
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

A textbook result (Turing 1936 §10 lists the real algebraic numbers among the computable
numbers), proved here by the flat route below; the leaf lemmas are in
`NormalNumbers.ComputableAlgebraic`.  The proof uses `x` as a simple root of the
`(r-1)`-st derivative of an annihilating polynomial (`r` the root multiplicity) rather than
the minimal polynomial, and local strict monotonicity in place of the IVT.

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
  obtain ⟨q, hroot, hder⟩ := ComputableAlgebraic.exists_simple_root hx
  obtain ⟨c, hc⟩ := exists_nat_ge (-x)
  obtain ⟨hroot', hder'⟩ := ComputableAlgebraic.exists_shifted_root q c hroot hder
  obtain ⟨F, hF, hFeq⟩ := ComputableAlgebraic.exists_primrec_floor _ (by linarith) hroot' hder'
  refine ⟨fun n => (F n : ℤ) - (c * 2 ^ n : ℕ),
    (ComputableAlgebraic.primrec_int_sub hF
      (Primrec.nat_mul.comp (Primrec.const c) ComputableAlgebraic.primrec_two_pow)).to_comp,
    fun n => ?_⟩
  have hpn : (0 : ℝ) < 2 ^ n := by positivity
  have hy : 0 ≤ 2 ^ n * (x + c) := mul_nonneg hpn.le (by linarith)
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one (2 ^ n * (x + c))
  show |x - (((F n : ℤ) - ((c * 2 ^ n : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n
  rw [hFeq]
  push_cast
  rw [show x - ((⌊2 ^ n * (x + c)⌋₊ : ℝ) - c * 2 ^ n) / 2 ^ n =
      (2 ^ n * (x + c) - ⌊2 ^ n * (x + c)⌋₊) / 2 ^ n by field_simp; ring,
    abs_div, abs_of_pos hpn, div_le_div_iff_of_pos_right hpn, abs_le]
  constructor <;> linarith

/-- **Uncomputable ⇒ transcendental**: the contrapositive of `isComputableReal_of_isAlgebraic`. -/
theorem transcendental_of_not_isComputableReal {x : ℝ} (hx : ¬ IsComputableReal x) :
    Transcendental ℤ x :=
  fun ha => hx (isComputableReal_of_isAlgebraic ha)

end NormalNumbers.ComputableReal
