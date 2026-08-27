/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.UniformTV

/-!
# Diagonal rigidity: an open question

Reading `b` digits of `x` in base `b` — the number of digits tied to the size of the
alphabet — and asking the histogram to be flat is **not** a weak form of normality.  It is a
rigidity that random reals fail, and whether *any* real satisfies it is open as far as we know.

## Where the question came from

`UniformTV` asks that base-`b` digit histograms flatten as `b → ∞`, over windows that outgrow
the base (`N ≥ L * b`).  That implies absolute normality
(`isAbsolutelyNormal_of_uniformDigitTV`).  The `L * b` floor is not decoration: with only `N`
samples in `b` cells the typical total variation is of order `√(b / N)`, so the depth must
outrun the base for flatness to be achievable at all.

This file asks what happens at the forbidden diagonal `N = b`, one digit per cell on average.

## Why it is a rigidity, not a weak normality

`digitTV_diag_eq` computes the diagonal exactly:
`digitTV b x b = (∑ c, |mᶜ - 1|) / (2 * b)`, where `mᶜ` counts occurrences of the digit `c`
among the first `b` base-`b` digits.  So `digitTV b x b → 0` says precisely that the first `b`
base-`b` digits are a **permutation of `{0, …, b-1}` up to `o b` defects**.

That is *stronger* than randomness, not weaker.  Throw `b` balls into `b` bins and about `b / e`
bins stay empty, which alone pins the diagonal total variation near `1 / (2 * e)`.  A
uniformly random real therefore fails `DiagonallyRigid` badly, and the set of such reals is
null.  Being normal neither implies nor is implied by it: the two conditions are orthogonal.

## The question

`DiagonalRigidityQuestion` is deliberately a `Prop`-valued definition and **not** a theorem with
a `sorry`.  A `sorry` would assert that the answer is *yes*; nobody knows the answer, and an
artifact should not smuggle in a claim it cannot support.  Neither direction is proved here.

Intuition is genuinely absent.  The constraints for consecutive bases `b` and `b + 1` are
imposed at nearly the same precision — a base-`b` window of `b` digits pins `x` to about
`b * log b` bits — so they interlock tightly rather than acting independently, which is exactly
why a naive counting heuristic settles nothing.
-/

namespace NormalNumbers

open Filter

/-- **Diagonal rigidity.**  Reading exactly `b` digits in base `b`, the digit histogram
flattens as `b → ∞`.  Equivalently (`digitTV_diag_eq`), the first `b` base-`b` digits of `x`
form a permutation of `{0, …, b-1}` up to `o b` defects. -/
def DiagonallyRigid (x : ℝ) : Prop :=
  Tendsto (fun b : ℕ => digitTV b x b) atTop (nhds 0)

/-- **OPEN.**  Does any real number satisfy `DiagonallyRigid`?

Not a theorem, and not a `sorry`: neither direction is known to us.  A proof of this `Prop`
exhibits a witness; a proof of its negation shows the diagonal constraint is unsatisfiable for
every real. -/
def DiagonalRigidityQuestion : Prop := ∃ x : ℝ, DiagonallyRigid x

/-- The strictly stronger, defect-free variant: the first `b` base-`b` digits are *exactly* a
permutation of `{0, …, b-1}` for all large `b`.  `ExactlyDiagonallyRigid x → DiagonallyRigid x`
(`diagonallyRigid_of_exact`), so a negative answer here is weaker news than a negative answer
above. -/
def ExactlyDiagonallyRigid (x : ℝ) : Prop :=
  ∀ᶠ b : ℕ in atTop, ∀ c < b, digitOccCount b x b c = 1

/-- Missing digit values are the cheap obstruction: a digit value absent from the first `b`
base-`b` digits contributes a full `1` to the defect sum, so a real using few distinct values in
base `b` is bounded away from diagonal flatness.  This is what kills every "obvious" candidate,
rationals included — an eventually periodic expansion uses boundedly many values, while the
alphabet grows without bound. -/
theorem digitTV_diag_ge_missing (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    ((((Finset.range b).filter fun c => digitOccCount b x b c = 0).card : ℝ)) / (2 * b)
      ≤ digitTV b x b := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have h1 : (0 : ℕ) < b := lt_of_lt_of_le (by norm_num) hb
    exact_mod_cast h1
  have key : ((((Finset.range b).filter fun c => digitOccCount b x b c = 0).card : ℝ))
      ≤ ∑ c ∈ Finset.range b, |(digitOccCount b x b c : ℝ) - 1| := by
    have hsub : ((Finset.range b).filter fun c => digitOccCount b x b c = 0)
        ⊆ Finset.range b := Finset.filter_subset _ _
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => abs_nonneg ((digitOccCount b x b i : ℝ) - 1))
    refine le_trans (le_of_eq ?_) hmono
    rw [Finset.sum_congr rfl (fun c hc => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    have : digitOccCount b x b c = 0 := (Finset.mem_filter.mp hc).2
    rw [this]
    norm_num
  rw [digitTV_diag_eq b hb x]
  gcongr

/-- `ExactlyDiagonallyRigid` is the stronger condition: an exact permutation has zero defect,
so the diagonal total variation is not merely small but identically `0` for all large `b`. -/
theorem diagonallyRigid_of_exact (x : ℝ) (h : ExactlyDiagonallyRigid x) :
    DiagonallyRigid x := by
  have hzero : (fun b : ℕ => digitTV b x b) =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [h] with b hb
    unfold digitTV
    rw [Finset.sum_eq_zero, zero_div]
    intro c hc
    rw [hb c (Finset.mem_range.mp hc)]
    simp
  exact Tendsto.congr' hzero.symm tendsto_const_nhds

end NormalNumbers
