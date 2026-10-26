/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.PiBBP
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The backward BBP series

The real forward series is pi.  The rational formula also makes sense at
negative integers.  Its backward series appears to sum to ZERO in Q_2.
The infinite identity below is frozen with a paper argument, not a Lean proof.
The finite algebra and the telescoping controls are proved independently.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.BBPBackward

def kick (x : ℚ) : ℚ :=
  4 / (8*x+1) - 2 / (8*x+4) - 1 / (8*x+5) - 1 / (8*x+6)

def backwardPartial (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, (16 : ℚ)^(j+1) * kick (-(j+1 : ℚ))

theorem kick_cast (n : ℕ) : (kick n : ℝ) = bbpKick n := by
  simp [kick, bbpKick]

/-- The even denominators cancel: this expression has odd denominator at
every integer x.  This makes backward 2-adic convergence natural. -/
theorem kick_factored (x : ℚ) (h1 : 8*x+1 ≠ 0) (h2 : 2*x+1 ≠ 0)
    (h3 : 8*x+5 ≠ 0) (h4 : 4*x+3 ≠ 0) :
    kick x = (120*x^2+151*x+47) /
      ((8*x+1)*(2*x+1)*(8*x+5)*(4*x+3)) := by
  have h5 : 8*x+4 ≠ 0 := by intro h; apply h2; linarith
  have h6 : 8*x+6 ≠ 0 := by intro h; apply h4; linarith
  have h7 : 1+x*2 ≠ 0 := by intro h; apply h2; linarith
  unfold kick
  field_simp [h1, h2, h3, h4, h5, h6, h7]
  ring_nf
  field_simp [h7]
  <;> ring

/-- Clearing the denominators in the generating-function decomposition.
The derivative of the backward-series primitive is
8u/(1-2u+2u^2) + 8u/(1-2u^2). -/
@[blueprint (title := "Backward BBP generating function splits into two quadratic factors")]
theorem generating_identity (u : ℚ) :
    (16*u+16*u^2+32*u^3-64*u^6) *
        ((1-2*u+2*u^2)*(1-2*u^2)) =
      (8*u*(1-2*u^2)+8*u*(1-2*u+2*u^2)) * (1-16*u^8) := by
  ring

theorem backward_first : backwardPartial 1 = 256 / 21 := by
  norm_num [backwardPartial, kick, Finset.sum_range_succ]

theorem backward_second : backwardPartial 2 = 8192 / 231 := by
  norm_num [backwardPartial, kick, Finset.sum_range_succ]

theorem backward_third : backwardPartial 3 = 266272768 / 1514205 := by
  norm_num [backwardPartial, kick, Finset.sum_range_succ]

/-- The coefficient-5 control already breaks the first cancellation. -/
theorem changed_coefficient_first :
    (16 : ℚ) * (kick (-1) + 1 / (8*(-1)+1)) = 208 / 21 := by
  norm_num [kick]

/-- FROZEN (confidence 99%).  Exact probes: see the checked-in script and JSON.
Paper argument: in Q_2(i), i^2=-1, factor P(u)=1-2u+2u^2 as
(1-(1+i)u)(1-(1-i)u).  All logarithmic series below converge at u=1,
since |1+i|_2=|1-i|_2=2^(-1/2).  The generating identity gives the primitive
  2 log P(u) - 2 log(1-2u^2)
    + 2i (log(1-(1+i)u) - log(1-(1-i)u)).
At u=1 the arguments are 1, -1, -i, i; the 2-adic logarithm vanishes
on each, as they are roots of unity.  Grouping coefficients by blocks of
eight gives exactly 16^k * kick(-k).  Thus the sum is zero.
The missing Lean work is the convergent power-series/logarithm argument in
the ramified extension, NOT a connection to digit disjunctivity.
The changed-coefficient control has valuation 4 at all 256 probed cutoffs.
-/
@[blueprint (title := "Frozen: the backward BBP series sums to zero in the 2-adic field")]
theorem backward_hasSum_zero :
    HasSum (fun j : ℕ =>
      (((16 : ℚ)^(j+1) * kick (-(j+1 : ℚ)) : ℚ) : ℚ_[2])) 0 := by
  sorry

/-- Open stronger pattern, supported by all cutoffs 1 through 256 in the
exact probe.  Unlike the sum-zero identity, no paper proof is supplied here.
It would give a quantitative congruence, not a disjunctivity theorem. -/
@[blueprint (title := "Open: exact valuation of every backward BBP partial sum")]
def BackwardValuation : Prop :=
  ∀ N : ℕ, 0 < N →
    padicValRat 2 (backwardPartial N) = (4*N+4+padicValNat 2 N : ℕ)

/-- A rational telescoping kick; this control is independent of BBP. -/
def coboundary (F : ℤ → ℚ) (n : ℤ) : ℚ := F n - F (n+1) / 16

@[blueprint (title := "Backward telescoping controls retain the negative of the forward seed")]
theorem backward_coboundary (F : ℤ → ℚ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (16 : ℚ)^(j+1) * coboundary F (-(j+1 : ℤ))) =
      16^N * F (-(N : ℤ)) - F 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [coboundary, Nat.cast_add, Nat.cast_one]
    have he : -((N : ℤ)+1)+1 = -(N : ℤ) := by ring
    rw [he, pow_succ]
    ring

theorem forward_coboundary (F : ℤ → ℚ) (N : ℕ) :
    (∑ j ∈ Finset.range N, coboundary F j / (16 : ℚ)^j) =
      F 0 - F N / 16^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [coboundary, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    <;> ring

end NormalNumbers.PiDisjunctiveRoutes.BBPBackward
