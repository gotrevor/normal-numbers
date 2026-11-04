/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.BBPSpan
import NormalNumbers.Disjunctive
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# A quadratic-twisted, two-radix rigidity question

Read `../../../MAZE.md` and `docs/pi-routes/dual-radix.md`.
This is an exploratory conjecture, NOT an admitted proof campaign.  The naive
quadratic-norm test did not produce an integer contradiction.  No implication
from mere dense two-parameter orbits to a dense one-parameter orbit is assumed.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.DualRadix

open MasterConjectures

theorem independent_radix_powers (m n : ℕ) (hm : 0 < m) :
    (16 : ℕ) ^ m ≠ 9 ^ n := by
  intro h
  have hmod := congrArg (fun k : ℕ => k % 2) h
  simp [Nat.pow_mod, Nat.ne_of_gt hm] at hmod

/-- The paired arctangent expansion in base nine, scaled to sqrt(3)*pi. -/
noncomputable def ternaryKick (n : ℝ) : ℝ :=
  144 * n / ((4 * n - 3) * (4 * n - 1))

/-- Classical identity, recorded as an input (99% confidence).
Derivation: pair consecutive terms of atan(1/sqrt(3)) = pi/6 and multiply
by 6*sqrt(3).  This module does not claim its HasSum proof is completed. -/
def PiTernaryIdentity : Prop :=
  HasSum (fun n : ℕ => ternaryKick (n + 1) / (9 : ℝ) ^ (n + 1))
    (Real.sqrt 3 * Real.pi)

/-- Arithmetic data suggested by the binary BBP formula and PiTernaryIdentity.
The binary formula is already proved in PiBBPProof; packaging both formulas into
this class remains an explicit input here, not the research crux. -/
def PiDualData : Prop :=
  IsBBPTypeSeries 16 Real.pi ∧ IsBBPTypeSeries 9 (Real.sqrt 3 * Real.pi)

/-- Exploratory conjecture: two independent rational-kick descriptions, linked
by a quadratic twist, rule out simultaneous proper digit languages for x.
This asks about x in BOTH bases, not about sqrt(3)*x in base nine.  No transfer
of disjunctivity through multiplication by sqrt(3) is presumed.
Truth is plausible under the existing stronger BBP-normality expectation;
no proof mechanism or numerical probability of success is asserted. -/
@[blueprint (title := "Quadratic-twisted dual-radix rigidity (exploratory)")]
def QuadraticDualRadixRigidity : Prop :=
  ∀ x : ℝ, Irrational x → IsBBPTypeSeries 16 x →
    IsBBPTypeSeries 9 (Real.sqrt 3 * x) →
    IsDisjunctive 16 x ∨ IsDisjunctive 9 x

/-- Conditional transfer only.  The rigidity hypothesis is unproved. -/
theorem pi_disjunctive_of_dualRigidity
    (h : QuadraticDualRadixRigidity) (hdata : PiDualData) :
    IsDisjunctive 16 Real.pi ∨ IsDisjunctive 9 Real.pi :=
  h Real.pi irrational_pi hdata.1 hdata.2

/-- Rational approximants used in the exact norm preflight. -/
def binaryPartial (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n,
    (4 / (8 * (k : ℚ) + 1) - 2 / (8 * k + 4) -
      1 / (8 * k + 5) - 1 / (8 * k + 6)) / 16 ^ k

def ternaryPartial (m : ℕ) (coefficient : ℚ := 6) : ℚ :=
  coefficient * ∑ k ∈ Finset.range m,
    (1 / (4 * (k : ℚ) + 1) - 1 / (3 * (4 * k + 3))) / 9 ^ k

def rawNorm (n m : ℕ) : ℚ :=
  3 * binaryPartial n ^ 2 - ternaryPartial m ^ 2

def clearedNorm (n m : ℕ) : ℤ :=
  let a := binaryPartial n
  let b := ternaryPartial m
  3 * (a.num * b.den) ^ 2 - (b.num * a.den) ^ 2

/-- The quadratic conjugates explain the proposed norm, but give no word input. -/
theorem quadratic_norm_identity (a b : ℝ) :
    (Real.sqrt 3 * a - b) * (-Real.sqrt 3 * a - b) = b ^ 2 - 3 * a ^ 2 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc
    _ = b ^ 2 - (Real.sqrt 3) ^ 2 * a ^ 2 := by ring
    _ = _ := by rw [hs]

/-- Known-answer control: Pell approximants do retain a unit after denominator
clearing.  Small raw error alone does not decide the integer size. -/
theorem pell_unit_norm_identity (p q : ℚ) (hp : p ≠ 0)
    (h : p ^ 2 - 3 * q ^ 2 = 1) :
    3 * (q / p) ^ 2 - 1 = -(1 / p ^ 2) := by
  field_simp
  nlinarith

/-- Finite probe record, NOT a proved asymptotic theorem.  Exact Python rational
arithmetic checked these five pairs, including a deliberately wrong coefficient.
In particular, small raw norms did not become integers of absolute value <1. -/
def NormPreflight : Prop :=
  ∀ nm ∈ ([(2, 3), (4, 5), (8, 10), (16, 20), (32, 40)] : List (ℕ × ℕ)),
    0 < |rawNorm nm.1 nm.2| ∧ |rawNorm nm.1 nm.2| < 1 ∧
      1 < |clearedNorm nm.1 nm.2| ∧
      8 < 3 * binaryPartial nm.1 ^ 2 - ternaryPartial nm.2 5 ^ 2

/-- The reported integer sizes are also a frozen finite probe statement. -/
def NormBitLengthPreflight : Prop :=
  ∀ sample ∈ ([((2, 3), 55), ((4, 5), 126), ((8, 10), 298),
      ((16, 20), 630), ((32, 40), 1296)] : List ((ℕ × ℕ) × ℕ)),
    (clearedNorm sample.1.1 sample.1.2).natAbs.log2 + 1 = sample.2

/-- Full rational cancellation still leaves these nonunit numerators.
Finite exact-Python evidence; this proposition is not a kernel proof. -/
def ReducedNormPreflight : Prop :=
  ∀ sample ∈ ([((2, 3), 38), ((4, 5), 87), ((8, 10), 200),
      ((16, 20), 455), ((32, 40), 901)] : List ((ℕ × ℕ) × ℕ)),
    (rawNorm sample.1.1 sample.1.2).num.natAbs.log2 + 1 = sample.2

end NormalNumbers.PiDisjunctiveRoutes.DualRadix
