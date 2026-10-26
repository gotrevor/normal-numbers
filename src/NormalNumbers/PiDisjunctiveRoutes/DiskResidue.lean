/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive

/-!
# Route 3: integer disk residues

Route 3 of three experimental routes to disjunctivity of π.
See `NormalNumbers.PiDisjunctiveRoutes` for the shared framing and evidence tiers.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- Integer disk count, including the origin, axes, and boundary.
The positive quadrant is counted by integer square roots. -/
def diskCount (R : ℕ) : ℕ :=
  1 + 4 * R + 4 * ∑ j ∈ Finset.range R, Nat.sqrt (R ^ 2 - (j + 1) ^ 2)

/-- The real quadratic character modulo four, with integer values. -/
def chiFour (d : ℕ) : ℤ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-- Classical sum-of-two-squares input, recorded as a hypothesis Prop.
Summing r₂(m) = 4 Σ_{d ∣ m} χ₄(d) for 1 ≤ m ≤ R² gives this identity.
This is an optional arithmetic handle on the disk-cover conjecture;
the geometric shadow and its conditional transfer do not assume it. -/
def DiskDivisorIdentity : Prop :=
  ∀ R : ℕ, (diskCount R : ℤ) =
    1 + 4 * ∑ d ∈ Finset.Icc 1 (R ^ 2), chiFour d * ((R ^ 2 / d : ℕ) : ℤ)

/-- Radius 4^n, modulus 8^n: area/modulus is 2^n π, while elementary
perimeter error/modulus tends to zero.  No sharp circle-problem bound is used. -/
def diskResidue (n : ℕ) : ℕ := diskCount (4 ^ n) % (8 ^ n)

noncomputable def diskPhase (n : ℕ) : ℝ :=
  (diskCount (4 ^ n) : ℝ) / (8 : ℝ) ^ n

/-- Frozen geometric bridge, 99% confidence, not yet Lean-proved.
Unit lattice squares sandwich the disk between disks with radius R ± √2.
Thus |diskCount R - π R²| ≤ C R for R ≥ 1.  Set R = 4^n and divide by 8^n.
The oversampling is intentional: the trivial perimeter estimate suffices. -/
@[blueprint (title := "Oversampled integer disk counts shadow the binary orbit of π")]
theorem diskPhase_shadow :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |diskPhase n - (2 : ℝ) ^ n * Real.pi| ≤ C / 2 ^ n := by
  sorry

/-- Quantitative covering conjecture, entirely in natural-number arithmetic.
Every window [N,2N], once N ≥ C 4^k, hits the middle half of every k-bit
cylinder.  It asks for coverage, not uniform frequencies.
Confidence in truth: 85%, heuristic only, untested.  Square counts are a
negative control: their analogous phases tend to zero.  A proposed proof
must exploit the quadratic boundary, not just area plus perimeter error. -/
@[blueprint (title := "Low residues of expanding integer disks cover every binary cylinder")]
def DiskResidueCover : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ N : ℕ, C * 4 ^ k ≤ N →
    ∀ j : ℕ, j < 2 ^ k → ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      (4 * j + 1) * 8 ^ n < 4 * 2 ^ k * diskResidue n ∧
      4 * 2 ^ k * diskResidue n < (4 * j + 3) * 8 ^ n

/-- Frozen transfer, 99% confidence, not yet Lean-proved.
The middle-half margin absorbs the vanishing diskPhase error.  Taking
arbitrarily large N gives arbitrarily late visits to every binary cylinder. -/
theorem pi_disjunctive_of_diskResidueCover (h : DiskResidueCover) :
    IsDisjunctive 2 Real.pi := by
  sorry

/-- The disk convention is tested on a hand-countable known answer. -/
example : diskCount 1 = 5 := by decide +kernel
example : diskCount 2 = 13 := by decide +kernel
example : diskCount 4 = 49 := by decide +kernel
example : (diskCount 4 : ℤ) =
    1 + 4 * ∑ d ∈ Finset.Icc 1 16, chiFour d * ((16 / d : ℕ) : ℤ) := by
  decide +kernel

end NormalNumbers.PiDisjunctiveRoutes
