/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import NormalNumbers.PiBBP
import NormalNumbers.Furstenberg

/-!
# Three experimental routes to disjunctivity of π

These are research statements, not established arithmetic estimates.  The three
new premises are `PiQuantitativeTripleReturn`, `PiPrimeReservoirSupport`, and
`DiskResidueCover`.  The transfer arguments below are frozen with `sorry`:
their docstrings give the mathematical argument and its evidence tier.

The first qualitative premise is EQUIVALENT to binary disjunctivity for
irrational inputs.  It is a change of target, not a weakening.  The other two
premises ask for extra joint support or a quantitative covering rate.  No
numerical evidence or claim of literature priority is asserted here.

Existing foundation: `MasterConjectures.BaileyCrandallHypA`,
`MasterConjectures.hypA_pi_base16`, `PiBBP`, and
`Furstenberg.isClosed_invariant_finite_or_univ`.  In particular the BBP
surrogate itself is not a new route; the prime/residual JOINT support is the
new premise, and must not be inferred from separate marginal distribution.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- Distance to an integer, expressed without a choice of nearest integer. -/
def NearInteger (x ε : ℝ) : Prop := ∃ z : ℤ, |x - (z : ℝ)| < ε

/-- One prescribed return target, at arbitrarily late positions. -/
def TripleReturn (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ NearInteger (((2 : ℝ) ^ n - 3) * x) ε

/-- A deliberately generous quantitative return conjecture for π.
Confidence in truth: 90%, heuristic only; no proof mechanism established.
The bound is exponential in the requested precision, not in a starting index. -/
@[blueprint (title := "π returns near its triple within an exponential precision budget")]
def PiQuantitativeTripleReturn : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ n : ℕ, k ≤ n ∧ n ≤ C * 4 ^ k ∧
      NearInteger (((2 : ℝ) ^ n - 3) * Real.pi) (1 / 2 ^ k)

/-- Frozen mathematical argument, 99% confidence, not yet Lean-proved.
Let K be the binary orbit closure on the circle.  TripleReturn gives 3x ∈ K.
Since K is ×2-invariant, every 2^m 3x belongs to K.  Continuity gives 3K ⊆ K.
Irrationality makes K infinite; the existing ×2×3 theorem gives K = circle.
Conversely, a dense irrational binary orbit has every tail dense, and hence
approaches 3x.  This equivalence explicitly prevents calling the return
premise weaker than disjunctivity. -/
@[blueprint (title := "A single triple-return target characterizes binary disjunctivity")]
theorem tripleReturn_iff_disjunctive {x : ℝ} (hx : Irrational x) :
    TripleReturn x ↔ IsDisjunctive 2 x := by
  sorry

/-- Frozen transfer, 99% confidence: take precision k ≥ the requested
starting index, then let k grow; apply the previous bootstrap and π irrational. -/
theorem pi_disjunctive_of_quantitativeTripleReturn
    (h : PiQuantitativeTripleReturn) : IsDisjunctive 2 Real.pi := by
  sorry

/-- The part of the BBP rational head carried by prime denominators > 4n.
Such a denominator occurs only once in the four denominator families below
8n.  The odd families are 8j+1 (coefficient 4) and 8j+5 (coefficient -1).
All other terms remain in `bbpResidual`; nothing is discarded. -/
noncomputable def bbpPrimeReservoir (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (16 : ℝ) ^ (n - j) *
    ((if Nat.Prime (8 * j + 1) ∧ 4 * n < 8 * j + 1 then
        4 / (8 * (j : ℝ) + 1) else 0) -
     (if Nat.Prime (8 * j + 5) ∧ 4 * n < 8 * j + 5 then
        1 / (8 * (j : ℝ) + 5) else 0))

noncomputable def bbpResidual (n : ℕ) : ℝ :=
  (16 : ℝ) ^ n * piPartial n - bbpPrimeReservoir n

/-- The same BBP head as an exact rational, for denominator arithmetic. -/
def bbpRationalHead (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (16 : ℚ) ^ (n - j) *
    (4 / (8 * (j : ℚ) + 1) - 2 / (8 * (j : ℚ) + 4) -
      1 / (8 * (j : ℚ) + 5) - 1 / (8 * (j : ℚ) + 6))

/-- Frozen elementary argument, 99% confidence, not yet Lean-proved.
A prime in this strip divides exactly one displayed denominator (all are
< 8n); its numerator is 4 or -1 times a power of 16, prime to p.  All
other terms are p-integral, so the pole survives in the reduced rational.
This certifies an arithmetic source, NOT independence modulo one. -/
@[blueprint (title := "Fresh BBP prime denominators survive reduction of the whole head")]
theorem fresh_prime_dvd_head_den {n p : ℕ} (hp : Nat.Prime p)
    (hlo : 4 * n < p) (hhi : p < 8 * n) (hclass : p % 8 = 1 ∨ p % 8 = 5) :
    p ∣ (bbpRationalHead n).den := by
  sorry

/-- Exact split; the residual retains the whole unselected rational head. -/
theorem bbp_split (n : ℕ) :
    bbpPrimeReservoir n + bbpResidual n = (16 : ℝ) ^ n * piPartial n := by
  simp [bbpResidual]

/-- Every open rectangle in the two-torus is visited arbitrarily late.
Confidence in truth: 70%, speculative arithmetic decoupling, untested.
This is stronger than support of the sum.  Separate uniform marginals do
not suffice: a rational telescoping control can lock the sum on a diagonal.
There is no conditioning on the exact residual, which could encode n. -/
@[blueprint (title := "Fresh BBP prime denominators have joint support with the residual")]
def PiPrimeReservoirSupport : Prop :=
  ∀ a c d e : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    0 ≤ d → d < e → e ≤ 1 → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧
      Int.fract (bbpPrimeReservoir n) ∈ Ioo a c ∧
      Int.fract (bbpResidual n) ∈ Ioo d e

/-- Frozen transfer, 99% confidence, not yet Lean-proved.
Choose a rectangle whose sum modulo one lies strictly inside the desired
cylinder.  Hit it at n large enough that the BBP tail O(n^-2) is smaller
than the boundary margin.  The exact split then gives a genuine π hit. -/
theorem pi_disjunctive_of_primeReservoirSupport (hπ : PiBBP)
    (h : PiPrimeReservoirSupport) : IsDisjunctive 16 Real.pi := by
  sorry

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
example : 5 ∣ (bbpRationalHead 1).den := by decide +kernel
example : 13 ∣ (bbpRationalHead 2).den := by decide +kernel
example : 17 ∣ (bbpRationalHead 3).den := by decide +kernel
example : (diskCount 4 : ℤ) =
    1 + 4 * ∑ d ∈ Finset.Icc 1 16, chiFour d * ((16 / d : ℕ) : ℤ) := by
  decide +kernel

end NormalNumbers.PiDisjunctiveRoutes
