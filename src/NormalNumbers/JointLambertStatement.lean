import NormalNumbers.CastingOut
import NormalNumbers.JointLambertEncoding

/-!
# Frozen simultaneous Erdős–Borwein target

Paper proof: `papers/2026-09-26-joint-lambert-disjunctivity.md`.
These are propositions, not claimed Lean theorems.  The existing scalar
`CastingOut.ConjC2` is unchanged.  A Finset enforces distinct bases, including
multiplicatively dependent pairs such as 2 and 4.
-/

namespace NormalNumbers.JointLambert

/-- Every prescribed collection of words occurs at a common, arbitrarily late
offset.  Offset `n` means the words start at digit `n + 1` after the point. -/
def JointWords (S : Finset ℕ) : Prop :=
  ∀ lengths values : ℕ → ℕ,
    (∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ b ∈ S,
        ⌊(b : ℝ) ^ lengths b * orbit b (CastingOut.erdosBorweinAtBase b) n⌋
          = (values b : ℤ)

/-- Full paper headline, including base 2.  Not yet a theorem in Lean. -/
def JointLambertDisjunctivity : Prop :=
  ∀ S : Finset ℕ, (∀ b ∈ S, 2 ≤ b) → JointWords S

/-- The finite encoding interface: even divisor counts hit every product of
open intervals.  `s >= 2` leaves the zero slot available to the CRT construction. -/
def EvenEncoding : Prop :=
  ∀ S : Finset ℕ, (∀ b ∈ S, 2 ≤ b) →
    ∀ lo hi : ℕ → ℝ,
      (∀ b ∈ S, 0 ≤ lo b ∧ lo b < hi b ∧ hi b ≤ 1) →
      ∃ s a : ℕ, 2 ≤ s ∧ 2 ≤ a ∧
        ∀ b ∈ S, lo b < Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) ∧
          Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) < hi b

end NormalNumbers.JointLambert
