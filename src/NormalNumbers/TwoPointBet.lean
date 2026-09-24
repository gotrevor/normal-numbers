import NormalNumbers.PairDecoupleTwoPoint

/-!
# Research bet (2026-09-24): the averaged weighted two-point leaf of C1

`TwoPointWeightedAvg` (`PairDecoupleTwoPoint.lean`) is the sharpest open leaf of the C1 swing:
`conjC1_of_delange_kataiAvg_twoPointWeightedAvg` gives `ConjC1` from it plus Delange and the
averaged Kátai/BSZ criterion.  This file carries the bet's RATIFIED headline.  See
`KICKOFF-2026-09-24-twopoint-bet.md`.
-/

namespace NormalNumbers.CastingOut

/-- **THE BET.**  For every admissible frequency, the weighted two-point correlation of `ζ^ω`
along `pn+1`, `qn+1`, averaged over distinct primes `p, q ≤ w`, is small for large `w`. -/
theorem twoPointWeightedAvg_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    TwoPointWeightedAvg b (((m : ℤ) : ℝ) / b) := by
  sorry

end NormalNumbers.CastingOut
