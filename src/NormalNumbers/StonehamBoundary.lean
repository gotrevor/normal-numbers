import NormalNumbers.StonehamBase6
import NormalNumbers.Disjunctive

/-!
# Fixed-boundary-offset proof of base-6 Stoneham disjunctivity

Attended statement freeze: Ren / Astra, 2026-09-13.
These are proof obligations, not claims of completed formalization.
See BRIEF-stoneham-boundary-2026-09-13.md for the full elementary route.

The headline says every real subinterval is visited arbitrarily late.  It
does not assert normality, a frequency bound, or any statement about log 2.
The boundary map is `k ↦ 3^k - k`, with INTEGER subtraction for congruences.
-/

namespace NormalNumbers

/-- The block-exponent map hits every residue at every binary precision.
Frozen statement: do not weaken, re-hypothesize, rename, or delete. -/
theorem stoneham_exponent_residue_surjective (r a : ℕ) :
    ∃ k : ℕ, k < 2 ^ r ∧
      ((3 : ℤ) ^ k - (k : ℤ)) % (2 ^ r : ℤ) = (a : ℤ) % (2 ^ r : ℤ) := by
  sorry

/-- A fine grid is supplied by the powers of 3.  Only the residues 1 mod 8
are needed, so full classification of the generated subgroup is optional.
Frozen statement. -/
theorem stoneham_three_pow_grid (c a : ℕ) (hc : 3 ≤ c)
    (ha : a < 2 ^ c) (hgrid : a % 8 = 1) :
    ∃ e : ℕ, 3 ^ e % 2 ^ c = a := by
  sorry

/-- Every point on that grid is the exact readout at arbitrarily late
block boundaries.  Natural subtraction is safe once the returned block
conditions are established.  Frozen statement. -/
theorem stoneham_boundary_readout_recurrence (c a K : ℕ) (hc : 3 ≤ c)
    (ha : a < 2 ^ c) (hgrid : a % 8 = 1) :
    ∃ k : ℕ, K ≤ k ∧ 3 ≤ 3 ^ k - c ∧
      sC (3 ^ k - c) = c ∧ readout (3 ^ k - c) = a := by
  sorry

/-- A uniform one-cell bound, strengthening the public readout interface
using the bound already proved internally in StonehamBase6.  Frozen statement. -/
theorem stoneham_orbit_readout_cell (n : ℕ) (hn : 3 ≤ n) :
    (readout n : ℝ) / (2 : ℝ) ^ sC n < orbit 6 stoneham23 n ∧
      orbit 6 stoneham23 n < ((readout n : ℝ) + 1) / (2 : ℝ) ^ sC n := by
  sorry

/-- The sparse boundary subsequence visits every interval arbitrarily late.
This is the mathematical campaign endpoint.  Frozen statement. -/
theorem stoneham_base6_interval_recurrence (u v : ℝ)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ orbit 6 stoneham23 n ∈ Set.Ico u v := by
  sorry

/-- Every finite base-6 word occurs in the Stoneham constant alpha_(2,3).
Frozen headline.  This is weaker than normality, which is false in base 6. -/
theorem isDisjunctive_six_stoneham23 : IsDisjunctive 6 stoneham23 := by
  intro u v hu huv hv
  obtain ⟨n, _, hn⟩ := stoneham_base6_interval_recurrence u v hu huv hv 0
  exact ⟨n, hn⟩

end NormalNumbers
