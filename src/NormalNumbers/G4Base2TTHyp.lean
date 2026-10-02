/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Bins

/-!
# N5: TT's hypothesis (3.1) for a bin indicator

For a set `I` of primes all `> Y ≥ X^{1/101}`, the bin indicator `g_I` has mean
`δ_I(N) = Σ_{T ⊆ I, ∏T ≤ 2N} (−1)^{|T|}/∏T` on every progression in `(N, 2N]`, with error
`≪ N/log X`.  Inclusion–exclusion over the squarefree `I`-products `d ≤ 2N`: each costs `O(1)`
(for `q < Y`, `gcd(d, q) = 1`), and they number `≪ N/log X` (rough-number count: `d` has at most
`101` prime factors, all `> Y`, so Chebyshev plus Mertens).  For `q ≥ Y` both sides are
`O(N/Y + 1)`.  The truncation `∏T ≤ 2N` is essential: the untruncated product misses by
`≈ mass(I)²`, which is not `o(1)`.
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- The truncated density `δ_I(N)`. -/
noncomputable def binDelta (I : Finset ℕ) (N : ℝ) : ℝ :=
  ∑ T ∈ I.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) ≤ 2 * N),
    (-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)

/-- **N5.**  TT's hypothesis (3.1) for bin indicators, with `L = log X / C₅`.  85%. -/
theorem binInd_ap_mean : ∃ C₅ X₀ : ℝ, 0 < C₅ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ Y : ℝ,
    X ^ ((1 : ℝ) / 101) ≤ Y → ∀ I : Finset ℕ, (∀ p ∈ I, p.Prime ∧ Y < p) →
    ∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
      ‖(∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), binInd I n)
          - (((N / q) * binDelta I N : ℝ) : ℂ)‖ ≤ N / (Real.log X / C₅) := by
  sorry

end NormalNumbers.G4.Base2
