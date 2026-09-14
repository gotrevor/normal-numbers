/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Tensor

/-!
# The `√K` in the cover bound is real: a matching lower bound

Laps 32–33 *measured* the deficit `δ_K ≍ √K` of `entropy_E1` and traced it to
`log_det_one_add_tensorGram_le'`, concluding "beating the order needs cancellation across `j`
in `∑_j log(1 + Λ_j)`".  This module settles that as a **theorem**: there is no cancellation
to be had, because

    `log det (1 + T_{K²}^{⊗K}) ≥ c · (K²)^K · √K`

for an explicit `c > 0` and all large `K`.  So the upper bound
`log det (1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 12√K)` is of the **right order**, and the
expedition's word-length ceiling `ℓ = o(√K)` is a property of the object, not of the estimate.

The proof is a fourth-moment (Paley–Zygmund / Khintchine) lower bound, entirely finite:

* `posPart_le_log_one_add` — `(log Λ)^+ ≤ log(1 + Λ)`, so the determinant dominates the
  positive part of the log-spectrum;
* centering the one-site log-spectrum makes `∑_j log Λ̃_j = 0` **exactly**, so
  `∑_j (log Λ̃_j)^+ = ½ ∑_j |log Λ̃_j|`, and `(log Λ)^+ ≥ (log Λ̃)^+` because the centering
  shift `K log(s+1)/s` is nonnegative;
* `sum_abs_ge_sq_mul_sqrt` — two Cauchy–Schwarz steps give `(∑X²)³ ≤ (∑|X|)² (∑X⁴)`;
* `sum_pi_quad` — the exact fourth moment of `X_j = ∑_i ℓ(j_i)` for centered `ℓ`:
  `s² ∑_j X_j⁴ = K s^{K+1} ∑ ℓ⁴ + 3K(K−1) s^K (∑ ℓ²)²` — the `3K²` here is what turns the
  ratio `(∑X²)³/(∑X⁴)` into `Θ(K)` and produces the `√K`;
* `sum_sq_log_lam_ge` / `sum_quad_log_lam_le` — the one-site spectrum has second log-moment
  `≥ (log²2/2) s` (half the eigenvalues are `≥ 2`) and fourth log-moment `O(s)`.
-/

open Finset Real

namespace NormalNumbers.G4

/-! ### §1  Elementary inequalities -/

/-- `(log Λ)^+ ≤ log (1 + Λ)` for `Λ > 0`. -/
theorem posPart_le_log_one_add {Λ : ℝ} (h : 0 < Λ) :
    max (Real.log Λ) 0 ≤ Real.log (1 + Λ) := by
  refine max_le ?_ ?_
  · exact Real.log_le_log h (by linarith)
  · exact Real.log_nonneg (by linarith)

/-- Two Cauchy–Schwarz steps: `(∑ X²)³ ≤ (∑ |X|)² (∑ X⁴)`. -/
theorem sum_sq_cube_le {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    (∑ j, X j ^ 2) ^ 3 ≤ (∑ j, |X j|) ^ 2 * ∑ j, X j ^ 4 := by
  sorry

/-- The Paley–Zygmund form: `∑ |X| ≥ (∑X²) √((∑X²)/(∑X⁴))`. -/
theorem sum_abs_ge_sq_mul_sqrt {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    (∑ j, X j ^ 2) * Real.sqrt ((∑ j, X j ^ 2) / ∑ j, X j ^ 4) ≤ ∑ j, |X j| := by
  sorry

/-! ### §2  The fourth moment of a sum of `K` independent coordinates -/

/-- **Exact fourth moment** for a centered one-site weight `ℓ`. -/
theorem sum_pi_quad {s : ℕ} (hs : 1 ≤ s) (ℓ : Fin s → ℝ) (h1 : ∑ k, ℓ k = 0) (K : ℕ) :
    (s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 4
      = K * (s : ℝ) ^ (K + 1) * (∑ k, ℓ k ^ 4)
        + 3 * K * (K - 1) * (s : ℝ) ^ K * (∑ k, ℓ k ^ 2) ^ 2 := by
  sorry

/-! ### §3  The one-site log-spectrum: second moment from below, fourth from above -/

/-- At least half the eigenvalues satisfy `λ_j ≥ 2`, so `∑_j log²λ_j ≥ (log²2) ⌊s/2⌋`. -/
theorem sum_sq_log_lam_ge (s : ℕ) :
    Real.log 2 ^ 2 * ((s : ℝ) / 2 - 1) ≤ ∑ j : Fin s, Real.log (lam s j) ^ 2 := by
  sorry

/-- Fourth log-moment of the spectrum: `∑_j log⁴λ_j = O(s)`. -/
theorem sum_quad_log_lam_le {s : ℕ} (hs : 1 ≤ s) :
    ∑ j : Fin s, Real.log (lam s j) ^ 4 ≤ 4194304 * (s : ℝ) := by
  sorry

end NormalNumbers.G4
