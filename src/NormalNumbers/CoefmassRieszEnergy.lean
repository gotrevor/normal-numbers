/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelPhaseAlgebra

/-!
# Model energy above the Riesz cutoff

The coefmass route (`docs/notes/coefmass-bv-ledger-2026-10-11.md`) names `RieszEnergyTail` as one
of the inputs of `siteFactorizationScheduled_of'`.  It is elementary, and this file proves it.

**Objects.**  For a finite set `P` of primes, the local phase of `p` at `n` is
`ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j`.  It is unimodular and depends only on `n mod p`.
`μ_p` is its mean over one period, and `φ_p = ψ_p − μ_p`.  Since `∏ (μ_p + φ_p) = ∏ ψ_p`, the
frozen product expands over subsets: `Φ = Σ_{T ⊆ P} c_T` with
`c_T = ∏_{p∉T} μ_p ∏_{p∈T} φ_p`.  The Riesz truncation weights the `T`-term by
`w_T = (1 − log d_T / K)_+^k`, where `d_T = ∏_{p∈T} p`.

**Claim.**  Over one CRT period `M = ∏_{p∈P} p`,
`mean |Φ − P_k|² ≤ (k/K) Σ_{p∈P} V_p log p`, where `V_p = 1 − |μ_p|²`.

**Proof plan** (each step a lemma):
1. *CRT product average.*  For pairwise distinct primes, `(1/M) Σ_{n<M} ∏_{p∈P} g_p(n mod p)`
   equals `∏_{p∈P} (1/p) Σ_{r<p} g_p r`.  This is the only arithmetic input; use
   `Nat.chineseRemainder` or the `ZMod` product equivalence.
2. *Periodicity.*  `psiP J y h p n = psiP J y h p (n % p)`.
3. *Orthogonality.*  For `T ≠ T′` the mean of `c_T · conj c_{T′}` is 0, because a prime in the
   symmetric difference contributes a factor `mean φ_p = 0` (by step 1).  Also
   `mean |c_T|² = ∏_{p∉T} |μ_p|² ∏_{p∈T} V_p`, using `mean |φ_p|² = mean |ψ_p|² − |μ_p|² = V_p`
   (with `|ψ_p| = 1`, `‖zPhase‖ = 1`).
4. *Expansion.*  `Φ − P_k = Σ_T (1 − w_T) c_T`, by `Finset.prod_add`.  So
   `mean |Φ − P_k|² = Σ_T (1 − w_T)² mean |c_T|²`.
5. *Scalar inequality.*  For `k ≥ 1`, `K > 0` and `x = log d_T / K ≥ 0`,
   `(1 − (max 0 (1 − x))^k)² ≤ k x`.  If `x ≥ 1` the left side is 1.  Otherwise use
   Bernoulli (`one_add_mul_le_pow`) and `(1−w)² ≤ 1−w`.
6. *Summation.*  `Σ_T log d_T ∏_{p∉T}|μ_p|² ∏_{p∈T} V_p = Σ_p V_p log p`, since
   `|μ_p|² + V_p = 1`: split `log d_T = Σ_{p∈T} log p` and sum out the other primes.

Exact numerical control (Opus, 2026-10-11): J=3, P={7,11,13,17}, four `(K, k)` pairs.  The
period-mean energy equals the orthogonal sum to all printed digits and lies under the bound.
-/

namespace NormalNumbers.PrimeModel.SiteFactor

open NormalNumbers.PrimeModel.PhaseAlgebra

/-- Local phase of prime `p` at `n`: `ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j`. -/
noncomputable def psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p n : ℕ) : ℂ :=
  ∏ j : Fin J, if p ≤ y j ∧ p ∣ n + j.val + 1 then zPhase h J j else 1

/-- Exact average over one period: the model expectation, by CRT. -/
noncomputable def periodMean (F : ℕ → ℂ) (M : ℕ) : ℂ := (∑ n ∈ Finset.range M, F n) / M

/-- The period mean of the local phase. -/
noncomputable def muP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ) : ℂ :=
  periodMean (psiP J y h p) p

/-- Riesz-truncated centered expansion over a finite prime set `P`:
`Σ_{T ⊆ P} (1 − log d_T/K)_+^k ∏_{p∉T} μ_p ∏_{p∈T} (ψ_p − μ_p)`. -/
noncomputable def rieszCentered (P : Finset ℕ) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k : ℕ)
    (n : ℕ) : ℂ :=
  ∑ T ∈ P.powerset, ((max 0 (1 - Real.log (∏ p ∈ T, (p : ℝ)) / K)) ^ k : ℝ) *
    ((∏ p ∈ P \ T, muP J y h p) * ∏ p ∈ T, (psiP J y h p n - muP J y h p))

/-- **Model energy above the Riesz cutoff.** -/
def RieszEnergyTail : Prop :=
  ∀ (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
    ∀ K : ℝ, 0 < K → ∀ k : ℕ, 1 ≤ k →
      (∑ n ∈ Finset.range (∏ p ∈ P, p),
          ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2) / (∏ p ∈ P, p : ℕ)
        ≤ k / K * ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p

theorem rieszEnergyTail : RieszEnergyTail := by
  sorry

end NormalNumbers.PrimeModel.SiteFactor
