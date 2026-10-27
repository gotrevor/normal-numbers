/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CoefmassRieszEnergy
import NormalNumbers.CoefmassInputs

/-!
# Coefmass route: Riesz and transfer inputs, and the scheduled site-factorization producer

These are the remaining reviewed statements of `docs/notes/coefmass-bv-ledger-2026-10-11.md`.  They
use the model objects (`psiP`, `periodMean`, `muP`, `rieszCentered`) of `CoefmassRieszEnergy`,
where the energy input `RieszEnergyTail` is proved (`rieszEnergyTail`).

The producer is the SD-free route (referee Astra 2026-10-11): the conditional kernel has
vanishing arithmetic L¹ norm, so no Selberg–Delange input is needed for the scheduled Prop.
-/

namespace NormalNumbers.PrimeModel.SiteFactor

open Filter
open NormalNumbers.Literature
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.Quant

/-- **Riesz fourth moment** (paper: Astra, refereed by Opus, 2026-10-11).  For integer
`k > β = 9A/2` with `A = Σ_j |z_j − 1|²`, the model `‖P_k‖₄` is at most
`(k! e/2π) e^{9C₀A/2} [2^{β/2} π + 2/(k−β)]`, uniformly in `J, y, P, K`.

K is the raw `log D`.  Every subset containing a prime with `log p > K` has weight 0, so the
expansion is `∏_{P∖P_small} μ_p` (modulus ≤ 1) times the expansion over `log p ≤ K`.  The
paper's bound (R) then applies there with `y = e^K`. -/
def RieszFourthMoment : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (P : Finset ℕ),
    (∀ p ∈ P, p.Prime ∧ 2 * J < p) → ∀ K : ℝ, 1 ≤ K → ∀ k : ℕ,
      let A := ∑ j : Fin J, ‖zPhase h J j - 1‖ ^ 2
      9 * A / 2 < k →
        (∑ n ∈ Finset.range (∏ p ∈ P, p), ‖rieszCentered P J y h K k n‖ ^ 4)
            / (∏ p ∈ P, p : ℕ)
          ≤ ((k.factorial : ℝ) * Real.exp 1 / (2 * Real.pi) * Real.exp (9 * C₀ * A / 2)
              * (2 ^ (9 * A / 4) * Real.pi + 2 / (k - 9 * A / 2))) ^ 4

/-- Augmented label at `p`: the sites `j` with `p ∣ n+j+1` that are active at `p` (`p ≤ y_j`),
plus the target `k`.  For `p > 2J` it has at most one element. -/
def augLabel (J : ℕ) (y : Fin J → ℕ) (k : Fin J) (p n : ℕ) : Finset (Fin J) :=
  Finset.univ.filter (fun j => (p ≤ y j ∨ j = k) ∧ p ∣ n + j.val + 1)

/-- Labelled primes: the primes of `S` in `(2J, Y]`. -/
def labPrimes (S : ℕ → Prop) [DecidablePred S] (J Y : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 * J) Y).filter (fun p => p.Prime ∧ S p)

/-- **Augmented joint TV** (repair 2: (5.3′) on the §8 schedule; paper, accepted).  Any
`‖F‖ ≤ 1` that factors through `(n mod primorial 2J, p ↦ augLabel p n)`, for the labelled primes
up to `y_head`, has integer mean within `C e^{−u}` of its model (period) mean.

- `primorial (2J)` is the TV-state modulus `Q_TV`.  It is never a BV modulus.
- The full window `winJ N` is covered by an explicit extension of the source proof: sites with
  `y_j ≤ 2J` carry no labels.
- `u₀` must satisfy both `u ≥ 32` and the CRT condition `(√2+2)/16 + 2(406/u² + 4/u) < 1`;
  `u₀ = 40` works. -/
def AugmentedJointTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℕ, ∀ q a : ℕ, 3 ≤ q → Nat.Coprime a q → ∀ u : ℕ, u₀ ≤ u →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ k : Fin (winJ N), ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 1) →
      (let J := winJ N
       let y := cutU u N J
       let P := labPrimes (residueClass q a) J (y ⟨0, k.pos⟩)
       ∀ n m, n % primorial (2 * J) = m % primorial (2 * J) →
         (∀ p ∈ P, augLabel J y k p n = augLabel J y k p m) → F n = F m) →
      ‖prefixMean F N
        - periodMean F (primorial (2 * winJ N) *
            ∏ p ∈ labPrimes (residueClass q a) (winJ N)
                    (cutU u N (winJ N) ⟨0, k.pos⟩), p)‖
        ≤ C * Real.exp (-(u : ℝ)) + ε

/-- **Scheduled site factorization from the reviewed inputs** (the SD-free route; ledger
"SD-free scheduled producer").  This is `siteFactorizationScheduled_of''` in the referee
correspondence.  The paper proof runs as follows.
- BV transfers `P f` to `Λ f`, with a Hölder truncation of the Q-part first.
- The residual `Λ − C` uses the fresh L² norm, `hE`, `hM4` and `hTV`.
- The kernel satisfies `mean |C_k| ≤ |B| e^{W/J} → 0`, since a nontrivial other site's phases give
  `Re a_p ≤ −c_h` on a growing range of primes.
- The target is `|W_y G_h| ≤ C e^{−u} δ polylog(u) + o(1)`.
- `hE` is proved: see `rieszEnergyTail`. -/
theorem siteFactorizationScheduled_of_kernelDecay (hBV : MultBVOmegaRestricted)
    (hTV : AugmentedJointTV) (hM4 : RieszFourthMoment) (hE : RieszEnergyTail)
    (hMer : MertensAPAsymptotic) : SiteFactorizationScheduled := sorry

end NormalNumbers.PrimeModel.SiteFactor
