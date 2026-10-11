/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeSiteFactorization
import NormalNumbers.G4MertensAP

/-!
# Coefmass route: reviewed inputs and the scheduled second-order producer

These are the statements of `docs/notes/coefmass-bv-ledger-2026-10-11.md` and
`docs/notes/pair-second-order-2026-10-11.md` that the referee (Astra) has reviewed.  The Riesz
inputs (`RieszFourthMoment`, `RieszEnergyTail`), `AugmentedJointTV` and the site-factorization
producer depend on definitions being proved on branch `wip/riesz-energy`.  They are planted after
that branch merges.

* `MultBVOmegaRestricted`: restricted-level BV for the ω form, derived from `MultBVResidue`.
* Literature inputs `MertensAPAsymptotic`, `BrunTitchmarshAP` and `UpperSieveTwoLinearForms`.
  The last two are checked against K. Ford, *Sieve Methods* lecture notes (2023), Thms 2.7 and
  2.5.
* `PairSecondOrderScheduled` and its producer.  This is the frozen `PairSecondOrder` on the
  Erdős–Turán schedule only, as a separate statement; the all-`u` Prop is unchanged.  Its proof
  (paper, signed off conditionally by Astra 2026-10-11) loses a factor `log(1/δ)` in the corner
  `p ≈ p′ ≈ √N`, which the schedule absorbs.
-/

namespace NormalNumbers.Literature

open Filter Topology

/-- Mertens in progressions, asymptotic form (classical).  The repo has only lower-bound rates
(`G4.MertensAP.mertensRate_residueClass`).  It gives the fresh mass
`Σ_{y<p≤x, p≡a} 1/p = δ log(log x/log y) + o(1)` as `y → ∞`. -/
def MertensAPAsymptotic : Prop :=
  ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q → ∃ M : ℝ, Tendsto (fun x : ℕ =>
    G4.MertensAP.sumInvPrimesIn (PrimeModel.SiteFactor.residueClass q a) x
      - Real.log (Real.log x) / (Nat.totient q : ℝ)) atTop (𝓝 M)

/-- Brun–Titchmarsh in progressions (Montgomery–Vaughan 1973: constant 2), weakened to an
absolute C.  Checked source: K. Ford, *Sieve Methods* lecture notes (2023), Thm 2.7. -/
def BrunTitchmarshAP : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → ∀ x : ℝ, (k : ℝ) < x →
    (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % k = l % k)).card : ℝ)
      ≤ C * x / ((Nat.totient k : ℝ) * Real.log (x / k))

/-- Upper-bound sieve for two linear forms, uniform in the coefficients.  Source: K. Ford,
*Sieve Methods* lecture notes (2023), Thm 2.5 with k = 2 (constants depend only on k, for
primitive admissible forms).  The general case reduces to it by elementary case splits:
- a nonprimitive form has at most 2 prime hits;
- a primitive inadmissible pair is obstructed at 2, so it has at most 4 hits;
- otherwise use four sign choices, which preserve `|E|` and admissibility.

The singular series is at most `C (E/φ(E))²`. -/
def UpperSieveTwoLinearForms : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ : ℕ, ∀ b₁ b₂ : ℤ, 0 < a₁ → 0 < a₂ →
    (a₁ : ℤ) * a₂ * (a₁ * b₂ - a₂ * b₁) ≠ 0 → ∀ X : ℕ, 3 ≤ X →
      (((Finset.Icc 1 X).filter (fun t : ℕ =>
          ((a₁ : ℤ) * t + b₁).natAbs.Prime ∧ ((a₂ : ℤ) * t + b₂).natAbs.Prime)).card : ℝ)
        ≤ C * (((a₁ * a₂ * (a₁ * b₂ - a₂ * b₁) : ℤ).natAbs : ℝ)
                / Nat.totient (a₁ * a₂ * (a₁ * b₂ - a₂ * b₁) : ℤ).natAbs) ^ 2
            * X / Real.log X ^ 2

end NormalNumbers.Literature

namespace NormalNumbers.PrimeModel.SiteFactor

open Filter
open NormalNumbers.Literature
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.Quant

/-- **Restricted-level BV for the ω form** (derived from `MultBVResidue`; believed ~90%).  Moduli
range only up to `x^θ` with `θ < 1/4`, NOT the full `√x/log^B` range.  A consumer whose conductor
is `Q·N^θ` at lengths `N/a`, `a ≤ (log N)^D`, invokes this at some `θ′ ∈ (θ, 1/4)`; the strict
gap absorbs both. -/
def MultBVOmegaRestricted : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ z : ℂ, ‖z‖ = 1 → ∀ θ : ℝ, 0 < θ → θ < 1/4 →
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 3 ≤ x →
      ∑ e ∈ (Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊).filter (fun e => Nat.Coprime e q₀),
        ⨆ c : {c : Fin e // Nat.Coprime c.val e},
          ‖apDiscrepancy (fun n => z ^ omegaLe (residueClass q₀ a) y n) x e c.val.val‖
        ≤ C * x / Real.log x ^ A

/-- Believed ~90%.  English proof:
- write `z^{ω_P} = z^{Ω_P} ∗ h_z`, whose local factor is `H_p = 1 + z(1−z)X²/(1−X)`, so h is
  supported on squarefull b with `|h| ≤ 2`;
- for `b ≤ √x`, apply `MultBVResidue` at length `x/b`, with moduli `e ≤ x^θ ≤ √(x/b)/log^B`
  since θ < 1/4;
- for `b > √x`, use the trivial bound `x^{θ+3/4+ε}`.

A coprime residue c kills every term with `(b, e) > 1`. -/
theorem multBVOmegaRestricted_of (h : MultBVResidue) : MultBVOmegaRestricted := sorry

/-- **Second order on the Erdős–Turán schedule.**  A SEPARATE statement: the frozen all-`u`
`PairSecondOrder` is unchanged. -/
def PairSecondOrderScheduled : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₁ : ℕ, ∀ q a : ℕ, 3 ≤ q → q₁ ≤ q → Nat.Coprime a q →
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ schedU q → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖fullMean (residueClass q a) (winJ N) h N
        - windowMeanLeG (residueClass q a) (winJ N) (cutU (schedU q) N (winJ N)) h N
        - freshOneSite (residueClass q a) (winJ N) (cutU (schedU q) N (winJ N)) h N‖
        ≤ C * freshBudget (1 / (Nat.totient q : ℝ)) h (winJ N) (schedU q) ^ 2 + ε

/-- Paper proof, signed off conditionally by the referee (Astra, 2026-10-11):
`docs/notes/pair-second-order-2026-10-11.md`, "Consolidated pair argument (v2)" and the final
review section.  The steps:
- a fixed fresh-site cut, with the deep tail through `J₁(N)`;
- the unimodular reduction `|R| ≤ Σ_{i<j} |f_i||f_j|`;
- regions: CRT, Brun–Titchmarsh off the diagonal, the two-forms sieve near the diagonal (where
  the weighted compatibility average gives exactly δ²), and the corner `p ≈ p′ ≈ √N` at
  `γ = w = δ`.

The corner loses `log(1/δ)`, which the schedule's `log s ≥ 4 log(1/ρ)` absorbs. -/
theorem pairSecondOrderScheduled_of (hBT : BrunTitchmarshAP) (hUS : UpperSieveTwoLinearForms)
    (hMer : MertensAPAsymptotic) : PairSecondOrderScheduled := sorry

/-- The `cprimeResidueQuad_of_scheduled` chain with the scheduled second-order input: the 10-01
chain evaluates `PairSecondOrder` only at `u = ⌈ρ⁻²⌉`, `|h| ≤ H = ⌈ρ⁻²⌉`
(`docs/CPRIME-SITE-FACTORIZATION-2026-10-01.md`, §Chain). -/
theorem cprimeResidueQuad_of_scheduled' (hSF : SiteFactorizationScheduled)
    (hPair : PairSecondOrderScheduled) : CPrimeResidueQuad := sorry

end NormalNumbers.PrimeModel.SiteFactor
