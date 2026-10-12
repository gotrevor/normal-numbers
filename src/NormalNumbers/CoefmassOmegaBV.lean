/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeSiteFactorization

/-!
# Restricted-level Bombieri–Vinogradov for the ω form

`MultBVOmegaRestricted` and its producer `multBVOmegaRestricted_of`, moved verbatim from
`CoefmassInputs.lean` (statements frozen; referee sign-off on the statement: Astra/codex2,
2026-10-12, mail `20261012T020512Z-codex2-8f0bc6bb`).  The only input is `MultBVResidue`
(`CPrimeSiteFactorization.lean`).
-/

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

/-- Paper proof (Opus, refereed by Astra/codex2 2026-10-12).  Fix `q₀, a, z, θ, A`; write
`S = {p prime : p ≡ a (q₀), p ≤ y}`, `f = z^{Ω_S}` (`omegaMultLe`), `g = z^{ω_S}` (`omegaLe`).

1. *Convolution.*  `g = h ∗ f` on positive integers, where `h` is multiplicative with
   `h(p^ν) = z(1−z)` for `p ∈ S`, `ν ≥ 2`, and every other prime-power value `0` (`h(1) = 1`).
   The local identity is `(1 + (z−1)X)(1 − zX)/(1 − X) = 1 + z(1−z)X²/(1−X)`.  Hence
   `|h(b)| ≤ H(b)`, where `H(b) = 2^{ω(b)}` on squarefull `b` and `0` otherwise.  `H` does not
   depend on `q₀, a, y, z`.
2. *Summability of the majorant.*  For `s > 1/2`, `Σ_b H(b)/b^s = ∏_p (1 + 2p^{−2s}/(1−p^{−s}))`
   is finite.  So `Σ H(b)/b` is bounded, and by Rankin `Σ_{b>T} H(b)/b ≪_ε T^{−1/2+ε}`.
3. *Discrepancy identity.*  For `(c, e) = 1`:
   `Δ(g, x; e, c) = Σ_{b ≤ x, (b,e)=1} h(b) Δ(f, ⌊x/b⌋; e, c·b⁻¹ mod e)`.  The terms with
   `(b, e) > 1` drop from both the progression sum and the coprime mean.  `b ↦ c b⁻¹` permutes
   the units mod `e`, so `sup_c |Δ(g)| ≤ Σ_b |h(b)| sup_c |Δ(f, ⌊x/b⌋; e, ·)|`.  `e = 1` is
   trivial (the discrepancy is `0`).
4. *Small `b ≤ √x`.*  `t = ⌊x/b⌋ ≥ √x/2` and `log t ≥ (log x)/3` eventually.  With `B` from
   `MultBVResidue` at saving `A`, put `B⁺ = max B 0`.  Then `√t/(log t)^{B⁺} ≥ x^θ` eventually
   (θ < 1/4), so every `e ≤ x^θ` lies in the input's modulus range at length `t`.  The input
   gives `≤ C t/(log t)^A`, and summing with weight `H(b)` gives `≪ x/(log x)^A` by step 2.
   Invoke the input with the SAME `y` (it may exceed `t`).
5. *Large `b > √x`.*  Use `sup_c |Δ(f, t; e, c)| ≤ 2t` and `Σ_{e ≤ x^θ} 1 ≤ x^θ`.  Together
   with step 2 this gives `≪ x^{θ + 3/4 + ε}`; take `ε < 1/4 − θ`.
6. *Quantifiers.*  Every threshold and constant is independent of `y`.  For the finitely many
   `x` below the threshold, `|g| ≤ 1` bounds the sum, so enlarge `C`. -/
theorem multBVOmegaRestricted_of (h : MultBVResidue) : MultBVOmegaRestricted := sorry

end NormalNumbers.PrimeModel.SiteFactor
