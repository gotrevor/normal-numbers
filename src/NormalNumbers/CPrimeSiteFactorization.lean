/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeQuantStatement

/-!
# Site factorization: the frozen statements behind `RelativeFirstOrder`

Quantitative C′ (`CPrimeQuantStatement.lean`) bounds the orbit discrepancy of `∑_{p∈P} 1/(4ᵖ−1)`
by `C ρ log³(1/ρ)`, where `ρ` is the square-root fresh mass.  The `ρ` comes from one place: the
transfer from the full window mean `W` to the frozen mean `W_y` (site `j` keeps only the primes
`≤ y_j`) is bounded by the triangle inequality, linear in the fresh mass.

This file freezes the three statements that would make that defect quadratic:

* `SiteFactorization`: the first-order fresh term `T1'` (fresh primes at one site, every other
  site frozen) equals `W_y · G_h(u)` up to an error that vanishes as the schedule parameter `u`
  grows.  `G_h(u) = ∑_k [s_k^{κ_k} e^{−γκ_k}/Γ(1+κ_k) − 1]` with `κ_k = δ(z_k − 1)`,
  `s_k = u²·2^{k+1}`, `δ = 1/φ(q)`.  The proof-regime cutoffs make the Dickman factor `F_κ`
  of `docs/CPRIME-QUANTITATIVE-2026-09-30.md` equal to `1` up to the stated error, so the
  limit form appears here.
* `PairSecondOrder`: what is left, `W − W_y − T1'`, lives on integers with fresh primes at two
  sites and is bounded by the square of the weighted fresh mass.  Upper-bound sieve strength.
* `CPrimeResidueQuad`: the consumer.  Residue classes mod `q` have discrepancy
  `O(log³φ(q)/φ(q)²)`, the square of `CPrimeResidueRich`'s rate.

The one external input the mechanism names is `Literature.GranvilleShaoBVResidue`
(Bombieri–Vinogradov for `z^{Ω_P}`, Granville–Shao 2018).  Paper statement, mechanism and the
negative-inventory check: `docs/CPRIME-SITE-FACTORIZATION-2026-10-01.md`.

## Guard rule

**Content locator.**  `SiteFactorization`'s error `C(e^{−u/2} + δ/√u)` is fixed before `u` is
chosen, while the triangle bound on `T1'` grows like `δ log u`.  So the Prop claims genuine
first-order cancellation; it is not discharged by the C′ transfer bound.  Since
`|W_y| ≤ 4e^{−u} + o(1)` in this regime, its content is "one-site fresh primes inherit the frozen
mean's decay"; the explicit `G_h` makes it testable at reachable `N`
(`experiments/cprime_fresh_cancellation.py`).

**Degenerate cases.**  At a pole (`κ` a negative integer, e.g. `z = −1`, `δ = 1/2`) Mathlib's
`Complex.Gamma` vanishes, so the inverse is `0` and the site factor is `−1`, which is the
analytic value.  All primes are excluded (`3 ≤ q`), and the statements say nothing about G₄.
`PairSecondOrder` is the only place two sites carry fresh primes at once, and it asks for an
upper bound only: no parity-sensitive correlation enters.
-/

namespace NormalNumbers.PrimeModel.SiteFactor

open Filter
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseFactor
open NormalNumbers.PrimeModel.PhaseAlgebra NormalNumbers.PrimeModel.Quant

/-- Primes `≡ a (mod q)`. -/
def residueClass (q a : ℕ) : ℕ → Prop := fun p => p % q = a % q

instance (q a : ℕ) : DecidablePred (residueClass q a) :=
  fun p => inferInstanceAs (Decidable (p % q = a % q))

/-- Window length `⌊log₂ log₂ N⌋ + 1`, as in the probe. -/
def winJ (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N) + 1

/-- Proof-regime cutoffs: site `j+1` keeps the primes `≤ N^(u⁻²·2^{−(j+1)})`. -/
noncomputable def cutU (u N J : ℕ) : Fin J → ℕ :=
  fun j => ⌊(N : ℝ) ^ ((1 / (u : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (j.val + 1))⌋₊

/-- The full window mean, every prime of `S` counted (`n + j + 1 ≤ N + J`). -/
noncomputable def fullMean (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (h : ℤ) (N : ℕ) : ℂ :=
  prefixMean (fun n => ∏ j : Fin J, zPhase h J j ^ omegaLe S (N + J) (n + j.val + 1)) N

/-- **`T1'`**: fresh primes at one site `k`, every site's frozen part kept.
`∑_k mean[ ∏_j z_j^{ω_{≤y_j}(n+j)} · (z_k^{ω_{>y_k}(n+k)} − 1) ]`.  It differs from the exact
one-site term `T1` only on integers with fresh primes at two sites. -/
noncomputable def freshOneSite (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (N : ℕ) : ℂ :=
  ∑ k : Fin J, prefixMean (fun n =>
    (∏ j : Fin J, zPhase h J j ^ omegaLe S (y j) (n + j.val + 1)) *
      (zPhase h J k ^ omegaGt S (y k) (n + k.val + 1) - 1)) N

/-- One site's factor `s^κ e^{−γκ} / Γ(1+κ) − 1`.  The fresh tail `∏_{y<p≤N, p∈P}(1 + w/p) → s^κ`
by Mertens in progressions, and `e^{−γκ}/Γ(1+κ)` is the Selberg–Delange size budget. -/
noncomputable def siteFactor (κ : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ κ * Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * κ) *
    (Complex.Gamma (1 + κ))⁻¹ - 1

/-- `G_h(u) = ∑_k siteFactor(δ(z_k − 1), u²·2^{k+1})`. -/
noncomputable def siteG (δ : ℝ) (h : ℤ) (J u : ℕ) : ℂ :=
  ∑ k : Fin J, siteFactor ((δ : ℂ) * (zPhase h J k - 1)) ((u : ℝ) ^ 2 * 2 ^ (k.val + 1))

/-- **Site factorization (frozen).**  For residue classes, `T1' = W_y · G_h(u)` up to
`C_h (e^{−u/2} + δ/√u)`, with `C_h` uniform in the modulus and in `u`. -/
def SiteFactorization : Prop :=
  ∃ u₀ : ℕ, ∀ h : ℤ, h ≠ 0 → ∃ C : ℝ, 0 < C ∧
    ∀ q a : ℕ, 3 ≤ q → Nat.Coprime a q → ∀ u : ℕ, u₀ ≤ u → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖freshOneSite (residueClass q a) (winJ N) (cutU u N (winJ N)) h N
        - windowMeanLeG (residueClass q a) (winJ N) (cutU u N (winJ N)) h N
          * siteG (1 / (Nat.totient q : ℝ)) h (winJ N) u‖
        ≤ C * (Real.exp (-(u : ℝ) / 2) + 1 / ((Nat.totient q : ℝ) * Real.sqrt u)) + ε

/-- The weighted fresh mass `∑_k |z_k − 1| · δ log(u²·2^{k+1})`, the expansion parameter. -/
noncomputable def freshBudget (δ : ℝ) (h : ℤ) (J u : ℕ) : ℝ :=
  ∑ k : Fin J, ‖zPhase h J k - 1‖ * (δ * Real.log ((u : ℝ) ^ 2 * 2 ^ (k.val + 1)))

/-- **Second order (frozen).**  `W − W_y − T1'` is at most an absolute constant times the square
of the weighted fresh mass: an upper-bound sieve for two linear forms, no parity input. -/
def PairSecondOrder : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q a : ℕ, 3 ≤ q → Nat.Coprime a q → ∀ h : ℤ, ∀ u : ℕ, 1 ≤ u →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖fullMean (residueClass q a) (winJ N) h N
        - windowMeanLeG (residueClass q a) (winJ N) (cutU u N (winJ N)) h N
        - freshOneSite (residueClass q a) (winJ N) (cutU u N (winJ N)) h N‖
        ≤ C * freshBudget (1 / (Nat.totient q : ℝ)) h (winJ N) u ^ 2 + ε

/-- **Quadratic residue-class discrepancy (frozen consumer).**  Primes `≡ a (mod q)` give orbit
discrepancy `≤ C log³φ(q)/φ(q)²`, uniformly in the unit `a`. -/
def CPrimeResidueQuad : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q a : ℕ, q₀ ≤ q → Nat.Coprime a q →
    OrbitDefectLe (PrimeLambert.subsetLambert (residueClass q a) 4)
      (C * Real.log (Nat.totient q) ^ 3 / (Nat.totient q : ℝ) ^ 2)

end NormalNumbers.PrimeModel.SiteFactor

namespace NormalNumbers.Literature

open NormalNumbers.PrimeModel.SiteFactor

/-- `Ω` restricted to the primes of `S` up to `y`, with multiplicity. -/
def omegaMultLe (S : ℕ → Prop) [DecidablePred S] (y n : ℕ) : ℕ :=
  ∑ p ∈ (n.primeFactors.filter S).filter (fun p => p ≤ y), n.factorization p

/-- `Δ(f, x; e, c) = ∑_{n≤x, n≡c (e)} f(n) − (1/φ(e)) ∑_{n≤x, (n,e)=1} f(n)`. -/
noncomputable def apDiscrepancy (f : ℕ → ℂ) (x e c : ℕ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % e = c % e), f n)
    - (1 / (Nat.totient e : ℂ)) * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => Nat.Coprime n e), f n

/-- **Bombieri–Vinogradov for `z^{Ω_{P,≤y}}`, moduli coprime to `q₀` (cited, AUDIT PENDING).**
Source: A. Granville, X. Shao, *When does the Bombieri–Vinogradov theorem hold for a given
multiplicative function?*, Forum Math. Sigma (2018), arXiv:1706.05710, Theorem 2.1, which is
uniform in an `x`-dependent `f` in the class `C` (`|Λ_f| ≤ Λ`; `z^{Ω}` is completely
multiplicative and 1-bounded, so it qualifies).  Its hypothesis (2.1) is classical BV for primes
in `P`, i.e. primes `≡ a` mod `q₀·e`.
⚠️ Faithfulness is NOT yet audited.  Theorem 2.1 is stated for `Ξ = {1}`, and `z^{Ω_P}`
correlates with characters mod `q₀`, so the Siegel–Walfisz hypothesis fails at moduli sharing a
factor with `q₀`.  The paper calls the `Ξ`-modification straightforward and states it for
Theorems 2.2–2.3 only.  Restricting to `(e, q₀) = 1` removes those characters from `Ξ_e`; that
step is ours.  `y = x` gives the full function. -/
def GranvilleShaoBVResidue : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ z : ℂ, ‖z‖ = 1 → ∀ A : ℝ, 0 < A →
    ∃ B C : ℝ, 0 < C ∧ ∀ x y : ℕ, 2 ≤ x →
      ∑ e ∈ (Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊).filter (fun e => Nat.Coprime e q₀),
        ⨆ c : {c : Fin e // Nat.Coprime c.val e},
          ‖apDiscrepancy (fun n => z ^ omegaMultLe (residueClass q₀ a) y n) x e c.val.val‖
        ≤ C * x / Real.log x ^ A

end NormalNumbers.Literature
