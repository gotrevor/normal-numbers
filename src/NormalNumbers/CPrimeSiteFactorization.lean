/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeQuantStatement
import BoundedGaps.BombieriVinogradov.Statement
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

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

Literature inputs: `Literature.GranvilleShaoCor71` (Bombieri–Vinogradov for multiplicative
functions), `BoundedGaps.Maynard.bombieriVinogradov` (classical), `Literature.SelbergDelangeResidue`,
`Literature.SelbergUpperTwoForms`.  The believed wiring theorems (`sorry`, with confidence and
evidence) are at the end.  Paper statement, mechanism and the
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
`C (1 + log|h|)^m (e^{−u/2} + δ/√u)`, with `C, m` uniform in `h`, the modulus and `u`.
(Referee 2026-10-01: the constant must be polylog in `h`, chosen before `h`, or Erdős–Turán
cannot sum it.) -/
def SiteFactorization : Prop :=
  ∃ u₀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ, h ≠ 0 →
    ∀ q a : ℕ, 3 ≤ q → Nat.Coprime a q → ∀ u : ℕ, u₀ ≤ u → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖freshOneSite (residueClass q a) (winJ N) (cutU u N (winJ N)) h N
        - windowMeanLeG (residueClass q a) (winJ N) (cutU u N (winJ N)) h N
          * siteG (1 / (Nat.totient q : ℝ)) h (winJ N) u‖
        ≤ C * (1 + Real.log |(h : ℝ)|) ^ m
            * (Real.exp (-(u : ℝ) / 2) + 1 / ((Nat.totient q : ℝ) * Real.sqrt u)) + ε

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
discrepancy `≤ C log⁵φ(q)/φ(q)²`, uniformly in the unit `a`.  (`log⁵`, not `log³`: the weighted
fresh mass is `ρ(k_h log u + k_h² + log u)`, its square is `ρ²L⁴`, and Erdős–Turán adds one `L`;
referee 2026-10-01.) -/
def CPrimeResidueQuad : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q a : ℕ, q₀ ≤ q → Nat.Coprime a q →
    OrbitDefectLe (PrimeLambert.subsetLambert (residueClass q a) 4)
      (C * Real.log (Nat.totient q) ^ 5 / (Nat.totient q : ℝ) ^ 2)

end NormalNumbers.PrimeModel.SiteFactor

namespace NormalNumbers.Literature

open Filter Topology

/-- Granville–Shao's class `C`: `f(1) = 1` and `f·log = Λ_f ∗ f` with `|Λ_f(n)| ≤ Λ(n)`, i.e.
`−F'/F = ∑ Λ_f(n) n^{−s}` with `|Λ_f| ≤ Λ`.  This forces `|f| ≤ 1` and an Euler product.  Every
1-bounded completely multiplicative function is in `C`. -/
def InClassC (f : ℕ → ℂ) : Prop :=
  f 1 = 1 ∧ ∃ Λf : ℕ → ℂ, (∀ n, ‖Λf n‖ ≤ ArithmeticFunction.vonMangoldt n) ∧
    ∀ n, 1 ≤ n → f n * Real.log n = ∑ d ∈ n.divisors, Λf d * f (n / d)

/-- `Δ_A(f, x; q, a)`, with `A` the primitive characters of conductor `≤ D`:
`∑_{n≤x, n≡a (q)} f(n) − (1/φ(q)) ∑_{χ mod q, cond χ ≤ D} χ̄(a) ∑_{n≤x} f(n)χ(n)`.
The principal character has conductor `1`, so `D ≥ 1` contains the usual `Δ`.  (GS print
`χ(a)`; orthogonality needs `χ̄(a)` with their `S_f(x, χ) = ∑ f(n)χ(n)`.) -/
noncomputable def apDiscrepancyChar (f : ℕ → ℂ) (x q a : ℕ) (D : ℝ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q), f n)
    - (1 / (Nat.totient q : ℂ)) *
      ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => (χ.conductor : ℝ) ≤ D)),
        (starRingEnd ℂ) (χ (a : ZMod q)) * ∑ n ∈ Finset.Icc 1 x, f n * χ (n : ZMod q)

/-- `∑_{q≤Q} max_{(a,q)=1} |Δ_A(f, x; q, a)|`. -/
noncomputable def bvSumChar (f : ℕ → ℂ) (x Q : ℕ) (D : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ⨆ a : {a : Fin q // Nat.Coprime a.val q},
    ‖apDiscrepancyChar f x q a.val.val D‖

/-- **Granville–Shao, Corollary 7.1 (cited).**  A. Granville, X. Shao, *When does the
Bombieri–Vinogradov theorem hold for a given multiplicative function?*, Forum Math. Sigma 6
(2018), arXiv:1706.05710v1, §7, Corollary 7.1.  Fix `A ≥ 0`, `B > A + 5`, `γ > 2A + 6`; put
`Q = x^{1/2}/(log x)^B`, `y = x/(log x)^γ`, `A` = primitive characters of conductor
`≤ (log x)^B`.  If `f ∈ C` and `∑_{q≤Q} max |Δ_A(f·1_P, X; q, a)| ≪ x/((log x)^A log(x/y))` for
all `y ≤ X ≤ x`, then `∑_{q≤Q} max |Δ_A(f, x; q, a)| ≪ x/(log x)^A`.  No Siegel–Walfisz
hypothesis: the characters it would control are subtracted in `Δ_A`.  Uniform in an
`x`-dependent `f` (the point of the paper's §2).
Transcription: the implied constant of the conclusion depends on `A, B, γ` and the hypothesis's
constant `K`; real `X ∈ [y, x]` becomes natural `X ≥ ⌊y⌋` (the sums only see `⌊X⌋`); a
threshold `x₀` is allowed (weaker). -/
def GranvilleShaoCor71 : Prop :=
  ∀ A B γ : ℝ, 0 ≤ A → A + 5 < B → 2 * A + 6 < γ → ∀ K : ℝ, 0 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ f : ℕ → ℂ, InClassC f →
      (∀ X : ℕ, ⌊(x : ℝ) / Real.log x ^ γ⌋₊ ≤ X → X ≤ x →
        bvSumChar (fun n => if n.Prime then f n else 0) X ⌊Real.sqrt x / Real.log x ^ B⌋₊
            (Real.log x ^ B)
          ≤ K * x / (Real.log x ^ A * Real.log ((x : ℝ) / ((x : ℝ) / Real.log x ^ γ)))) →
      bvSumChar f x ⌊Real.sqrt x / Real.log x ^ B⌋₊ (Real.log x ^ B) ≤ C * x / Real.log x ^ A

/-- **Selberg–Delange for `z^{ω_P}`, `P` a residue class (cited corollary).**  Tenenbaum,
*Introduction to Analytic and Probabilistic Number Theory* (3rd ed.), Thm II.5.2 with `N = 0`,
applied to `F(s) = ∑ z^{ω_P(n)} n^{−s} = ζ(s)^{1+κ} G(s)`, `κ = (z − 1)/φ(q₀)`.  Here
`G = ∏_{χ mod q₀} L(s, χ)^{c_χ} × (absolutely convergent)` is holomorphic in a fixed zero-free
region; for fixed `q₀` a possible exceptional zero sits at a fixed distance from `1`.  Main term
`x (log x)^κ G(1)/Γ(1+κ)`, relative error `O(1/log x)`.  `G(1)` is the limit of the partial
Euler products `∏_{p≤X} (1 − 1/p)^{1+κ}(1 + f(p)/(p − 1))`, by Mertens in progressions.
⚠️ Instantiating the class `P(z; c₀, δ, M)` hypotheses is OUR step (unaudited), as is the
Euler-product identification of `G(1)`.  At a pole of `Γ(1+κ)` Mathlib's `Γ = 0` gives main term
`0`, matching `1/Γ` entire.  The constant is uniform on `|z| = 1` (II.5.2 is uniform for
`|z| ≤ A`); the wiring uses infinitely many `z_k`. -/
def SelbergDelangeResidue : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ = 1 →
    ∃ L₀ : ℂ,
      Tendsto (fun X : ℕ => ∏ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
        (1 - 1 / (p : ℂ)) ^ (1 + (z - 1) / (Nat.totient q₀ : ℂ)) *
          (1 + (if p % q₀ = a % q₀ then z else 1) / ((p : ℂ) - 1))) atTop (𝓝 L₀) ∧
      ∀ x : ℕ, 3 ≤ x →
        ‖(∑ n ∈ Finset.Icc 1 x,
              z ^ ((n.primeFactors.filter (fun p => p % q₀ = a % q₀)).card)) / (x : ℂ)
          - L₀ * (Real.log x : ℂ) ^ ((z - 1) / (Nat.totient q₀ : ℂ))
              * (Complex.Gamma (1 + (z - 1) / (Nat.totient q₀ : ℂ)))⁻¹‖
        ≤ C * Real.log x ^ (((z - 1) / (Nat.totient q₀ : ℂ)).re - 1)

/-- **Upper-bound sieve for a prime pair in two linear forms (cited, weakened).**
Halberstam–Richert, *Sieve Methods* (1974), Theorem 3.12: for `(a, b) = 1`, `2 ∣ ab`,
`#{p ≤ x : ap + b prime} ≤ 8 ∏_{p>2}(1 − (p−1)⁻²) ∏_{2<p∣ab} (p−1)/(p−2) · x/log²x (1 + o(1))`.
Weakened here to an unspecified absolute constant times `(ab/φ(ab))²`, which dominates the
`ab`-product.  ⚠️ Theorem number recalled, not re-opened this session. -/
def SelbergUpperTwoForms : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → ∀ x : ℕ, 3 ≤ x →
    (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ (a * p + b).Prime)).card : ℝ)
      ≤ C * ((a * b : ℕ) / (Nat.totient (a * b) : ℝ)) ^ 2 * x / Real.log x ^ 2

end NormalNumbers.Literature

namespace NormalNumbers.PrimeModel.SiteFactor

open NormalNumbers.Literature

/-- `Ω` restricted to the primes of `S` up to `y`, with multiplicity. -/
def omegaMultLe (S : ℕ → Prop) [DecidablePred S] (y n : ℕ) : ℕ :=
  ∑ p ∈ (n.primeFactors.filter S).filter (fun p => p ≤ y), n.factorization p

/-- `Δ(f, x; e, c) = ∑_{n≤x, n≡c (e)} f(n) − (1/φ(e)) ∑_{n≤x, (n,e)=1} f(n)`. -/
noncomputable def apDiscrepancy (f : ℕ → ℂ) (x e c : ℕ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % e = c % e), f n)
    - (1 / (Nat.totient e : ℂ)) * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => Nat.Coprime n e), f n

/-- **BV for `z^{Ω_{P,≤y}}` at moduli coprime to `q₀` (derived, believed).**  The form
`SiteFactorization` consumes.  `y = x` gives the full function.  Plain `Δ` is right here: at
moduli coprime to `q₀` the only small-conductor characters `z^{Ω_P}` correlates with (those mod
`q₀`) are not induced, and `TwistedSiegelWalfisz` removes the rest. -/
def MultBVResidue : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ z : ℂ, ‖z‖ = 1 → ∀ A : ℝ, 0 < A →
    ∃ B C : ℝ, 0 < C ∧ ∀ x y : ℕ, 2 ≤ x →
      ∑ e ∈ (Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊).filter (fun e => Nat.Coprime e q₀),
        ⨆ c : {c : Fin e // Nat.Coprime c.val e},
          ‖apDiscrepancy (fun n => z ^ omegaMultLe (residueClass q₀ a) y n) x e c.val.val‖
        ≤ C * x / Real.log x ^ A

/-- **Siegel–Walfisz for twisted `z^{Ω_{P,≤y}}` (believed, open node).**  For a nonprincipal
character `χ` of modulus `r ≤ (log x)^B` coprime to `q₀`, `∑_{n≤x} z^{Ω_{P,≤y}(n)} χ(n) ≪_A
x/(log x)^A`, uniformly in `y`.  `χ·z^{Ω_P}` has Dirichlet series `∏_ψ L(s, χψ)^{c_ψ}`
(`ψ mod q₀`) with every `χψ` nonprincipal, so there is no pole at `s = 1`; with Siegel's theorem
the bound is ineffective but holds.  Uniformity in `y` is the part to check. -/
def TwistedSiegelWalfisz : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ z : ℂ, ‖z‖ = 1 → ∀ A B : ℝ, 0 < A → 0 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ x y r : ℕ, 3 ≤ x → 1 ≤ r → (r : ℝ) ≤ Real.log x ^ B →
      Nat.Coprime r q₀ → ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
        ‖∑ n ∈ Finset.Icc 1 x, z ^ omegaMultLe (residueClass q₀ a) y n * χ (n : ZMod r)‖
          ≤ C * x / Real.log x ^ A

/-- Believed, ~85% (statement).  English proof: Selberg–Delange with characters (Tenenbaum
II.5) plus Siegel's theorem for the `L(s, χψ)`.  ⚠️ The earlier sketch ("the `y`-truncation
changes `G` by a factor bounded uniformly in `y`") is WRONG (referee 2026-10-01):
`∑_{p≤y} p^{−σ}` on `σ = 1 − c/log T` blows up when `log y ≫ log T`.  A two-regime argument
(small `y`: the twist by `χ` acts on the `y`-rough part; large `y`: contour as for `y = x`) is
owed.  Evidence: none numerical; `y = x`, `z = 1` is Siegel–Walfisz, a theorem. -/
theorem twistedSiegelWalfisz : TwistedSiegelWalfisz := sorry

/-- Believed, ~80%.  English proof: GS Corollary 7.1 applies to `f = z^{Ω_{P,≤y}} ∈ C`
(completely multiplicative, 1-bounded).  Its hypothesis is BV for `f·1_P`: on primes `f` is
`1 + (z−1)·1[p ≡ a (q₀), p ≤ y]`, so `Δ_A(f·1_P; q)` is classical BV at modulus `lcm(q, q₀)`
(characters mod `q₀` are subtracted inside `Δ_A` when `q₀ ∣ q`), and the cutoff `p ≤ y` costs
two BV evaluations.  Then `Δ = Δ_A + ∑_{χ ∈ A_e, χ ≠ χ₀} χ̄(c) S_f(x, χ)/φ(e)`; for `(e, q₀) = 1`
each `χ` has conductor coprime to `q₀`, so `TwistedSiegelWalfisz` bounds it, and the sum over `e`
loses only `(log x)^{2B+1}`, absorbed by choosing `A` larger.  This replaces the 2026-10-01
first-draft citation of GS Theorem 2.1, whose Siegel–Walfisz hypothesis fails at moduli sharing a
factor with `q₀` (doc, open check (a): resolved this way). -/
theorem multBVResidue_of (h71 : GranvilleShaoCor71)
    (hBV : BoundedGaps.Maynard.bombieriVinogradov) (hTSW : TwistedSiegelWalfisz) :
    MultBVResidue := sorry

/-- ⚠️ **Believed ~15%: these hypotheses are probably INSUFFICIENT** (referee 2026-10-01).  The
statement `SiteFactorization` itself is believed ~75%.  The gap is **uniformity in the growing
window `J`**, which is the Maze wall "fixed-window conductor at depth" again (row "site factorization via
log-power BV").  The multi-site sieve feeding BV carries modulus multiplicity about
`(2J)^{ω(e)}`, so its loss is `(log N)^{O(δJ²)}`.  Cutting the sites only gets to
`J₁ ≳ log₄ log log N`, while BV saves a FIXED power `(log N)^{−A}`.  The `|w_j|`-weighted
divisor expansion that would give multiplicity `C_h^{ω(e)}` has no level control.  Needed: BV
for `z^{Ω_{P,≤y}}` with a super-polylog saving (e.g. `Δ_A` with conductors up to
`exp(c√log x)` plus an exceptional-modulus excision), or a sieve with polylog `ℓ¹` mass at
growing depth.
Original sketch (doc §Mechanism): `T1'_k = mean[Φ^{≠k}(n)·(F − F_y)(n+k)]`;
sandwich C′'s CRT atoms (moduli `≤ N^{3/8}`) between fundamental-lemma sieves; BV for `F`,
`F_y` (`MultBVResidue`) handles each progression; main terms agree prime-by-prime except at
`q′ ∈ (y_k, y_j]` (cost `O(1/y_k)`); the global ratio `M[F]/M[F_y]` is
`SelbergDelangeResidue` over C′'s proved model mean (5.3), giving `siteFactor` up to
`O(e^{−u})`.  Step (b) has a working replacement: positivity of `λ⁺ − λ⁻` and the sup bound
`|F − F_y| ≤ min(2, |w_k| s_k)`, total `C_h u² e^{−u}`.  The atom modulus `Q` must be cut down to
the P-primes `≤ 2J`.  The frozen phase sees only P-primes, and those never divide `q₀`, so the
moduli stay coprime to `q₀`.
Evidence: at `a = 1, 0.5` (NOT the proof regime) the measured `G = T1/W_y` converges to the
analytic limit for residue classes, `2^20 → 2^26` (`probes/data-2026-10-01-cprime-analytic-G.md`).
Controls: `P = {101}` exact one-prime test, and `J = 1`, where the statement is an identity.
The probe has only `J = 5`, so it cannot see the growing-`J` gap. -/
theorem siteFactorization_of (hBV : MultBVResidue) (hSD : SelbergDelangeResidue) :
    SiteFactorization := sorry

/-- Believed, ~70%.  English proof: the left side lives on `n` with fresh primes at two sites,
`n + j = pm`, `n + j' = p′m′`; for fixed small cofactors the count of `p` is a prime pair in two
linear forms (`SelbergUpperTwoForms`, in progressions mod `q₀`), and summing `1/(m m′ log² )` over
the cofactor ranges gives the product of the two sites' fresh masses.  Pairs with `pp′ ≤ N` are
CRT-exact.  Evidence (`probes/data-2026-10-01-cprime-pair-second-order.md`):
- `|T2|/Fw² ∈ [0.007, 0.53]` over every set, `h ∈ {1, 3, 5}`, `a ∈ {1, 0.5}`, `N = 2^20…2^24`;
- it is stable in `N`, while `|T2|/ρ²` spans `[0.2, 40]` and grows with `h`;
- at fixed `N` it rises mildly with `q` (`0.18` at q = 3, `0.37` at q = 61), but falls with `N`
  for the sparsest classes.
Control: `P = {101, 103}` exact (`test_pair_second_order_ratio_exact`).  Not the proof regime. -/
theorem pairSecondOrder_of (h : SelbergUpperTwoForms) : PairSecondOrder := sorry

/-- Believed, ~70% given the two premises.  English proof (doc §Chain): `|W| ≤ |W_y|(1+|G_h|)
+ |T1' − W_y G_h| + |W − W_y − T1'|`; `|W_y| ≤ 4e^{−u} + o(1)` from C′ (5.3)–(5.4); take
`u = ⌈ρ⁻²⌉`, then Erdős–Turán with `H = ⌈ρ⁻²⌉`, which gives `ρ² log⁵(1/ρ)`.  C′'s (5.3)–(5.4)
need a deep-site truncation lemma under `winJ`: its `y_J < 2J`.  Cutting at `J₁ ≈ L3 N` costs
`4^{−J₁} δ log log N → 0`.  Shares the six build gaps of
`docs/CPRIME-QUANTITATIVE-2026-09-30.md` (Erdős–Turán, quantitative Weyl wiring, Mertens-AP
upper bound, …). -/
theorem cprimeResidueQuad_of (hSF : SiteFactorization) (hPair : PairSecondOrder) :
    CPrimeResidueQuad := sorry

end NormalNumbers.PrimeModel.SiteFactor
