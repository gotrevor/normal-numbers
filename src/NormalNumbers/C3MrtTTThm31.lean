/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultChase

/-!
# Tao–Teräväinen Theorem 3.1(ii), stated faithfully — and what it does and does not give

Source: T. Tao, J. Teräväinen, *Quantitative correlations and prime factors*, arXiv 2512.01739,
Theorem 3.1 (`papers/tao-teravainen-2025-quantitative-correlations.txt:1566`).  Case (ii), the
non-pretentious case, is the one the C3/MRT route wants: `δ_N = 0`, so the conclusion is a bound
on the bare two-point correlation.

Verbatim (case (ii)):

> Let `X ≥ 2`.  Suppose `g₁, g₂ : ℕ → ℂ` are 1-bounded multiplicative.  Let `1 ≤ L ≤ log X`.
> Suppose `δ_N = 0` for all `X^{0.4} ≤ N ≤ X`, and `exp(M(g₁; X², log^{1/125} X)) ≫ L`.
> Let `c > 0` be a sufficiently small absolute constant.  Then there is `E ⊂ [√X, X]` with
> `(1/log X) ∫_E dt/t ≪ L^{-c}` such that for any `W ≤ L^c` and integers `b, h₁, h₂ = O(L^c)`
> with `h₁ ≠ h₂`,
>     `(W/N) ∑_{N<n≤2N, n ≡ b (mod W)} g₁(n+h₁) g₂(n+h₂)  ≪  L^{-c}`
> for all `N ∈ [√X, X] \ E`.

## What is formalised here

* `IsCoprimeMultiplicativeNat` — the `ℕ`-side of `IsCoprimeMultiplicativeInt`; `zOmegaNat z`
  satisfies it (`isCoprimeMultiplicativeNat_zOmegaNat`).
* `ttPretentiousSum g X t` — the inner sum of TT's `M(g; X², log^{1/125} X)`, a sum over the
  primes `p ≤ X²` of `(1 − Re(g(p) p^{-it}))/p`; and `TTNonPretentious g X L`, hypothesis (3.3)
  in the "for all admissible `t`" form (equivalent to the stated infimum bound).
* **`TwoPointNaturalCorrelation`** — Theorem 3.1(ii) itself, exceptional set and all, with the
  logarithmic density bound stated as a genuine integral `∫_E t⁻¹`.
* `c3_two_point_natural_of_TT` — the instantiation the route needs: `h₁ = 1`, `h₂ = 2`,
  `W = M₀`, `b = r`, `g_i = z_i^ω`, which turns TT's conclusion into a bound on the
  **natural** dyadic average of the C3 two-point correlation along the class of `r` mod `M₀`.

## The honest ledger entry — TT 3.1 does NOT discharge `LogToNaturalCorrelation 2`

`LogToNaturalCorrelation K` asks for `Tendsto … atTop (𝓝 0)` — convergence along **every**
scale.  Theorem 3.1 delivers the bound only for `N ∉ E`, and a set of logarithmic density
`o(1)` may still contain a whole dyadic block `[A, A^{1+δ}]` (log-mass `δ log A`, a positive
proportion of `log X` when `A = X^{1/2}`).  So no pointwise limit follows, and this is exactly
what TT say in print (`:2997`): removing the exceptional set is out of reach.

The consequence for the ledger is precise, and it is an *improvement*, not a defeat: the
`D = 2` row should be re-stated as a **scale-exceptional** natural-density rung.  That
variant is a published theorem; the unconditional one is not.  See `PENDING_WORK.md`, lap 62.
-/

open Finset MeasureTheory

namespace NormalNumbers

namespace CastingOut

/-! ## The `ℕ`-side hypothesis class -/

/-- Multiplicativity on coprime arguments, on `ℕ` — TT's "1-bounded multiplicative" together
with `norm_le_one`. -/
def IsCoprimeMultiplicativeNat (g : ℕ → ℂ) : Prop :=
  g 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → g (m * n) = g m * g n

/-- `z^ω` as a function on `ℕ`. -/
noncomputable def zOmegaNat (z : ℂ) : ℕ → ℂ := fun n => z ^ omegaNat n

@[simp] lemma zOmegaNat_apply (z : ℂ) (n : ℕ) : zOmegaNat z n = z ^ omegaNat n := rfl

theorem isCoprimeMultiplicativeNat_zOmegaNat (z : ℂ) :
    IsCoprimeMultiplicativeNat (zOmegaNat z) := by
  refine ⟨by simp [zOmegaNat, omegaNat], fun m n hm hn hmn => ?_⟩
  simp only [zOmegaNat]
  rw [omegaNat_mul_coprime_pos hm hn hmn, pow_add]

theorem norm_zOmegaNat_le_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖zOmegaNat z n‖ ≤ 1 := by
  simp [zOmegaNat, norm_pow, hz]

/-! ## TT's pretentious distance and hypothesis (3.3) -/

/-- The inner sum of TT's `M(g; X², log^{1/125} X)`: over primes `p ≤ X²`,
`∑ (1 − Re(g(p) p^{-it}))/p`. -/
noncomputable def ttPretentiousSum (g : ℕ → ℂ) (X : ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime,
    (1 - (g p * Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re) / (p : ℝ)

/-- **TT (3.3)**, the non-pretentiousness hypothesis of Theorem 3.1(ii):
`exp(M(g; X², log^{1/125} X)) ≫ L`.  Stated as a bound valid for every admissible `t`, which
is equivalent to the bound on the infimum over `|t| ≤ log^{1/125} X`. -/
def TTNonPretentious (g : ℕ → ℂ) (X L : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
    A * L ≤ Real.exp (ttPretentiousSum g X t)

/-! ## Theorem 3.1(ii) -/

/-- **Tao–Teräväinen arXiv 2512.01739, Theorem 3.1(ii)** — the quantitative two-point
correlation estimate for 1-bounded multiplicative functions, in natural (dyadic) averaging,
with a progression built in and an exceptional set of scales of logarithmic density `≪ L^{-c}`.

`c` and the implied constants are the absolute constants of the statement; `δ_N = 0` in case
(ii), so the correlation appears bare. -/
def TwoPointNaturalCorrelation : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
        TTNonPretentious g₁ X L →
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Icc (Real.sqrt X) X ∧
          (∫ t in E, t⁻¹) ≤ Cst * L ^ (-c) * Real.log X ∧
          ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X → (N : ℝ) ∉ E →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / (N : ℝ) : ℝ) •
                  ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                    g₁ (n + h₁) * g₂ (n + h₂)‖
                ≤ Cst * L ^ (-c)

/-! ## The instantiation the C3/MRT route needs -/

/-- **The C3 two-point correlation, natural-density, outside an exceptional set of scales.**
Theorem 3.1(ii) applied with `g_i = z_i^ω`, `h₁ = 1`, `h₂ = 2`, `W = M₀`, `b = r`.  The
summand is literally the `K = 2` summand of the campaign's correlation, in the *original*
variable `n` with the *natural* weight `1`.

This is what the log-averaged chain (`progression_log_rung_class_mult`) cannot give: the
saving here is `L^{-c}` over a dyadic window, not `ε log N` over an initial segment.  The price
is the scale-exceptional set `E`, which is why this does **not** yield
`LogToNaturalCorrelation 2`. -/
theorem c3_two_point_natural_of_TT (htt : TwoPointNaturalCorrelation)
    {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1) (X L : ℝ) (hX : 2 ≤ X)
    (hL1 : 1 ≤ L) (hLX : L ≤ Real.log X) (hnp : TTNonPretentious (zOmegaNat z₀) X L) :
    ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Icc (Real.sqrt X) X ∧
        (∫ t in E, t⁻¹) ≤ Cst * L ^ (-c) * Real.log X ∧
        ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X → (N : ℝ) ∉ E →
          ∀ Mo r : ℕ, 0 < Mo → (Mo : ℝ) ≤ L ^ c → (2 : ℝ) ≤ L ^ c →
            ‖((Mo : ℝ) / (N : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % Mo = r % Mo),
                  ∏ i : Fin 2, (![z₀, z₁] i) ^ omegaNat (n + (i : ℕ) + 1)‖
              ≤ Cst * L ^ (-c) := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := htt
  obtain ⟨E, hEmeas, hEsub, hElog, hEbd⟩ := hmain (zOmegaNat z₀) (zOmegaNat z₁)
    (isCoprimeMultiplicativeNat_zOmegaNat z₀) (isCoprimeMultiplicativeNat_zOmegaNat z₁)
    (norm_zOmegaNat_le_one hz₀) (norm_zOmegaNat_le_one hz₁) X L hX hL1 hLX hnp
  refine ⟨c, Cst, hc, hCst, E, hEmeas, hEsub, hElog, fun N hN1 hN2 hNE Mo r hMo hMoL h2L => ?_⟩
  have h1L : (1 : ℝ) ≤ L ^ c := le_trans (by norm_num) h2L
  have hspec := hEbd N hN1 hN2 hNE Mo r 1 2 hMo hMoL (by exact_mod_cast h1L)
    (by exact_mod_cast h2L) (by norm_num)
  refine le_trans (le_of_eq ?_) hspec
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fin.prod_univ_two]
  simp [zOmegaNat]

#print axioms IsCoprimeMultiplicativeNat
#print axioms TwoPointNaturalCorrelation
#print axioms c3_two_point_natural_of_TT

end CastingOut

end NormalNumbers
