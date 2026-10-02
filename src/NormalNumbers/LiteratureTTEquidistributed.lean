/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTTThm31
import NormalNumbers.Erdos257

/-!
# Tao–Teräväinen Theorem 3.1(i), the equidistributed case (cited input)

Tao, Teräväinen, *Quantitative correlations and some problems on prime factors of consecutive
integers*, arXiv:2512.01739, Theorem 3.1 case (i).  Tier P: read from the PDF on 2026-10-02 and
checked against the transcription in `docs/ERDOS257-BASE2-SUBSET-AUDIT-2026-10-02.md` §2a.
Shape mirrors case (ii), `CastingOut.TwoPointNaturalCorrelation` (`C3MrtTTThm31.lean`).

Faithful-or-weaker:
* the `O(N L^{−1})` of (3.1) is pinned to constant `1` (a stronger hypothesis);
* (3.1) is demanded for every modulus `q ≥ 1`, as in the paper ("for all `a, q ∈ ℕ`");
* the shifts are `0 ≤ h ≤ L^c` and the residue `b` is a natural (the paper: integers `O(L^c)`);
* the conclusion is claimed only at natural `N`.

Consumer: the base-2 campaign for Erdős #257 on prime subsets, `Erdos257Base2.lean`.
-/

namespace NormalNumbers.CastingOut

/-- **Tao–Teräväinen arXiv:2512.01739, Theorem 3.1(i)** (equidistributed case).  `g₁` real-valued,
quantitatively equidistributed in every residue class with mean `δ_N` at every scale
`X^{0.4} ≤ N ≤ X`, and `g₁(p) = 1` for `exp(log^{1/11} X) ≤ p ≤ exp(log^{1/10} X)`; then the
centred two-point correlation is `≪ L^{−c}` outside a set of scales of logarithmic density
`≪ L^{−c}`. -/
def TTEquidistributedCorrelation : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Icc (Real.sqrt X) X ∧
          (∫ t in E, t⁻¹) ≤ Cst * L ^ (-c) * Real.log X ∧
          ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X → (N : ℝ) ∉ E →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / (N : ℝ) : ℝ) •
                  ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                    (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
                ≤ Cst * L ^ (-c)

end NormalNumbers.CastingOut
