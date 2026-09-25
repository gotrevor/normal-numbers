import NormalNumbers.ElliottLadder

/-!
# The genuinely *multiplicative* form of Tao's two-point log-Elliott theorem

`DIRECTION.md` fidelity gap, registered at lap 83.  The dependency's
`Erdos67b.IsMultiplicativeOnPositiveInt` carries **no** coprimality hypothesis, so it is
*complete* multiplicativity on positive integers; consequently the proved headline
`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott` is Tao 2016 Theorem 1.3 restricted to
completely multiplicative `g₁, g₂`.  Tao's theorem is for merely multiplicative `gᵢ`.

This file owns the `src/`-side statement of the honest form.

* `IsCoprimeMultOnPosInt` — `g 1 = 1` together with `g(mn) = g m · g n` for **coprime** positive
  `m, n`.  Strictly weaker than the dependency's predicate (`of_isMultiplicative`).
* `NonasymptoticLogElliottMult` — verbatim `Erdos67b.NonasymptoticLogElliott` with the two
  multiplicativity hypotheses weakened to `IsCoprimeMultOnPosInt`.  Note the direction: the
  hypothesis is weaker, so this `Prop` is **stronger**, and
  `NonasymptoticLogElliottMult → Erdos67b.NonasymptoticLogElliott` is free
  (`NonasymptoticLogElliottMult.toCompletelyMultiplicative`).

The dependency's `Prop` and the proved `nonasymptoticLogElliott` are left untouched.
-/

namespace NormalNumbers.ElliottMultStatement

open Erdos67b

/-- Multiplicativity on positive integers in the honest, *coprime* sense. -/
def IsCoprimeMultOnPosInt (g : ℤ → ℂ) : Prop :=
  g 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n →
      g ((m * n : ℕ) : ℤ) = g m * g n

/-- Complete multiplicativity implies the coprime form. -/
theorem IsCoprimeMultOnPosInt.of_isMultiplicative {g : ℤ → ℂ}
    (hg : IsMultiplicativeOnPositiveInt g) : IsCoprimeMultOnPosInt g :=
  ⟨hg.1, fun m n hm hn _ => hg.2 m n hm hn⟩

/-- **Tao 2016, Theorem 1.3**, in plby's finitary formulation, for merely multiplicative `gᵢ`. -/
def NonasymptoticLogElliottMult : Prop :=
  ∀ (a₁ a₂ : ℕ) (b₁ b₂ : ℤ),
    0 < a₁ → 0 < a₂ → (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ g₁ g₂ : ℤ → ℂ,
            IsCoprimeMultOnPosInt g₁ →
            IsCoprimeMultOnPosInt g₂ →
            (∀ n : ℤ, ‖g₁ n‖ ≤ 1) →
            (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
            (∀ q : ℕ, 0 < q → q ≤ A →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                |t| ≤ (A : ℝ) * X →
                  (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X) →
            ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤
              ε * Real.log W

/-- The mult form is stronger: it specialises to the dependency's completely multiplicative
`Prop`. -/
theorem NonasymptoticLogElliottMult.toCompletelyMultiplicative
    (h : NonasymptoticLogElliottMult) : NonasymptoticLogElliott := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
  obtain ⟨A₀, hA₀, hmain⟩ := h a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX g₁ g₂ hm₁ hm₂ h₁ h₂ hpret
  exact hmain A X W hA hAW hWX g₁ g₂
    (IsCoprimeMultOnPosInt.of_isMultiplicative hm₁)
    (IsCoprimeMultOnPosInt.of_isMultiplicative hm₂) h₁ h₂ hpret

end NormalNumbers.ElliottMultStatement
