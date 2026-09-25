import NormalNumbers.ElliottDilatedSelect
import NormalNumbers.ElliottDilatedUpperMirror

/-!
# The mirrored dilated graph criterion

`NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment_snd`
places the Fourier first-moment hypothesis on the *second* block.  Feeding it into the collision of
`NormalNumbers.ElliottDilatedSelect.exists_logProb_dyadic_dilatedMean_lower` (which is symmetric in
the two functions and needs no mirror) gives the mirrored dilated graph criterion: small Fourier
first moments of the dilated blocks of `conj ∘ f₂` alone force the affine pair correlation to be
small.

Everything else — the lower bound, the entropy selection, the parameter collision — is verbatim the
un-mirrored argument.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottDilatedSelect

open Erdos67b
open Erdos67b.FiniteEntropy
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottAffineGraph
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottDilatedUpper

noncomputable section

theorem exists_affineLogCorrelation_small_of_fourier_first_moments_snd
    {a : ℕ} (ha : 0 < a) (c₁ : ℕ) {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ Hmin : ℕ,
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ a ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
        (∀ j < J, ∀ t : ℤ, logProbExpectation L U (fun n ↦
          ‖blockFourier (a * (4 * h * (a * entropyScale H₀ j) + 1))
            (affineBlock (fun m ↦ conj (f₂ m)) a n (a * entropyScale H₀ j)) t‖) ≤
            ζ * (a * entropyScale H₀ j : ℕ)) →
        ‖affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ < η := by
  obtain ⟨ζ, hζ, H₁, hH₁, hupper⟩ :=
    exists_dilatedPairTwistedMean_small_of_fourier_first_moment_snd (c₁ := c₁) hh ha
      (show 0 < η / (2 * a) by
        have : (0 : ℝ) < a := Nat.cast_pos.mpr ha
        positivity)
  refine ⟨ζ, hζ, ?_⟩
  intro Hmin
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hH₀a, hJ, hL₀, hW₀, hlower⟩ :=
    exists_logProb_dyadic_dilatedMean_lower hη ha c₁ hh (max Hmin H₁)
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hH₀a, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ hfirst
  by_contra hnot
  obtain ⟨j, hj, hlarge⟩ :=
    hlower L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ (le_of_not_gt hnot)
  set m := entropyScale H₀ j with hmdef
  set H := a * m with hHdef
  have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
  have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
  have hH : H₁ ≤ H := (((le_max_right _ _).trans hmin).trans hmH₀).trans hmH
  have hH2 : 2 ≤ H := hH₁.trans hH
  have har : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hHr : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlogH : 0 < Real.log ((H : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hw : ∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)),
      ‖pairTwist f₁ f₂ p‖ ≤ 1 := by
    intro p hp
    have hppos : 0 < p := (PrimeEstimates.mem_primesInInterval.mp hp).2.2.pos
    exact (norm_pairTwist hu₁ hu₂ hppos).le
  have hsmall := hupper H hH L U hL (by omega : L ≤ U) f₁ f₂
    (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le) (pairTwist f₁ f₂) hw
    (fun t ↦ hfirst j hj t)
  have hgap : η / (2 * a) * (H : ℝ) / (32 * Real.log ((H : ℕ) : ℝ)) <
      η * (H : ℝ) / (32 * a * Real.log ((H : ℕ) : ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hkey : (0 : ℝ) < η * (H : ℝ) * Real.log ((H : ℕ) : ℝ) := by positivity
    have hLs : η / (2 * a) * (H : ℝ) * (32 * a * Real.log ((H : ℕ) : ℝ)) =
        16 * (η * (H : ℝ) * Real.log ((H : ℕ) : ℝ)) := by
      field_simp
      ring
    have hRs : η * (H : ℝ) * (32 * Real.log ((H : ℕ) : ℝ)) =
        32 * (η * (H : ℝ) * Real.log ((H : ℕ) : ℝ)) := by ring
    rw [hLs, hRs]
    linarith
  have hcast : ((H : ℕ) : ℝ) = (H : ℝ) := rfl
  linarith [hlarge, hsmall, hgap]

end

end NormalNumbers.ElliottDilatedSelect

#print axioms
  NormalNumbers.ElliottDilatedSelect.exists_affineLogCorrelation_small_of_fourier_first_moments_snd
