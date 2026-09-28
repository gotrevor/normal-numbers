import NormalNumbers.ElliottTwistedGraphCriterion
import ErdosProblems.Erdos67b.ElliottComplete

/-!
# The pure-shift two-function rung

`ShiftCMLogElliott` is the exact two-function analogue of `Erdos67b.UnitCircleLogElliott`: two
*independent* completely multiplicative unimodular functions `f₁, f₂`, non-pretentiousness on `f₁`
alone, and the correlation `∑_{n} f₁(n) f₂(n+h) / n` over the logarithmic window.

**This rung carries the entire analytic content of the crux.**  The remaining step to
`NormalNumbers.ElliottLadder.DilatedCMLogElliott` is the affine bookkeeping for the common dilation
`a` and the integer shifts `c₁, c₂`, which involves no new analysis.

The proof is `Erdos67b.unitCircleLogElliott`'s assembly with two substitutions:

* the graph criterion `Erdos67b.exists_logPairCorrelation_small_of_fourier_first_moments` is replaced
  by `exists_pairLogCorrelation_small_of_fourier_first_moments` (proved over the previous five laps);
* the MRT input `Erdos67b.mrtModulatedShortIntervalUnrestricted` is used **unchanged**.  This is the
  audit conclusion of this lap: MRT is applied to `f₁` only, and everything downstream of it — the
  Fourier first-moment transfer `Erdos67b.logProb_fourier_firstMoment_of_MRT` and the window
  bookkeeping — mentions a single function.  So `f₂` costs nothing on the MRT side, matching the fact
  that the graph criterion's Fourier hypothesis constrains `f₁` alone.

The only genuinely new ingredient is `norm_shiftedPairLogCorrelation_le_trimmed`, the two-function
window-trimming bound; it comes straight from the dependency's function-agnostic
`Erdos67b.norm_elliottWindow_trim_error`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-- The two-function shifted logarithmic correlation.  Compare `Erdos67b.shiftedLogCorrelation`,
which is the `f₂ = conj f₁` case (`shiftedPairLogCorrelation_conj`). -/
def shiftedPairLogCorrelation (f₁ f₂ : ℕ → ℂ) (h X W : ℕ) : ℂ :=
  ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * f₁ n * f₂ (n + h)

@[simp]
theorem shiftedPairLogCorrelation_conj (f : ℕ → ℂ) (h X W : ℕ) :
    shiftedPairLogCorrelation f (fun n ↦ conj (f n)) h X W = shiftedLogCorrelation f h X W := rfl

/-- The general integer-affine correlation specialises to the two-function shifted correlation. -/
theorem elliottLogCorrelation_positiveIntExtension_pair (f₁ f₂ : ℕ → ℂ) (h X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) 1 1 0 h X W =
      shiftedPairLogCorrelation f₁ f₂ h X W := by
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hnpos := (mem_elliottLogWindow.mp hn).1
  have hnhpos : 0 < n + h := Nat.add_pos_left hnpos h
  simp only [integerAffine_one_zero, integerAffine_one_nat,
    positiveIntExtension_natCast hnpos, positiveIntExtension_natCast hnhpos]

/-- Two-function window trimming.  Port of `Erdos67b.norm_shiftedLogCorrelation_le_trimmed`. -/
theorem norm_shiftedPairLogCorrelation_le_trimmed
    {X W : ℕ} (hW : 0 < W) (L₀ h : ℕ) (f₁ f₂ : ℕ → ℂ)
    (h₁ : ∀ n, 0 < n → ‖f₁ n‖ = 1) (h₂ : ∀ n, 0 < n → ‖f₂ n‖ = 1) :
    ‖shiftedPairLogCorrelation f₁ f₂ h X W‖ ≤
      ‖∑ n ∈ Icc (elliottTrimmedLower X W L₀) X, (n : ℝ)⁻¹ • (f₁ n * f₂ (n + h))‖ + L₀ := by
  have herr := norm_elliottWindow_trim_error (X := X) hW L₀
    (fun n ↦ f₁ n * f₂ (n + h)) (by
      intro n hn
      rw [norm_mul, h₁ n hn, h₂ (n + h) (by omega)]
      norm_num)
  have heq : shiftedPairLogCorrelation f₁ f₂ h X W =
      ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ • (f₁ n * f₂ (n + h)) := by
    simp only [shiftedPairLogCorrelation, harmonicWeight, Complex.real_smul, mul_assoc]
  rw [heq]
  apply (norm_le_norm_add_norm_sub
    (∑ n ∈ Icc (elliottTrimmedLower X W L₀) X, (n : ℝ)⁻¹ • (f₁ n * f₂ (n + h))) _).trans
  apply add_le_add le_rfl
  simpa only [norm_sub_rev] using herr

/-! ## The rung -/

/-- **The pure-shift, two-function, completely multiplicative unimodular log-Elliott bound.**
The exact two-function analogue of `Erdos67b.UnitCircleLogElliott`. -/
def ShiftCMLogElliott : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ h : ℕ, 0 < h →
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ f₁ f₂ : ℕ → ℂ,
          IsCompletelyMultiplicativeOnPositive f₁ →
          IsCompletelyMultiplicativeOnPositive f₂ →
          (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
          (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
          MRTNonpretentious f₁ A X →
          ‖shiftedPairLogCorrelation f₁ f₂ h X W‖ ≤ ε * Real.log W

/-- **The two-function pure-shift rung is proved.**  `Erdos67b.unitCircleLogElliott`'s assembly with
the two-function graph criterion substituted; the MRT input is used verbatim because it only ever
sees `f₁`. -/
theorem shiftCMLogElliott : ShiftCMLogElliott := by
  intro ε hε h hh
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ζ, hζ, hgraph⟩ := exists_pairLogCorrelation_small_of_fourier_first_moments hh hη
  let δ : ℝ := ζ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Hmin, hHmin, hmrt⟩ := mrtModulatedShortIntervalUnrestricted δ hδ
  obtain ⟨H₀, J, L₀, M₀, hH₀min, hH₀, hJ, hL₀, hM₀, hgraphMain⟩ := hgraph Hmin
  let Hmax := max H₀ ((range J).sup (entropyScale H₀))
  have hHmax : Hmin ≤ Hmax := hH₀min.trans (le_max_left _ _)
  obtain ⟨N, hN, hmrtMain⟩ := hmrt Hmax hHmax
  obtain ⟨A₀, hA₀4, hA₀N, hA₀L, hthreshold⟩ := elliottExists_finalThreshold L₀ N M₀ hε
  refine ⟨A₀, by omega, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  have hA₀W : A₀ ≤ W := hA.trans hAW
  have hW4 : 4 ≤ W := hA₀4.trans hA₀W
  have hW : 0 < W := by omega
  obtain ⟨hlog, hmassThreshold, herror⟩ := hthreshold W hA₀W
  set L := elliottTrimmedLower X W L₀ with hLdef
  obtain ⟨hL, hLL, hLX⟩ := elliottTrimmedLower_geometry hW4 hWX
    (hA₀L.trans (hA₀W.trans hWX))
  obtain ⟨hMlo, hMhi⟩ := elliottTrimmedMass_bounds hW hWX hlog
  have hM : 0 < (logProbMassNN L X : ℝ) := by
    exact_mod_cast logProbMassNN_pos hL (by omega)
  have hcorr : ‖pairLogCorrelation L X f₁ f₂ h‖ < η := by
    apply hgraphMain L X hL hLX hLL (hmassThreshold.trans hMlo) f₁ f₂ hm₁ hm₂ hu₁ hu₂
    intro j hj t _ht
    have hHlo : Hmin ≤ entropyScale H₀ j := hH₀min.trans (le_entropyScale H₀ j)
    have hHhi : entropyScale H₀ j ≤ Hmax :=
      (Finset.le_sup (f := entropyScale H₀) (mem_range.2 hj)).trans (le_max_right _ _)
    have hfirst := hmrtMain A X W (entropyScale H₀ j) (hA₀N.trans hA) hAW hWX
      hHlo hHhi f₁ hm₁ hu₁ hpret ((t : ℝ) / (4 * h * entropyScale H₀ j + 1))
    have hbound := logProb_fourier_firstMoment_of_MRT hW
      (show 0 < entropyScale H₀ j by omega) hM hMlo hδ.le f₁
      (4 * h * entropyScale H₀ j + 1) (t : ℤ) (by
        simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          using hfirst)
    exact hbound.trans (by dsimp [δ]; nlinarith [Nat.cast_nonneg (α := ℝ) (entropyScale H₀ j)])
  rw [pairLogCorrelation, logProbExpectation_eq_mass_inv_smul_sum,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), inv_mul_eq_div] at hcorr
  have hsum := (div_lt_iff₀ hM).1 hcorr
  have htrim := norm_shiftedPairLogCorrelation_le_trimmed (X := X) hW L₀ h f₁ f₂ hu₁ hu₂
  calc
    ‖shiftedPairLogCorrelation f₁ f₂ h X W‖ ≤
        ‖∑ n ∈ Icc L X, (n : ℝ)⁻¹ • (f₁ n * f₂ (n + h))‖ + L₀ := htrim
    _ ≤ η * (logProbMassNN L X : ℝ) + L₀ := add_le_add hsum.le le_rfl
    _ ≤ η * (2 * Real.log W) + (ε / 2) * Real.log W :=
      add_le_add (mul_le_mul_of_nonneg_left hMhi hη.le) herror
    _ = ε * Real.log W := by dsimp [η]; ring

/-- Faithfulness anchor: the two-function pure-shift rung recovers the dependency's proved
unit-circle theorem. -/
theorem unitCircle_of_shiftCM (hshift : ShiftCMLogElliott) : UnitCircleLogElliott := by
  intro ε hε h hh
  obtain ⟨A₀, hA₀, hmain⟩ := hshift ε hε h hh
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f hmul hunit hpret
  have hconjMul : IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f n)) :=
    conj_isCompletelyMultiplicativeOnPositive hmul
  have hconjUnit : ∀ n : ℕ, 0 < n → ‖conj (f n)‖ = 1 := by
    intro n hn; rw [Complex.norm_conj]; exact hunit n hn
  have hres := hmain A X W hA hAW hWX f (fun n ↦ conj (f n)) hmul hconjMul hunit hconjUnit
    (fun q hq hqA χ t ht ↦ hpret q hq hqA χ t ht)
  rwa [shiftedPairLogCorrelation_conj] at hres

end

end NormalNumbers.ElliottTwistedGraph
