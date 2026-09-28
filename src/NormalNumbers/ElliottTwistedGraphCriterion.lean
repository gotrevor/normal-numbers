import NormalNumbers.ElliottTwistedGraphCorrelation

/-!
# The finite graph criterion for the two-function case

Both halves of the crux's graph argument are now proved:

* upper — `exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`
  (`NormalNumbers.ElliottTwistedGraph`),
* lower — `exists_logProb_dyadic_pairTwistedMean_lower`
  (`NormalNumbers.ElliottTwistedGraphCorrelation`).

This file collides them, giving the port of
`Erdos67b.exists_logPairCorrelation_small_of_fourier_first_moments`: at a fixed shift, small enough
Fourier first moments **of `f₁` alone** force the two-function pair correlation to be small.

Three things make the collision go through with the dependency's constants:

1. The two halves speak about the same quantity.  The lower bound produces the CRT-indexed mean
   `pairTwistedMeanCRT`, the upper bound consumes the reciprocal-prime mean
   `pairTwistedPrimeGraphMean`; `pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean` identifies them
   once `dyadicPrimes P ⊆ Nat.primesLE H`, which the scale bookkeeping supplies.
2. The twist required by the upper bound is *any* family with `‖w p‖ ≤ 1`; the lower bound supplies
   the specific `pairTwist f₁ f₂`, which is unimodular on the active primes.
3. The lower bound's constant is `16` and the upper bound's is `32`, exactly as in the dependency, so
   the contradiction is the dependency's `linarith` step verbatim.

**The asymmetry of the hypothesis is visible in the statement**: the Fourier first-moment hypothesis
mentions `f₁` only.  `f₂` enters only through `‖blockFourier T (conj ∘ c) t‖ ≤ H` and Parseval inside
`norm_pairTwistedPrimeGraphMean_le_largeFrequencies`.  That is precisely why Tao's Theorem 1.3
assumes non-pretentiousness of `g₁` and nothing about `g₂`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-- The dyadic block chosen by the graph argument lies in the ambient CRT index set. -/
theorem dyadicPrimes_subset_primesLE {H h : ℕ} (hh : 0 < h) :
    PrimeEstimates.dyadicPrimes (H / (4 * h + 4)) ⊆ Nat.primesLE H := by
  intro p hp
  have hdiv : H / (4 * h + 4) * (4 * h + 4) ≤ H := Nat.div_mul_le_self H _
  have hPH : 2 * (H / (4 * h + 4)) ≤ H := by nlinarith
  have hp' := PrimeEstimates.mem_primesInInterval.mp hp
  exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩

/-- **The completed finite graph criterion for two independent functions.**  Port of
`Erdos67b.exists_logPairCorrelation_small_of_fourier_first_moments`.  The Fourier tolerance `ζ`
precedes the arbitrary minimum block scale, preserving the analytic parameter order, and the
first-moment hypothesis constrains `f₁` only. -/
theorem exists_pairLogCorrelation_small_of_fourier_first_moments
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ Hmin : ℕ,
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
        (∀ j < J, ∀ t ∈ Finset.range (4 * h * entropyScale H₀ j + 1),
          logProbExpectation L U (fun n ↦
            ‖blockFourier (4 * h * entropyScale H₀ j + 1)
              (finiteSequenceBlock f₁ (entropyScale H₀ j) n) (t : ℤ)‖) ≤ ζ * entropyScale H₀ j) →
        ‖pairLogCorrelation L U f₁ f₂ h‖ < η := by
  obtain ⟨ζ, hζ, H₁, hH₁, hupper⟩ :=
    exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment hh hη
  refine ⟨ζ, hζ, ?_⟩
  intro Hmin
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, hlower⟩ :=
    exists_logProb_dyadic_pairTwistedMean_lower hη h (max Hmin H₁)
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ hfirst
  by_contra hnot
  obtain ⟨j, hj, hlarge⟩ :=
    hlower L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ (le_of_not_gt hnot)
  set H := entropyScale H₀ j with hHdef
  have hH : H₁ ≤ H := ((le_max_right _ _).trans hmin).trans (le_entropyScale H₀ j)
  have hH2 : 2 ≤ H := hH₁.trans hH
  -- the twist is unimodular on every prime, in particular on the active block
  have hw : ∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖pairTwist f₁ f₂ p‖ ≤ 1 := by
    intro p hp
    have hppos : 0 < p := (Nat.prime_of_mem_primesLE (dyadicPrimes_subset_primesLE hh hp)).pos
    exact (norm_pairTwist hu₁ hu₂ hppos).le
  -- the lower bound's CRT mean is the upper bound's reciprocal-prime mean
  have hbridge : ∀ n : ℕ,
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) =
        pairTwistedPrimeGraphMean (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) :=
    fun n ↦ pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean _ _ _ _ _
      (dyadicPrimes_subset_primesLE hh)
  simp only [hbridge] at hlarge
  have hsmall := hupper H hH L U hL (by omega) f₁ f₂
    (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le) (pairTwist f₁ f₂) hw (hfirst j hj)
  have hlog := log_entropyScale_pos hH₀ j
  have hscale : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hpos : 0 < η * H / (32 * Real.log H) := by positivity
  have heq : η * H / (16 * Real.log H) = 2 * (η * H / (32 * Real.log H)) := by ring
  rw [heq] at hlarge
  linarith

end

end NormalNumbers.ElliottTwistedGraph
