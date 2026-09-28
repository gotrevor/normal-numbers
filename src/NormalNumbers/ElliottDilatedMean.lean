import NormalNumbers.ElliottDilatedWeight
import NormalNumbers.ElliottGenericGraphDecoupling

/-!
# Trading the dilated CRT sum for the uniform-residue mean

Step (i) of the dilated crux assembly.  The dilated analogue of
`NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedMean_sub_correlation_le`
(itself the port of `Erdos67b.norm_logProb_primeGraphMean_sub_correlation_le`).

Two proved rungs meet here:

* `NormalNumbers.ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le` (lap 35) —
  the dilated graph **sum**, tested at the shifted residue, is the affine correlation times
  `dilatedCorrelationWeight`, with explicit errors;
* an entropy-decoupling hypothesis on
  `NormalNumbers.ElliottGenericGraph.genDiscrepancyAt` — the difference between that sum and the
  uniform-residue CRT mean.  `NormalNumbers.ElliottGenericGraph.exists_logProb_gen_decoupling`
  (lap 30) supplies exactly this, at `Δ m = crtShift H (fun p ↦ p * c₁ / a)`.

The output is stated on `NormalNumbers.ElliottDilatedPairing.dilatedPairTwistedMean`, the object
that `NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment`
bounds from above — the join is
`NormalNumbers.ElliottDilatedBridge.genMeanCRT_dilatedEdgeReindexed`.  So after this file the two
halves of the crux are inequalities about literally the same quantity, and all that remains is the
parameter choreography.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedMean

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottAffineGraph
open NormalNumbers.ElliottGenericGraph
open NormalNumbers.ElliottDilatedBridge
open NormalNumbers.ElliottDilatedLower
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottDilatedCorrelation

noncomputable section

/-- The per-`n` residue at which the dilated graph sum is tested: the CRT element whose
`p`-component is the backward base-point shift `⌊p c₁ / a⌋`. -/
abbrev dilatedShift (H a c₁ : ℕ) : ZMod (primeGraphModulus H) :=
  crtShift H (fun p ↦ p * c₁ / a)

/-- **Step (i) of the dilated crux: the CRT sum traded for the uniform-residue mean.**

Given any decoupling bound `e` on the centred dilated graph observable, the *mean* is the affine
correlation times `dilatedCorrelationWeight`, up to `e` plus the correlation-transfer error. -/
theorem norm_logProb_dilatedMean_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    {H a : ℕ} (ha : 0 < a) (c₁ h : ℕ) {s : Finset ℕ} (hs : s ⊆ Nat.primesLE H)
    {Dmax : ℕ} (hD : ∀ p : PrimeGraphIndex H, p.1 * c₁ / a ≤ Dmax) (hDL : Dmax ≤ L)
    {e : ℝ}
    (hdec : ‖logProbExpectation L U (fun n ↦
        genDiscrepancyAt (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
          ((n : ZMod (primeGraphModulus H)) - dilatedShift H a c₁))‖ ≤ e) :
    ‖logProbExpectation L U (fun n ↦
        dilatedPairTwistedMean (pairTwist f₁ f₂)
          (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h s) -
      dilatedCorrelationWeight H a c₁ h s •
        affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ ≤
      e + (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) +
          2 * Dmax / ((L : ℝ) * logProbMassNN L U)) := by
  have herr := norm_logProb_dilatedGraph_sub_correlation_le hL hLU hm₁ hm₂ hu₁ hu₂
    H ha c₁ h s hD hDL
  -- the CRT mean is the Fourier mean the upper bound consumes
  have hmean : logProbExpectation L U (fun n ↦
      dilatedPairTwistedMean (pairTwist f₁ f₂)
        (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h s) =
      logProbExpectation L U (fun n ↦
        genMeanCRT (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s) :=
    Finset.sum_congr rfl fun n _ ↦ by
      dsimp only
      rw [genMeanCRT_dilatedEdgeReindexed _ _ _ ha c₁ h s hs]
  -- the decoupling hypothesis, unfolded
  have hdec' : ‖logProbExpectation L U (fun n ↦
      genSum (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - dilatedShift H a c₁)) -
      logProbExpectation L U (fun n ↦
        genMeanCRT (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s)‖ ≤ e := by
    have hsub := logProbExpectation_sub (E := ℂ) L U
      (fun n : ℕ ↦ genSum (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - dilatedShift H a c₁))
      (fun n : ℕ ↦ genMeanCRT (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s)
    rw [← hsub]
    simpa only [genDiscrepancyAt] using hdec
  rw [hmean]
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U (fun n ↦
      genMeanCRT (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s))
    (logProbExpectation L U (fun n ↦
      genSum (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - dilatedShift H a c₁)))
    (dilatedCorrelationWeight H a c₁ h s •
      affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ))
  rw [norm_sub_rev
    (logProbExpectation L U (fun n ↦
      genMeanCRT (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s))
    (logProbExpectation L U (fun n ↦
      genSum (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - dilatedShift H a c₁)))] at htri
  linarith

end

end NormalNumbers.ElliottDilatedMean

#print axioms NormalNumbers.ElliottDilatedMean.norm_logProb_dilatedMean_sub_correlation_le
