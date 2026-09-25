import NormalNumbers.ElliottDilatedBridge
import NormalNumbers.ElliottDilatedLower

/-!
# Correlation transfer for the `a`-dilated prime graph

The dilated analogue of
`NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedGraph_sub_correlation_le`.

Lap 34 identified the dilated CRT sum, at the shifted residue, with a sum of affine graph
observables; lap 26 showed each such observable has log-mean `C/p` with the dependency's errors
plus one term for the backward base-point shift.  Putting the two together gives: **the dilated
graph average is the affine correlation `C` times an explicit weight**, with a totally explicit
error.

The weight is the dilated analogue of `Erdos67b.primeGraphCorrelationWeight`: the prime `p`
contributes `#{j < H : a j + (p c₁ mod a) + p h < H} / p`, i.e. about `H/(a p)` instead of `H/p`,
because only every `a`-th block position lies in the progression the dilated edge samples.  That
factor `a` is a constant, absorbed exactly as everywhere else in this campaign.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedCorrelation

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottAffineGraph
open NormalNumbers.ElliottGenericGraph
open NormalNumbers.ElliottDilatedBridge
open NormalNumbers.ElliottDilatedLower
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottLadder

noncomputable section

/-- The dilated correlation weight.  Compare `Erdos67b.primeGraphCorrelationWeight`. -/
def dilatedCorrelationWeight (H a c₁ h : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
    ((Finset.univ.filter (fun j : Fin H ↦ a * j.1 + (p.1 * c₁) % a + p.1 * h < H)).card : ℝ)
      / p.1 else 0

/-- **The complete dilated graph average.**  The dilated analogue of
`NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedGraph_sub_correlation_le`. -/
theorem norm_logProb_dilatedGraph_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    (H : ℕ) {a : ℕ} (ha : 0 < a) (c₁ h : ℕ) (s : Finset ℕ)
    {Dmax : ℕ} (hD : ∀ p : PrimeGraphIndex H, p.1 * c₁ / a ≤ Dmax) (hDL : Dmax ≤ L) :
    ‖logProbExpectation L U (fun n ↦
        genSum (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
          ((n : ZMod (primeGraphModulus H)) - crtShift H (fun p ↦ p * c₁ / a))) -
      dilatedCorrelationWeight H a c₁ h s •
        affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ ≤
      (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) +
          2 * Dmax / ((L : ℝ) * logProbMassNN L U)) := by
  classical
  set C := affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) with hC
  set e := 2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) +
    2 * Dmax / ((L : ℝ) * logProbMassNN L U) with he'
  have he : 0 ≤ e := by rw [he']; positivity
  have hdn : ∀ (n : ℕ), L ≤ n → ∀ p : PrimeGraphIndex H, p.1 * c₁ / a ≤ n :=
    fun n hn p ↦ ((hD p).trans hDL).trans hn
  -- the per-edge means
  let A (p : PrimeGraphIndex H) (j : Fin H) : ℂ :=
    logProbExpectation L U (fun n ↦
      affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a p.1 (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)
        (n + (j.1 + 1) - p.1 * c₁ / a))
  have hedge (p : PrimeGraphIndex H) (j : Fin H) : ‖A p j - (p.1 : ℝ)⁻¹ • C‖ ≤ e := by
    have hh := norm_logProb_affineTwistedObservable_shift_sub_correlation_le hL hLU
      (Nat.prime_of_mem_primesLE p.2).pos hm₁ hm₂ hu₁ hu₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)
      (j.1 + 1) (p.1 * c₁ / a) ((hD p).trans hDL)
    refine hh.trans ?_
    rw [he']
    have h1 : ((j.1 + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (by omega : j.1 + 1 ≤ H)
    have h2 : ((p.1 * c₁ / a : ℕ) : ℝ) ≤ (Dmax : ℝ) := by exact_mod_cast hD p
    have hM : (0 : ℝ) < logProbMassNN L U := by exact_mod_cast logProbMassNN_pos hL hLU
    have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
    gcongr
  have hexpect : logProbExpectation L U (fun n ↦
        genSum (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
          ((n : ZMod (primeGraphModulus H)) - crtShift H (fun p ↦ p * c₁ / a))) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then A p j else 0 else 0 := by
    have hpoint : ∀ n : LogProbIndex L U,
        genSum (pairTwist f₁ f₂)
          (dilatedEdgeReindexed (affineBlock f₁ a n.1 H) (affineBlock f₂ a n.1 H) a c₁ h) s
          ((n.1 : ZMod (primeGraphModulus H)) - crtShift H (fun p ↦ p * c₁ / a)) =
        ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
          ∑ j : Fin H, if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then
            affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a p.1 (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)
              (n.1 + (j.1 + 1) - p.1 * c₁ / a) else 0 else 0 := by
      intro n
      exact genSum_dilatedEdgeReindexed_affineBlock _ f₁ f₂ ha n.1 c₁ h s
        (hdn n.1 (mem_logProbWindow.mp n.2).1)
    have hcongr : logProbExpectation L U (fun n : ℕ ↦ genSum (pairTwist f₁ f₂)
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - crtShift H (fun p ↦ p * c₁ / a))) =
        logProbExpectation L U (fun n : ℕ ↦ ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
          ∑ j : Fin H, if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then
            affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a p.1 (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)
              (n + (j.1 + 1) - p.1 * c₁ / a) else 0 else 0) :=
      Finset.sum_congr rfl fun n _ ↦ by simp only [hpoint]
    rw [hcongr]
    rw [logProbExpectation_finset_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [logProbExpectation_finset_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : a * j.1 + (p.1 * c₁) % a + p.1 * h < H
      · simp only [hj, if_true]; rfl
      · simp [hj, logProbExpectation]
    · simp [hp, logProbExpectation]
  have hcoef : dilatedCorrelationWeight H a c₁ h s • C =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then
          (p.1 : ℝ)⁻¹ • C else 0 else 0 := by
    rw [dilatedCorrelationWeight, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        div_eq_mul_inv]
    · simp [hp]
  rw [hexpect, hcoef, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : PrimeGraphIndex H, ‖(if p.1 ∈ s then
        ∑ j : Fin H, if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then A p j else 0 else 0) -
      (if p.1 ∈ s then ∑ j : Fin H,
        if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0 else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (H : ℝ) * e := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      by_cases hp : p.1 ∈ s
      · simp only [hp, if_true, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ j : Fin H, ‖(if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then A p j else 0) -
              (if a * j.1 + (p.1 * c₁) % a + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ _j : Fin H, e := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            by_cases hj : a * j.1 + (p.1 * c₁) % a + p.1 * h < H
            · simpa only [hj, if_true] using hedge p j
            · simpa only [hj, if_false, sub_zero, norm_zero] using he
          _ = H * e := by simp
      · simp only [hp, if_false, sub_zero, norm_zero]
        positivity
    _ = (Nat.primeCounting H : ℝ) * H * e := by
      rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul, mul_assoc]

end

end NormalNumbers.ElliottDilatedCorrelation

#print axioms
  NormalNumbers.ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le
