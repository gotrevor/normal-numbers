/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MediumPrimes
import NormalNumbers.G4RemainderW

/-!
# The §4D junk estimates for a sub-family of the medium primes

Every medium-range estimate of `G4MediumPrimes` is proved from *membership facts only*
(primality, coprimality to `P₀`, the good-prime separation, and the equidistribution of the
sample), so it holds verbatim for any subfamily `T ⊆ medPrimes R Y P₀` — in particular for
`(medPrimes R Y P₀).filter S`, which is the medium range of the prime-subset weight `ω_S`.

* `sum_sq_blockSum_sub_le` — the second moment for `T ⊆ medPrimes R Y P₀`;
* `sampleAvg_abs_blockSum_sub_le` — hence the first moment, against the *same* `medBudget`
  (the `S`-restricted sum of reciprocals and the `S`-restricted cardinality are both smaller).
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- **The medium-prime second moment for a subfamily.** -/
theorem sum_sq_blockSum_sub_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hK : 0 < G.K) (a : Fin G.K → Fin G.s) {T : Finset ℕ} (hT : T ⊆ medPrimes R Y G.P₀) :
    ∑ n ∈ apSample X G.P₀ G.b₀,
        blockSum bb G (fun m => (omegaOn T m : ℝ)) n a ^ 2
      ≤ (apSample X G.P₀ G.b₀).card * (∑ p ∈ T, (p : ℝ)⁻¹) * rowL2 bb G.K
        + 2 * (T.card : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 := by
  simp_rw [blockSum_omegaOn_eq]
  have hmain := sum_sq_block_le (apSample X G.P₀ G.b₀) T (rowCoeff bb G a)
    (shiftAL G.B G.Q G.D₀) (fun q => 0 < q ∧ q.Coprime G.P₀)
    (sum_rowCoeff_eq_zero bb G hK a)
    (fun p hp => (medPrimes_prime (hT hp)).pos)
    (fun p hp p' hp' hne =>
      (Nat.coprime_primes (medPrimes_prime (hT hp)) (medPrimes_prime (hT hp'))).2 hne)
    (fun p hp => ⟨(medPrimes_prime (hT hp)).pos,
      (Nat.Prime.coprime_iff_not_dvd (medPrimes_prime (hT hp))).2 (medPrimes_not_dvd (hT hp))⟩)
    (fun p hp p' hp' _ => ⟨Nat.mul_pos (medPrimes_prime (hT hp)).pos (medPrimes_prime (hT hp')).pos,
      Nat.Coprime.mul_left
        ((Nat.Prime.coprime_iff_not_dvd (medPrimes_prime (hT hp))).2 (medPrimes_not_dvd (hT hp)))
        ((Nat.Prime.coprime_iff_not_dvd (medPrimes_prime (hT hp'))).2
          (medPrimes_not_dvd (hT hp')))⟩)
    (fun p hp => sep_of_goodPrime _ (medPrimes_prime (hT hp)).pos
      (G.goodPrime_of_not_dvd_P₀ (medPrimes_prime (hT hp)) (medPrimes_not_dvd (hT hp))))
    (apSample_equidistributed G X)
  refine hmain.trans ?_
  have h1 := sum_sq_rowCoeff_le bb hbb G a
  have h2 := sum_abs_rowCoeff_le bb hbb G a
  have h2' : 0 ≤ ∑ i : G.Idx, |rowCoeff bb G a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hinv : 0 ≤ ∑ p ∈ T, (p : ℝ)⁻¹ := Finset.sum_nonneg fun p _ => by positivity
  gcongr

/-- **The medium-prime first moment for a subfamily**, against the *unrestricted* `medBudget`. -/
theorem sampleAvg_abs_blockSum_sub_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hK : 0 < G.K) (a : Fin G.K → Fin G.s)
    {T : Finset ℕ} (hT : T ⊆ medPrimes R Y G.P₀) :
    ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        |blockSum bb G (fun m => (omegaOn T m : ℝ)) n a|
      ≤ Real.sqrt (medBudget bb G X R Y) := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  refine (sampleAvg_abs_le_sqrt _ _).trans (Real.sqrt_le_sqrt ?_)
  have hc : (0 : ℝ) < (apSample X G.P₀ G.b₀).card := by exact_mod_cast hne.card_pos
  have h := sum_sq_blockSum_sub_le bb hbb G X R Y hK a hT
  have hsum : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ ∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun p _ _ => by positivity)
  have hcard : (T.card : ℝ) ≤ ((medPrimes R Y G.P₀).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hT
  have hcard0 : (0 : ℝ) ≤ (T.card : ℝ) := by positivity
  have hL2 := rowL2_nonneg hbr G.K
  have hL1 := rowL1_nonneg hbr G.K
  unfold medBudget
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        blockSum bb G (fun m => (omegaOn T m : ℝ)) n a ^ 2
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
          ((apSample X G.P₀ G.b₀).card * (∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹) * rowL2 bb G.K
            + 2 * ((medPrimes R Y G.P₀).card : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
        gcongr
    _ = _ := by field_simp

end NormalNumbers.G4
