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

/-! ### The `S`-restricted very-large range, and `bigAvgS` -/

variable (S : ℕ → Prop) [DecidablePred S]

/-- The `S`-restricted very-large-prime count. -/
def omegaVLS (Y P₀ m : ℕ) : ℕ := (m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ Y < p)).card

lemma omegaOn_medPrimesS_eq {R Y P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOn ((medPrimes R Y P₀).filter S) m
      = (m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ R < p ∧ p ≤ Y)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_medPrimes]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4⟩, hS⟩, h5⟩; exact ⟨⟨h1, h5, hm⟩, hS, h4, h2, h3⟩
  · rintro ⟨⟨h1, h2, -⟩, hS, h3, h4, h5⟩; exact ⟨⟨⟨h1, h4, h5, h3⟩, hS⟩, h2⟩

/-- **The `S`-junk splits at `Y`** into the filtered medium range and the `S`-very-large range. -/
theorem omegaBigS_split {R Y P₀ m : ℕ} (hRY : R ≤ Y) (hm : m ≠ 0) :
    omegaBigS S R P₀ m = omegaOn ((medPrimes R Y P₀).filter S) m + omegaVLS S Y P₀ m := by
  classical
  rw [omegaOn_medPrimesS_eq S hm]
  unfold omegaBigS omegaVLS
  rw [← Finset.card_filter_add_card_filter_not
    (s := m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ R < p)) (p := fun p => p ≤ Y)]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext p
    simp only [Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨h1, hS, h2, h3⟩, h4⟩; exact ⟨h1, hS, h2, h4⟩
    · rintro ⟨h1, hS, h2, h4⟩; exact ⟨⟨h1, hS, h2, by omega⟩, h4⟩

lemma omegaVLS_le_omegaVL (Y P₀ m : ℕ) : omegaVLS S Y P₀ m ≤ omegaVL Y P₀ m := by
  classical
  refine Finset.card_le_card (fun p hp => ?_)
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩

/-- The `S`-very-large block, pointwise: the same bound as the unrestricted one. -/
theorem abs_blockSum_omegaVLS_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) {Y : ℕ} (hY : 1 < Y)
    {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    {n : ℕ} (hMx : ∀ i : G.Idx, ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    (a : Fin G.K → Fin G.s) :
    |blockSum bb G (fun m => (omegaVLS S Y G.P₀ m : ℝ)) n a|
      ≤ (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hC : 0 ≤ Real.log Mx / Real.log Y := div_nonneg (Real.log_nonneg hMx1) hlog.le
  refine abs_blockSum_le bb hbb G hC n a fun α jj => ?_
  rw [abs_of_nonneg (by positivity)]
  have hpos : 0 < n + shiftAL G.B G.Q G.D₀ (α, jj) := by have := shiftAL_pos G (α, jj); omega
  have hle : ((omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℕ) : ℝ)
      ≤ ((omegaVL Y G.P₀ (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℕ) : ℝ) := by
    exact_mod_cast omegaVLS_le_omegaVL S Y G.P₀ _
  refine hle.trans ((omegaVL_le hY hpos).trans ?_)
  refine div_le_div_of_nonneg_right ?_ hlog.le
  exact Real.log_le_log (by exact_mod_cast hpos) (hMx (α, jj))

/-- **`bigAvgS`, split at `Y`** — the same closed bound as `bigAvg_le`. -/
theorem bigAvgS_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hRY : R ≤ Y) (hY : 1 < Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgS S bb G X R
      ≤ Real.sqrt (medBudget bb G X R Y) + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  set wmed : ℕ → ℝ := fun m => (omegaOn ((medPrimes R Y G.P₀).filter S) m : ℝ) with hwmed
  set wvl : ℕ → ℝ := fun m => (omegaVLS S Y G.P₀ m : ℝ) with hwvl
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hC : 0 ≤ (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
    have := Real.log_nonneg hMx1; have := rowL1_nonneg hbr G.K; positivity
  have hsplit : ∀ n ∈ P, ∀ ν : Fin G.rDim,
      |blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
        ≤ |blockSum bb G wmed n (G.rowEquiv.symm ν)|
          + |blockSum bb G wvl n (G.rowEquiv.symm ν)| := by
    intro n _ ν
    have h : blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
        = blockSum bb G wmed n (G.rowEquiv.symm ν)
          + blockSum bb G wvl n (G.rowEquiv.symm ν) := by
      rw [← blockSum_add]
      refine blockSum_congr bb G _ fun α jj => ?_
      have hpos := shiftAL_pos G (α, jj)
      simp only [hwmed, hwvl]
      rw [omegaBigS_split S hRY (by omega)]
      push_cast; ring
    rw [h]; exact abs_add_le _ _
  unfold bigAvgS
  rw [← hP]
  calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
      ≤ (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
          (|blockSum bb G wmed n (G.rowEquiv.symm ν)|
            + |blockSum bb G wvl n (G.rowEquiv.symm ν)|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν _ => hsplit n hn ν) (by positivity))
          (by positivity)
    _ = (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G wmed n (G.rowEquiv.symm ν)|
        + (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G wvl n (G.rowEquiv.symm ν)| := by
        simp_rw [Finset.sum_add_distrib, mul_add]
        rw [Finset.sum_add_distrib, mul_add]
    _ ≤ Real.sqrt (medBudget bb G X R Y)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
        refine add_le_add ?_ ?_
        · have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |blockSum bb G wmed n (G.rowEquiv.symm ν)|
              = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
                |blockSum bb G wmed n (G.rowEquiv.symm ν)| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
            ring
          rw [hswap]
          have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
          rw [← hr]
          refine avg_le_of_forall_le _ _ (Real.sqrt_nonneg _) fun ν _ => ?_
          exact sampleAvg_abs_blockSum_sub_le bb hbb G X R Y hne hK _ (Finset.filter_subset _ _)
        · refine avg_le_of_forall_le _ _ hC fun n hn => ?_
          have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
          rw [← hr]
          refine avg_le_of_forall_le _ _ hC fun ν _ => ?_
          exact abs_blockSum_omegaVLS_le S bb hbb G hY hMx1 (hMx n hn) _

end NormalNumbers.G4
