import NormalNumbers.PrimeModelComplement

/-!
# Lower atom bounds suffice for normalized finite probability laws

This is the one-sided transfer used with the Brun lower sieve.  It does not
require upper estimates on retained atoms or empirical discarded mass.
-/

open scoped BigOperators
namespace NormalNumbers.PrimeModel

/-- Normalization equates surplus and deficit mass. -/
theorem finite_L1_eq_twice_deficit {ι : Type*} [Fintype ι]
    (μ ν : ι → ℝ) (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1) :
    ∑ i, |ν i - μ i| = 2 * ∑ i, max (μ i - ν i) 0 := by
  have hid : ∀ i, |ν i - μ i| = 2 * max (μ i - ν i) 0 + ν i - μ i := by
    intro i
    by_cases h : μ i ≤ ν i
    · rw [max_eq_right (sub_nonpos.mpr h), abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · have h' := le_of_not_ge h
      rw [max_eq_left (sub_nonneg.mpr h'), abs_of_nonpos (sub_nonpos.mpr h')]
      ring
  simp_rw [hid]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hμ, hν]
  ring

/-- A lower bound on each retained atom gives the entire L1 bound. -/
theorem finite_L1_of_lower_atoms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : ι → ℝ) (B : Finset ι) (η : ℝ) (e : ι → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ i, 0 ≤ ν i)
    (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1)
    (hη : 0 ≤ η) (he : ∀ i ∈ B, 0 ≤ e i)
    (hlower : ∀ i ∈ B, (1 - η) * μ i - e i ≤ ν i) :
    ∑ i, |ν i - μ i| ≤
      2 * (∑ i ∈ Bᶜ, μ i) + 2 * η + 2 * ∑ i ∈ B, e i := by
  have hpoint : ∀ i, max (μ i - ν i) 0 ≤
      (if i ∈ B then η * μ i + e i else μ i) := by
    intro i
    by_cases hi : i ∈ B
    · rw [if_pos hi]
      apply max_le
      · have := hlower i hi; nlinarith
      · exact add_nonneg (mul_nonneg hη (hμ0 i)) (he i hi)
    · rw [if_neg hi]
      exact max_le (sub_le_self _ (hν0 i)) (hμ0 i)
  have hsumμ : ∑ i ∈ B, μ i ≤ 1 := by
    rw [← hμ]
    exact Finset.sum_le_univ_sum_of_nonneg hμ0
  have hdef : ∑ i, max (μ i - ν i) 0 ≤
      η + (∑ i ∈ B, e i) + ∑ i ∈ Bᶜ, μ i := by
    calc
      ∑ i, max (μ i - ν i) 0 ≤
          ∑ i, if i ∈ B then η * μ i + e i else μ i :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = η * (∑ i ∈ B, μ i) + (∑ i ∈ B, e i) + ∑ i ∈ Bᶜ, μ i := by
        rw [Finset.sum_ite]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        congr 1
        ext i
        simp
      _ ≤ η + (∑ i ∈ B, e i) + ∑ i ∈ Bᶜ, μ i := by
        have := mul_le_mul_of_nonneg_left hsumμ hη
        linarith
  rw [finite_L1_eq_twice_deficit μ ν hμ hν]
  linarith

/-- Lower sieve bounds transfer directly to any complex phase of norm at most one. -/
theorem finite_phase_of_lower_atoms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : ι → ℝ) (B : Finset ι) (η : ℝ) (e : ι → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ i, 0 ≤ ν i)
    (hμ : ∑ i, μ i = 1) (hν : ∑ i, ν i = 1)
    (hη : 0 ≤ η) (he : ∀ i ∈ B, 0 ≤ e i)
    (hlower : ∀ i ∈ B, (1 - η) * μ i - e i ≤ ν i)
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(∑ i, (ν i : ℂ) * f i) - ∑ i, (μ i : ℂ) * f i‖ ≤
      2 * (∑ i ∈ Bᶜ, μ i) + 2 * η + 2 * ∑ i ∈ B, e i := by
  have hphase : ‖(∑ i, (ν i : ℂ) * f i) - ∑ i, (μ i : ℂ) * f i‖
      ≤ ∑ i, |ν i - μ i| := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (hf i) (abs_nonneg (ν i - μ i))
  exact hphase.trans (finite_L1_of_lower_atoms μ ν B η e hμ0 hν0 hμ hν hη he hlower)

/-- Sharp anchor: model (1/2,1/2), empirical (0,1), retained state 1.
The retained lower estimate is exact with eta=e=0; discarded model mass 1/2
accounts for the entire L1 discrepancy 1. -/
example : (∑ i : Fin 2, |(if i = 0 then (0 : ℝ) else 1) - 1/2|) =
    2 * (∑ i ∈ ({1} : Finset (Fin 2))ᶜ, (1/2 : ℝ)) := by
  have hc : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  rw [hc]
  norm_num [Fin.sum_univ_two]

/-- info: 'NormalNumbers.PrimeModel.finite_L1_of_lower_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_L1_of_lower_atoms

/-- info: 'NormalNumbers.PrimeModel.finite_phase_of_lower_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_phase_of_lower_atoms

end NormalNumbers.PrimeModel
