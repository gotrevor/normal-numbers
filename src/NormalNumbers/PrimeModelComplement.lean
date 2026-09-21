import Mathlib

/-!
# Recovering a probability law from its retained mass

The prime-model shortcut needs a finite retained set but permits infinitely many
discarded states (unbounded prime valuations).  Hence the sums outside the retained
set and over the whole law are `tsum`, not finite-support approximations.
-/

open scoped BigOperators

namespace NormalNumbers.PrimeModel

/-- Splitting a summable real family at a finite set. -/
private lemma sum_add_tsum_compl_finset {ι : Type*} (f : ι → ℝ) (B : Finset ι)
    (hf : Summable f) :
    (∑ i ∈ B, f i) + (∑' i : {i // i ∉ B}, f i) = ∑' i, f i :=
  hf.sum_add_tsum_compl

/-- The finite retained error controls the difference of the retained masses. -/
private lemma abs_sum_sub_sum_le_sum_abs {ι : Type*} (μ ν : ι → ℝ) (B : Finset ι) :
    |(∑ i ∈ B, ν i) - (∑ i ∈ B, μ i)| ≤ ∑ i ∈ B, |ν i - μ i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Actual discarded mass is bounded using only model discarded mass and retained L1 error. -/
theorem probability_complement_tail {ι : Type*} (μ ν : ι → ℝ) (B : Finset ι)
    (hμ : Summable μ) (hν : Summable ν)
    (hμ_nonneg : ∀ i, 0 ≤ μ i) (hν_nonneg : ∀ i, 0 ≤ ν i)
    (hμ_one : ∑' i, μ i = 1) (hν_one : ∑' i, ν i = 1) :
    (∑' i : {i // i ∉ B}, ν i) ≤
      (∑' i : {i // i ∉ B}, μ i) + ∑ i ∈ B, |ν i - μ i| := by
  have hμs := sum_add_tsum_compl_finset μ B hμ
  have hνs := sum_add_tsum_compl_finset ν B hν
  have hd := abs_le.mp (abs_sum_sub_sum_le_sum_abs μ ν B)
  have hd0 : (0:ℝ) ≤ ∑ i ∈ B, |ν i - μ i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [hμ_one] at hμs
  rw [hν_one] at hνs
  linarith

/-- The complement shortcut, with the sharp coefficient 2 on both terms. -/
theorem probability_complement_L1 {ι : Type*} (μ ν : ι → ℝ) (B : Finset ι)
    (hμ : Summable μ) (hν : Summable ν)
    (hμ_nonneg : ∀ i, 0 ≤ μ i) (hν_nonneg : ∀ i, 0 ≤ ν i)
    (hμ_one : ∑' i, μ i = 1) (hν_one : ∑' i, ν i = 1) :
    (∑' i, |ν i - μ i|) ≤
      2 * (∑' i : {i // i ∉ B}, μ i) + 2 * ∑ i ∈ B, |ν i - μ i| := by
  have habs : Summable (fun i => |ν i - μ i|) := (hν.sub hμ).abs
  have hsplit := sum_add_tsum_compl_finset (fun i => |ν i - μ i|) B habs
  have hμc : Summable (fun i : {i // i ∉ B} => μ i) := hμ.subtype _
  have hνc : Summable (fun i : {i // i ∉ B} => ν i) := hν.subtype _
  have habsc : Summable (fun i : {i // i ∉ B} => |ν i - μ i|) := habs.subtype _
  have hcompl : (∑' i : {i // i ∉ B}, |ν i - μ i|)
      ≤ (∑' i : {i // i ∉ B}, ν i) + (∑' i : {i // i ∉ B}, μ i) := by
    rw [← hνc.tsum_add hμc]
    refine Summable.tsum_le_tsum (fun i => ?_) habsc (hνc.add hμc)
    calc |ν i.1 - μ i.1| ≤ |ν i.1| + |μ i.1| := abs_sub _ _
      _ = ν i.1 + μ i.1 := by
          rw [abs_of_nonneg (hν_nonneg _), abs_of_nonneg (hμ_nonneg _)]
  have htail := probability_complement_tail μ ν B hμ hν hμ_nonneg hν_nonneg hμ_one hν_one
  linarith

/-- Transfer to bounded complex phases, the form consumed by a correlation estimate. -/
theorem probability_complement_phase {ι : Type*} (μ ν : ι → ℝ) (B : Finset ι)
    (hμ : Summable μ) (hν : Summable ν)
    (hμ_nonneg : ∀ i, 0 ≤ μ i) (hν_nonneg : ∀ i, 0 ≤ ν i)
    (hμ_one : ∑' i, μ i = 1) (hν_one : ∑' i, ν i = 1)
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(∑' i, (ν i : ℂ) * f i) - (∑' i, (μ i : ℂ) * f i)‖ ≤
      2 * (∑' i : {i // i ∉ B}, μ i) + 2 * ∑ i ∈ B, |ν i - μ i| := by
  have hnormf : ∀ i, ‖(ν i - μ i : ℝ) • f i‖ ≤ |ν i - μ i| := by
    intro i
    rw [norm_smul, Real.norm_eq_abs]
    calc |ν i - μ i| * ‖f i‖ ≤ |ν i - μ i| * 1 :=
          mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
      _ = |ν i - μ i| := mul_one _
  have habs : Summable (fun i => |ν i - μ i|) := (hν.sub hμ).abs
  have hνf : Summable (fun i => (ν i : ℂ) * f i) := by
    refine Summable.of_norm_bounded hν (fun i => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν_nonneg i)]
    calc ν i * ‖f i‖ ≤ ν i * 1 := mul_le_mul_of_nonneg_left (hf i) (hν_nonneg i)
      _ = ν i := mul_one _
  have hμf : Summable (fun i => (μ i : ℂ) * f i) := by
    refine Summable.of_norm_bounded hμ (fun i => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ_nonneg i)]
    calc μ i * ‖f i‖ ≤ μ i * 1 := mul_le_mul_of_nonneg_left (hf i) (hμ_nonneg i)
      _ = μ i := mul_one _
  have hdiff : (∑' i, (ν i : ℂ) * f i) - (∑' i, (μ i : ℂ) * f i)
      = ∑' i, ((ν i - μ i : ℝ) • f i) := by
    rw [← hνf.tsum_sub hμf]
    congr 1
    funext i
    simp [Complex.real_smul, sub_mul, Complex.ofReal_sub]
  rw [hdiff]
  have hbound : ‖∑' i, ((ν i - μ i : ℝ) • f i)‖ ≤ ∑' i, |ν i - μ i| :=
    tsum_of_norm_bounded habs.hasSum hnormf
  exact hbound.trans
    (probability_complement_L1 μ ν B hμ hν hμ_nonneg hν_nonneg hμ_one hν_one)

end NormalNumbers.PrimeModel

