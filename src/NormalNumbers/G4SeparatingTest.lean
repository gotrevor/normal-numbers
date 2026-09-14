/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4E: the finite separating-test inequality

The candidate proof of base-four disjunctivity of the prime Lambert number `G₄` ends with a
*finite* contradiction (draft §9, brief §4E).  Stripped of every arithmetic and geometric
input it is the following statement about one probability space `(Ω, μ)`, one finite sample
`S : P → Ω`, one bounded test `f`, and one "trigonometric polynomial" `∑ᵢ cᵢ χᵢ` built from a
finite family of "characters" `χᵢ` that integrate to zero unless `i = i₀` (where `χ_{i₀} = 1`):

* the Haar average of `f` is at least `1 - δ₁`                         (input **B**),
* the sample average of `f` is at most `δ₂`                            (inputs **A** + **D**),
* every nontrivial character has sample average of norm at most `δ₃`   (input **C**),
* the polynomial approximates `f` uniformly within `κ` and its nontrivial Fourier mass is at
  most `Λ`                                                             (Jackson, **E**).

Then `1 ≤ δ₁ + δ₂ + 2κ + Λ·δ₃`.  With `κ = 1/16` this is the draft's "`7/8 - o(1) ≤ o(1)`".
Everything in this file is proved; it carries no arithmetic content and is reused verbatim by
the concrete torus wiring in `G4Wiring.lean`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- Sample average of `g` over the finite sample `S` restricted to the index set `P`. -/
noncomputable def sampleAvg {Ω : Type*} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Finset ℕ) (S : ℕ → Ω) (g : Ω → E) : E :=
  (P.card : ℝ)⁻¹ • ∑ n ∈ P, g (S n)

section abstractTest

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]

/-- **Finite separating-test inequality.**  See the module docstring.  The characters are
indexed by a finite set `Q` containing the trivial index `i₀`. -/
theorem separating_test_bound
    (Q : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ Q) (χ : ι → Ω → ℂ)
    (hχ₀ : ∀ ω, χ i₀ ω = 1)
    (hχ_int : ∀ i ∈ Q, Integrable (χ i) μ)
    (hχ_orth : ∀ i ∈ Q, i ≠ i₀ → ∫ ω, χ i ω ∂μ = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (S : ℕ → Ω)
    (f : Ω → ℝ) (hf_int : Integrable f μ)
    (c : ι → ℂ) (κ : ℝ)
    (h_approx : ∀ ω, ‖(∑ i ∈ Q, c i * χ i ω) - (f ω : ℂ)‖ ≤ κ)
    {δ₁ δ₂ δ₃ Λ : ℝ}
    (h_haar : 1 - δ₁ ≤ ∫ ω, f ω ∂μ)
    (h_sample : sampleAvg P S f ≤ δ₂)
    (h_decay : ∀ i ∈ Q, i ≠ i₀ → ‖sampleAvg P S (χ i)‖ ≤ δ₃)
    (h_budget : ∑ i ∈ Q.erase i₀, ‖c i‖ ≤ Λ)
    (hδ₃ : 0 ≤ δ₃) :
    1 ≤ δ₁ + δ₂ + 2 * κ + Λ * δ₃ := by
  set Pc : Ω → ℂ := fun ω => ∑ i ∈ Q, c i * χ i ω with hPc
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  -- (1) Haar integral of the polynomial is its constant coefficient.
  have hPc_int : Integrable Pc μ := by
    refine integrable_finsetSum Q fun i hi => ?_
    exact (hχ_int i hi).const_mul (c i)
  have h_int_Pc : ∫ ω, Pc ω ∂μ = c i₀ := by
    simp only [hPc]
    rw [integral_finsetSum Q fun i hi => (hχ_int i hi).const_mul (c i)]
    rw [← Finset.add_sum_erase Q _ hi₀]
    have h0 : ∫ ω, c i₀ * χ i₀ ω ∂μ = c i₀ := by
      simp [hχ₀]
    rw [h0, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [integral_const_mul, hχ_orth i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi),
      mul_zero]
  -- (2) Sample average of the polynomial.
  have h_lin : sampleAvg P S Pc = ∑ i ∈ Q, c i * sampleAvg P S (χ i) := by
    simp only [sampleAvg, hPc, Complex.real_smul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    ring
  have h_avg₀ : sampleAvg P S (χ i₀) = 1 := by
    simp only [sampleAvg, hχ₀, Finset.sum_const, Complex.real_smul]
    have : ((P.card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  have h_avg_Pc : sampleAvg P S Pc = c i₀ + ∑ i ∈ Q.erase i₀, c i * sampleAvg P S (χ i) := by
    rw [h_lin, ← Finset.add_sum_erase Q _ hi₀, h_avg₀, mul_one]
  have h_avg_close : ‖sampleAvg P S Pc - c i₀‖ ≤ Λ * δ₃ := by
    rw [h_avg_Pc, add_sub_cancel_left]
    calc ‖∑ i ∈ Q.erase i₀, c i * sampleAvg P S (χ i)‖
        ≤ ∑ i ∈ Q.erase i₀, ‖c i * sampleAvg P S (χ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Q.erase i₀, ‖c i‖ * δ₃ := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (h_decay i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)) (norm_nonneg _)
      _ = (∑ i ∈ Q.erase i₀, ‖c i‖) * δ₃ := by rw [Finset.sum_mul]
      _ ≤ Λ * δ₃ := mul_le_mul_of_nonneg_right h_budget hδ₃
  -- (3) Haar side: the polynomial's constant coefficient is within `κ` of `∫ f`.
  have h_haar_close : ‖c i₀ - ((∫ ω, f ω ∂μ : ℝ) : ℂ)‖ ≤ κ := by
    have hfC : Integrable (fun ω => (f ω : ℂ)) μ := hf_int.ofReal
    rw [← h_int_Pc, ← integral_complex_ofReal, ← integral_sub hPc_int hfC]
    calc ‖∫ ω, (Pc ω - (f ω : ℂ)) ∂μ‖
        ≤ κ * (μ Set.univ).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall h_approx)
      _ = κ := by simp
  -- (4) Sample side: the polynomial's sample average is within `κ` of the sample average of `f`.
  have h_sample_close : ‖sampleAvg P S Pc - ((sampleAvg P S f : ℝ) : ℂ)‖ ≤ κ := by
    have hκ : 0 ≤ κ := le_trans (norm_nonneg _) (h_approx (S (hP.choose)))
    simp only [sampleAvg, smul_eq_mul, Complex.real_smul]
    push_cast
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    calc ((P.card : ℝ))⁻¹ * ‖∑ n ∈ P, (Pc (S n) - (f (S n) : ℂ))‖
        ≤ (P.card : ℝ)⁻¹ * ∑ n ∈ P, κ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => h_approx (S n))
      _ = κ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  -- (5) Assemble, taking real parts.
  have e1 : (∫ ω, f ω ∂μ) - κ ≤ (c i₀).re := by
    have := (Complex.abs_re_le_norm (c i₀ - ((∫ ω, f ω ∂μ : ℝ) : ℂ))).trans h_haar_close
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [abs_le.mp this]
  have e2 : (c i₀).re ≤ (sampleAvg P S Pc).re + Λ * δ₃ := by
    have := (Complex.abs_re_le_norm (sampleAvg P S Pc - c i₀)).trans h_avg_close
    rw [Complex.sub_re] at this
    linarith [abs_le.mp this]
  have e3 : (sampleAvg P S Pc).re ≤ sampleAvg P S f + κ := by
    have := (Complex.abs_re_le_norm (sampleAvg P S Pc - ((sampleAvg P S f : ℝ) : ℂ))).trans
      h_sample_close
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [abs_le.mp this]
  linarith

/-- The contradiction form: a closed budget below `1` is impossible. -/
theorem separating_test_contradiction
    (Q : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ Q) (χ : ι → Ω → ℂ)
    (hχ₀ : ∀ ω, χ i₀ ω = 1)
    (hχ_int : ∀ i ∈ Q, Integrable (χ i) μ)
    (hχ_orth : ∀ i ∈ Q, i ≠ i₀ → ∫ ω, χ i ω ∂μ = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (S : ℕ → Ω)
    (f : Ω → ℝ) (hf_int : Integrable f μ)
    (c : ι → ℂ) (κ : ℝ)
    (h_approx : ∀ ω, ‖(∑ i ∈ Q, c i * χ i ω) - (f ω : ℂ)‖ ≤ κ)
    {δ₁ δ₂ δ₃ Λ : ℝ}
    (h_haar : 1 - δ₁ ≤ ∫ ω, f ω ∂μ)
    (h_sample : sampleAvg P S f ≤ δ₂)
    (h_decay : ∀ i ∈ Q, i ≠ i₀ → ‖sampleAvg P S (χ i)‖ ≤ δ₃)
    (h_budget : ∑ i ∈ Q.erase i₀, ‖c i‖ ≤ Λ)
    (hδ₃ : 0 ≤ δ₃)
    (h_closed : δ₁ + δ₂ + 2 * κ + Λ * δ₃ < 1) : False := by
  have := separating_test_bound (μ := μ) Q i₀ hi₀ χ hχ₀ hχ_int hχ_orth P hP S f hf_int c κ
    h_approx h_haar h_sample h_decay h_budget hδ₃
  linarith

end abstractTest

end NormalNumbers.G4
