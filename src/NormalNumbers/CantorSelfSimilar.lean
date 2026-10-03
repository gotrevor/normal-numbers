/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal

/-!
# Self-similarity of the quarter-Cantor law

`coinMeasure = ½ (cons true)_* coinMeasure + ½ (cons false)_* coinMeasure`, and
`cantorReal (cons c ω) = ψ_c (cantorReal ω)` with `ψ_c t = 1/2 + c/8 + (t − 1/2)/4`.  Hence
`pushFourier F ξ = ½ (pushFourier (F ∘ ψ₁) ξ + pushFourier (F ∘ ψ₀) ξ)`
(`pushFourier_self_similar`), the first step of the cylinder localisation behind
`ExplicitOmegaK.polyDecay_Gk`.
-/

open MeasureTheory

namespace NormalNumbers.CantorSelfSimilar

open ExplicitSquare

open Classical in

/-- Prepend a coin. -/
def consB (c : Bool) (ω : ℕ → Bool) : ℕ → Bool := fun i => Nat.casesOn i c ω

theorem measurable_consB (c : Bool) : Measurable (consB c) := by
  refine measurable_pi_lambda _ fun i => ?_
  cases i with
  | zero => exact measurable_const
  | succ j => exact measurable_pi_apply j

open Classical in
theorem uniform_apply (A : Set Bool) :
    (PMF.uniformOfFintype Bool).toMeasure A =
      2⁻¹ * (if true ∈ A then 1 else 0) + 2⁻¹ * (if false ∈ A then 1 else 0) := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  simp [Set.indicator, PMF.uniformOfFintype_apply, Fintype.card_bool]

open Classical in
theorem preimage_consB_pi (c : Bool) (s : Finset ℕ) (t : ℕ → Set Bool) :
    consB c ⁻¹' Set.pi (↑s) t =
      if (0 ∈ s → c ∈ t 0) then Set.pi ↑(s.preimage Nat.succ (Nat.succ_injective.injOn))
        (fun j => t (j + 1)) else ∅ := by
  ext ω
  split_ifs with h
  · simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_preimage]
    constructor
    · intro hω j hj; exact hω (j + 1) hj
    · intro hω i hi
      cases i with
      | zero => exact h hi
      | succ j => exact hω j hi
  · simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_empty_iff_false, iff_false]
    intro hω
    push Not at h
    exact h.2 (hω 0 h.1)

open Classical in
theorem prod_split (s : Finset ℕ) (f : ℕ → ENNReal) :
    ∏ i ∈ s, f i = (if 0 ∈ s then f 0 else 1) *
      ∏ j ∈ s.preimage Nat.succ (Nat.succ_injective.injOn), f (j + 1) := by
  rw [← Finset.prod_filter_mul_prod_filter_not s (· = 0)]
  congr 1
  · split_ifs with h
    · rw [show s.filter (· = 0) = {0} by ext i; simp; rintro rfl; exact h]; simp
    · rw [show s.filter (· = 0) = ∅ by ext i; simp; rintro hi rfl; exact h hi]; simp
  · refine Finset.prod_nbij' (fun i => i - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter] at hi
      simp only [Finset.mem_preimage]
      convert hi.1 using 1; omega
    · intro j hj; simp only [Finset.mem_preimage] at hj
      simp [hj]
    · intro i hi; simp at hi ⊢; omega
    · intro j _; simp
    · intro i hi; simp only [Finset.mem_filter] at hi
      rw [show i - 1 + 1 = i by omega]

open Classical in
/-- **One-step self-similarity of the coin measure.** -/
theorem coinMeasure_eq :
    coinMeasure = (2⁻¹ : ENNReal) • coinMeasure.map (consB true) +
      (2⁻¹ : ENNReal) • coinMeasure.map (consB false) := by
  symm
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpi : MeasurableSet (Set.pi (↑s) t) := MeasurableSet.pi s.countable_toSet fun i _ => ht i
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (measurable_consB true) hpi, Measure.map_apply (measurable_consB false) hpi,
    preimage_consB_pi, preimage_consB_pi, prod_split]
  have hc : coinMeasure (Set.pi ↑(s.preimage Nat.succ (Nat.succ_injective.injOn))
      (fun j => t (j + 1))) =
      ∏ j ∈ s.preimage Nat.succ (Nat.succ_injective.injOn),
        (PMF.uniformOfFintype Bool).toMeasure (t (j + 1)) := by
    unfold coinMeasure
    exact Measure.infinitePi_pi _ fun j _ => ht (j + 1)
  rw [apply_ite coinMeasure, apply_ite coinMeasure, measure_empty, hc, uniform_apply]
  generalize (∏ j ∈ s.preimage Nat.succ (Nat.succ_injective.injOn),
    (PMF.uniformOfFintype Bool).toMeasure (t (j + 1))) = X
  have h2 : (2⁻¹ : ENNReal) * X + 2⁻¹ * X = X := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  split_ifs <;> simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul, ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul] <;> tauto

/-- The quarter-Cantor IFS map `ψ_c`. -/
noncomputable def psi (c : Bool) (t : ℝ) : ℝ := 1 / 2 + (if c then 1 / 8 else 0) + (t - 1 / 2) / 4

theorem cantorReal_consB (c : Bool) (ω : ℕ → Bool) :
    cantorReal (consB c ω) = psi c (cantorReal ω) := by
  have hsum : ∀ e : ℕ → Bool, Summable fun i => (cantorDigits e i : ℝ) / (2 : ℝ) ^ (i + 1) := by
    intro e
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_two).mul_left (1 / 2))
    have : (cantorDigits e i : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (cantorDigits_lt e i)
    rw [pow_succ]
    calc (cantorDigits e i : ℝ) / (2 ^ i * 2) ≤ 1 / (2 ^ i * 2) := by gcongr
      _ = 1 / 2 * (1 / 2) ^ i := by rw [div_pow, one_pow]; field_simp
  have hshift : ∀ i, (cantorDigits (consB c ω) (i + 3) : ℝ) / (2 : ℝ) ^ (i + 3 + 1) =
      (cantorDigits ω (i + 1) : ℝ) / (2 : ℝ) ^ (i + 1 + 1) / 4 := by
    intro i
    have hd : cantorDigits (consB c ω) (i + 3) = cantorDigits ω (i + 1) := by
      unfold cantorDigits
      rw [if_neg (show i + 3 ≠ 0 by omega), if_neg (show i + 1 ≠ 0 by omega)]
      have hpar : (i + 3) % 2 = (i + 1) % 2 := by omega
      rw [hpar]
      by_cases h : (i + 1) % 2 = 0
      · rw [if_pos h, if_pos h, show (i + 3) / 2 - 1 = ((i + 1) / 2 - 1) + 1 by omega]; rfl
      · rw [if_neg h, if_neg h]
    rw [hd]; ring
  unfold cantorReal realOfDigits
  simp only [Nat.cast_ofNat]
  rw [← (hsum (consB c ω)).sum_add_tsum_nat_add 3, (hsum ω).tsum_eq_zero_add]
  rw [tsum_congr hshift, tsum_div_const]
  simp [Finset.sum_range_succ, cantorDigits, consB, psi]
  cases c <;> simp <;> ring

theorem measurable_cantorReal : Measurable cantorReal := by
  unfold cantorReal realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
  exact (measurable_of_countable (fun b : Bool =>
    if i = 0 then 1 else if i % 2 = 0 then (if b then 1 else 0) else 0)).comp
    (measurable_pi_apply (i / 2 - 1))

/-- **One-step self-similarity of `pushFourier`.** -/
theorem pushFourier_self_similar (F : ℝ → ℝ) (hF : Measurable F) (ξ : ℝ) :
    pushFourier F ξ = 2⁻¹ * pushFourier (F ∘ psi true) ξ + 2⁻¹ * pushFourier (F ∘ psi false) ξ := by
  set g : (ℕ → Bool) → ℂ := fun ω =>
    Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (cantorReal ω) : ℝ) : ℂ))
  have hgm : Measurable g := by
    refine Complex.measurable_exp.comp (measurable_const.mul ?_)
    exact Complex.measurable_ofReal.comp (measurable_const.mul (hF.comp measurable_cantorReal))
  have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      simp only [g, Complex.norm_exp]
      simp)
  have hpf : ∀ c, pushFourier (F ∘ psi c) ξ = ∫ ω, g (consB c ω) ∂coinMeasure := by
    intro c
    unfold pushFourier
    congr 1; funext ω
    simp only [g, Function.comp, cantorReal_consB]
  rw [hpf, hpf]
  unfold pushFourier
  change ∫ ω, g ω ∂coinMeasure = _
  conv_lhs => rw [coinMeasure_eq]
  have hfin : ∀ c, IsFiniteMeasure (coinMeasure.map (consB c)) := fun c => inferInstance
  rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
      ((hgi _ inferInstance).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
    integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
  simp [ENNReal.toReal_inv]

end NormalNumbers.CantorSelfSimilar
