/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouvilleAll

/-!
# Base-5 coin points and their second moment

The base-5 coin point `ptF free ω = Σ dᵢ 5^{−i−1}`, `dᵢ = 3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}` on free
places, `0` on forced ones.  This file ports the Cassels second-moment route of
`CantorLiouville`/`CantorLiouvilleAll` from base 3 to base 5:

* `charFun_realF`: `|𝔼 e(ξ x)| ≤ Π_{free p < M} φ₅(ξ/5^{p+1})`, `φ₅(t) = |1+e(t)+e(3t)+e(4t)|/4`;
* `five_point`: `Σ_{s<5} φ₅(x + s/5) ≤ 5/2` (Parseval: `Σ φ₅² = 5/4`, then Cauchy–Schwarz),
  the analogue of Cassels' three-point bound `≤ 2`;
* the residue/orbit sums for `5 ∤ b` via `b⁴ ≡ 1 (mod 5)` and lifting the exponent.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorFiveMoment

open DecayAeNormal ExplicitSquare CantorSelfSimilar CantorLiouville

/-! ## The point -/

/-- Free position `i` carries the base-5 digit `3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}`; forced ones `0`. -/
def ptDigitF (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ℕ :=
  if free i then 3 * (ω (2 * i)).toNat + (ω (2 * i + 1)).toNat else 0

/-- The point coded by coins `ω`. -/
noncomputable def ptF (free : ℕ → Bool) (ω : ℕ → Bool) : ℝ := realOfDigits 5 (ptDigitF free ω)

theorem ptDigitF_lt (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) :
    ptDigitF free ω i < 5 ∧ ptDigitF free ω i ≠ 2 := by
  unfold ptDigitF; split_ifs <;> cases ω (2 * i) <;> cases ω (2 * i + 1) <;> simp

theorem ptDigitF_le_four (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ptDigitF free ω i ≤ 4 :=
  Nat.lt_succ_iff.1 (ptDigitF_lt free ω i).1

theorem summable_ptDigitF (free : ℕ → Bool) (ω : ℕ → Bool) :
    Summable fun i => (ptDigitF free ω i : ℝ) / (5 : ℝ) ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_geometric_of_lt_one (r := (5 : ℝ)⁻¹) (by norm_num) (by norm_num)))
  have : (ptDigitF free ω i : ℝ) ≤ 5 := by exact_mod_cast (ptDigitF_lt free ω i).1.le
  rw [inv_pow, div_le_iff₀ (by positivity), pow_succ, inv_mul_cancel_left₀ (by positivity)]
  exact this

theorem measurable_ptF (free : ℕ → Bool) : Measurable (ptF free) := by
  unfold ptF realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
  unfold ptDigitF
  have h1 : Measurable fun ω : ℕ → Bool => ω (2 * i) := measurable_pi_apply _
  have h2 : Measurable fun ω : ℕ → Bool => ω (2 * i + 1) := measurable_pi_apply _
  have : Measurable fun ω : ℕ → Bool => (ω (2 * i), ω (2 * i + 1)) := h1.prodMk h2
  exact (measurable_of_countable (fun q : Bool × Bool =>
    if free i then 3 * q.1.toNat + q.2.toNat else 0)).comp this

/-- Peeling one digit (two coins). -/
theorem ptF_cons (free : ℕ → Bool) (c₀ c₁ : Bool) (ω : ℕ → Bool) :
    ptF free (consB c₀ (consB c₁ ω)) =
      (if free 0 then (3 * c₀.toNat + c₁.toNat : ℕ) else (0 : ℕ)) / 5 +
        ptF (fun i => free (i + 1)) ω / 5 := by
  unfold ptF realOfDigits
  simp only [Nat.cast_ofNat]
  rw [(summable_ptDigitF free (consB c₀ (consB c₁ ω))).tsum_eq_zero_add, ← tsum_div_const]
  congr 1
  · simp only [ptDigitF, consB, zero_add, pow_one]
    split_ifs <;> simp
  · refine tsum_congr fun i => ?_
    have e1 : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
    simp only [ptDigitF, e1, consB]
    rw [pow_succ _ (i + 1)]; field_simp

/-! ## The per-digit factor -/

/-- `φ₅(t) = |1 + e(t) + e(3t) + e(4t)| / 4`, the modulus of the digit characteristic function. -/
noncomputable def phiF (t : ℝ) : ℝ := ‖(1 + ee t + ee (3 * t) + ee (4 * t)) / 4‖

theorem phiF_nonneg (t : ℝ) : 0 ≤ phiF t := norm_nonneg _

theorem phiF_le_one (t : ℝ) : phiF t ≤ 1 := by
  unfold phiF
  rw [norm_div]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4, div_le_one (by norm_num)]
  calc ‖1 + ee t + ee (3 * t) + ee (4 * t)‖ ≤ ‖1 + ee t + ee (3 * t)‖ + ‖ee (4 * t)‖ := norm_add_le _ _
    _ ≤ ‖1 + ee t‖ + ‖ee (3 * t)‖ + ‖ee (4 * t)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + ‖ee t‖ + ‖ee (3 * t)‖ + ‖ee (4 * t)‖ := by gcongr; exact norm_add_le _ _
    _ = 4 := by simp [norm_ee]; norm_num

theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

theorem ee_add_int (t : ℝ) (n : ℤ) : ee (t + n) = ee t := by
  rw [ee_add, ee_int, mul_one]

theorem phiF_add_int (t : ℝ) (n : ℤ) : phiF (t + n) = phiF t := by
  unfold phiF
  have h3 : 3 * (t + n) = 3 * t + ((3 * n : ℤ) : ℝ) := by push_cast; ring
  have h4 : 4 * (t + n) = 4 * t + ((4 * n : ℤ) : ℝ) := by push_cast; ring
  rw [h3, h4, ee_add_int, ee_add_int, ee_add_int]

theorem phiF_neg (t : ℝ) : phiF (-t) = phiF t := by
  unfold phiF
  rw [← norm_star]
  congr 1
  simp only [star_div₀, star_add, star_one, RCLike.star_def, conj_ee, map_ofNat]
  ring_nf

/-! ## Characteristic function -/

theorem integral_split (g : (ℕ → Bool) → ℂ) (hgm : Measurable g) (hgb : ∀ ω, ‖g ω‖ ≤ 1) :
    ∫ ω, g ω ∂coinMeasure =
      2⁻¹ * ∫ ω, g (consB true ω) ∂coinMeasure + 2⁻¹ * ∫ ω, g (consB false ω) ∂coinMeasure := by
  have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  conv_lhs => rw [coinMeasure_eq]
  rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
      ((hgi _ inferInstance).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
    integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
  simp [ENNReal.toReal_inv]

/-- **Riesz-product bound, base 5.** -/
theorem charFun_realF (M : ℕ) : ∀ (free : ℕ → Bool) (ξ : ℝ),
    ‖∫ ω, ee (ξ * ptF free ω) ∂coinMeasure‖ ≤
      ∏ p ∈ (Finset.range M).filter (fun p => free p = true), phiF (ξ / 5 ^ (p + 1)) := by
  induction M with
  | zero =>
    intro free ξ
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    refine (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
    simp
  | succ M ih =>
    intro free ξ
    set free' : ℕ → Bool := fun i => free (i + 1)
    set I' := ∫ ω, ee (ξ / 5 * ptF free' ω) ∂coinMeasure
    have hm : ∀ (c₀ c₁ : Bool), Measurable fun ω => ee (ξ * ptF free (consB c₀ (consB c₁ ω))) :=
      fun c₀ c₁ => measurable_ee.comp (((measurable_ptF free).comp
        ((measurable_consB c₀).comp (measurable_consB c₁))).const_mul ξ)
    have hc : ∀ c₀ c₁ : Bool, ∫ ω, ee (ξ * ptF free (consB c₀ (consB c₁ ω))) ∂coinMeasure =
        ee (ξ * ((if free 0 then (3 * c₀.toNat + c₁.toNat : ℕ) else (0 : ℕ)) / 5)) * I' := by
      intro c₀ c₁
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [ptF_cons, ← ee_add]
      congr 1; ring
    have hs1 := integral_split (fun ω => ee (ξ * ptF free ω))
      (measurable_ee.comp ((measurable_ptF free).const_mul ξ)) (fun ω => (norm_ee _).le)
    have hs2 : ∀ c₀ : Bool, ∫ ω, ee (ξ * ptF free (consB c₀ ω)) ∂coinMeasure =
        2⁻¹ * ∫ ω, ee (ξ * ptF free (consB c₀ (consB true ω))) ∂coinMeasure +
          2⁻¹ * ∫ ω, ee (ξ * ptF free (consB c₀ (consB false ω))) ∂coinMeasure := fun c₀ =>
      integral_split (fun ω => ee (ξ * ptF free (consB c₀ ω)))
        (measurable_ee.comp (((measurable_ptF free).comp (measurable_consB c₀)).const_mul ξ))
        (fun ω => (norm_ee _).le)
    have hI' := ih free' (ξ / 5)
    rw [hs1, hs2, hs2, hc, hc, hc, hc, Finset.prod_filter, Finset.prod_range_succ',
      ← Finset.prod_filter]
    have hre : ∏ p ∈ (Finset.range M).filter (fun p => free (p + 1) = true),
        phiF (ξ / 5 ^ (p + 1 + 1)) =
        ∏ p ∈ (Finset.range M).filter (fun p => free' p = true), phiF (ξ / 5 / 5 ^ (p + 1)) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 1; rw [pow_succ]; ring
    rw [hre]
    by_cases h0 : free 0 = true
    · simp only [h0, if_true]
      have : 2⁻¹ * (2⁻¹ * (ee (ξ * (((3 * true.toNat + true.toNat : ℕ) : ℝ) / 5)) * I') +
            2⁻¹ * (ee (ξ * (((3 * true.toNat + false.toNat : ℕ) : ℝ) / 5)) * I')) +
          2⁻¹ * (2⁻¹ * (ee (ξ * (((3 * false.toNat + true.toNat : ℕ) : ℝ) / 5)) * I') +
            2⁻¹ * (ee (ξ * (((3 * false.toNat + false.toNat : ℕ) : ℝ) / 5)) * I')) =
          ((1 + ee (ξ / 5) + ee (3 * (ξ / 5)) + ee (4 * (ξ / 5))) / 4) * I' := by
        have e0 : ee 0 = 1 := by simpa using ee_int 0
        simp only [Bool.toNat_true, Bool.toNat_false]
        norm_num
        rw [e0]
        ring_nf
      have hφ : ‖(1 + ee (ξ / 5) + ee (3 * (ξ / 5)) + ee (4 * (ξ / 5))) / 4‖ =
          phiF (ξ / 5 ^ (0 + 1)) := by simp [phiF]
      rw [this, norm_mul, mul_comm, hφ]
      exact mul_le_mul_of_nonneg_right hI' (norm_nonneg _)
    · simp only [Bool.not_eq_true] at h0
      simp only [h0, Bool.false_eq_true, if_false, Nat.cast_zero, zero_div, mul_zero]
      have e0 : ee 0 = 1 := by simpa using ee_int 0
      rw [e0, mul_one]
      have : 2⁻¹ * (2⁻¹ * (1 * I') + 2⁻¹ * (1 * I')) + 2⁻¹ * (2⁻¹ * (1 * I') + 2⁻¹ * (1 * I'))
          = I' := by ring
      rw [this]
      exact hI'

end NormalNumbers.CantorFiveMoment
