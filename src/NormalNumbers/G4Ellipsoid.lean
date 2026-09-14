/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4B (geometry): volume of the image of a cube under `[A_G, I_g]`

The zonotope step of draft §5 is replaced by the ellipsoid bound (lap-1 route decision):

  `vol (L '' cube) ≤ √det(L Lᵀ) · (√(2πe/g) · √(card ι))^g`,   `L : Matrix g ι ℝ`,

because the sup-cube `[-1,1]^ι` lies in the Euclidean ball of radius `√(card ι)`, the ball maps
into `C(ball)` for `C = √(L Lᵀ)` (`L = C U` with `U Uᵀ = I`, and `U` is a contraction), `C`
scales volume by `det C = √det(L Lᵀ)`, and a Euclidean ball of radius `R` in `ℝ^g` has volume at
most `(√(2πe/g) R)^g` (Gaussian comparison — no Gamma function needed).

Applied to `L = [A_G, I_g]` this gives the exponent `½ log det(I + A_G A_Gᵀ) + O(H)` of draft
(5.3) once `card ι = H + g` and `g ≤ H`.
-/

open Matrix MeasureTheory Real
open scoped BigOperators ENNReal

namespace NormalNumbers.G4

/-! ### Gaussian comparison: volume of a Euclidean ball in `Fin`-indexed `ℝ^g` -/

section ball
variable {g : Type*} [Fintype g] [DecidableEq g]

/-- The closed Euclidean ball `{z | z ⬝ᵥ z ≤ R²}` in the pi space `g → ℝ`. -/
def eball (g : Type*) [Fintype g] (R : ℝ) : Set (g → ℝ) := {z | z ⬝ᵥ z ≤ R ^ 2}

lemma measurableSet_eball (R : ℝ) : MeasurableSet (eball g R) :=
  measurableSet_le (by fun_prop) measurable_const

lemma eball_subset_pi_closedBall {R : ℝ} (hR : 0 ≤ R) :
    eball g R ⊆ Metric.closedBall (0 : g → ℝ) R := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs, ← sq_le_sq₀ (abs_nonneg _) hR, sq_abs]
  have : z i ^ 2 ≤ z ⬝ᵥ z := by
    unfold dotProduct
    have := Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg (z j))
      (Finset.mem_univ i)
    nlinarith
  exact this.trans hz

lemma volume_eball_ne_top {R : ℝ} (hR : 0 ≤ R) : volume (eball g R) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_pi_closedBall _ hR]; exact ENNReal.ofReal_ne_top)
    (measure_mono (eball_subset_pi_closedBall hR))

/-- **Gaussian comparison**: `vol {z ⬝ᵥ z ≤ R²} ≤ (√(2πe/n) R)^n`, `n = card g ≥ 1`. -/
theorem volume_eball_le {R : ℝ} (hR : 0 < R) (hg : 0 < Fintype.card g) :
    (volume (eball g R)).toReal
      ≤ (Real.sqrt (2 * π * Real.exp 1 / Fintype.card g) * R) ^ Fintype.card g := by
  set n : ℕ := Fintype.card g
  have hn : (0 : ℝ) < n := by exact_mod_cast hg
  set b : ℝ := n / (2 * R ^ 2)
  have hb : 0 < b := by positivity
  -- the product Gaussian
  let f : (g → ℝ) → ℝ := fun z => ∏ i, Real.exp (-b * z i ^ 2)
  have hf_eq : ∀ z, f z = Real.exp (-b * (z ⬝ᵥ z)) := by
    intro z
    simp only [f, dotProduct, ← Real.exp_sum, Finset.mul_sum, sq]
  have hf_int : Integrable f := Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hb)
  have hf_nonneg : ∀ z, 0 ≤ f z := fun z => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have h_total : ∫ z, f z = Real.sqrt (π / b) ^ n := by
    simp only [f]
    rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-b * t ^ 2)), integral_gaussian]
  -- lower bound on the ball
  have h_lower : Real.exp (-(n : ℝ) / 2) * (volume (eball g R)).toReal ≤ ∫ z in eball g R, f z := by
    have := setIntegral_ge_of_const_le_real (measurableSet_eball R) (volume_eball_ne_top hR.le)
      (f := f) (c := Real.exp (-(n : ℝ) / 2)) ?_ hf_int.integrableOn
    · simpa [measureReal_def] using this
    · intro z hz
      rw [hf_eq]
      apply Real.exp_le_exp.mpr
      have : b * (z ⬝ᵥ z) ≤ b * R ^ 2 := mul_le_mul_of_nonneg_left hz hb.le
      have hbR : b * R ^ 2 = n / 2 := by simp only [b]; field_simp
      linarith
  have h_upper : ∫ z in eball g R, f z ≤ ∫ z, f z :=
    setIntegral_le_integral hf_int (Filter.Eventually.of_forall hf_nonneg)
  -- assemble
  have key : (volume (eball g R)).toReal ≤ Real.exp ((n : ℝ) / 2) * Real.sqrt (π / b) ^ n := by
    have hpos : 0 < Real.exp (-(n : ℝ) / 2) := Real.exp_pos _
    have h1 : Real.exp (-(n : ℝ) / 2) * (volume (eball g R)).toReal ≤ Real.sqrt (π / b) ^ n := by
      rw [← h_total]; exact h_lower.trans h_upper
    have h2 : Real.exp ((n : ℝ) / 2) * Real.exp (-(n : ℝ) / 2) = 1 := by
      rw [← Real.exp_add]; rw [show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 by ring, Real.exp_zero]
    calc (volume (eball g R)).toReal
        = Real.exp ((n : ℝ) / 2) * (Real.exp (-(n : ℝ) / 2) * (volume (eball g R)).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ Real.exp ((n : ℝ) / 2) * Real.sqrt (π / b) ^ n := by gcongr
  refine key.trans (le_of_eq ?_)
  -- `e^{n/2} (π/b)^{n/2} = (√(e π / b))^n = (√(2πe/n) R)^n`
  have he : Real.exp ((n : ℝ) / 2) = Real.sqrt (Real.exp 1) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_nat_mul]; congr 1; ring
  rw [he, ← mul_pow]
  congr 1
  rw [← Real.sqrt_mul (Real.exp_pos 1).le, ← Real.sqrt_mul_self hR.le, ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [b]
  field_simp

end ball

/-! ### The contraction `L = C U`, `C = √(L Lᵀ)` -/

section contraction
variable {g ι : Type*} [Fintype g] [Fintype ι] [DecidableEq g] [DecidableEq ι]

/-- For a real matrix `P` with `Pᵀ P = P` (a symmetric idempotent), `x ⬝ᵥ P x ≤ x ⬝ᵥ x`. -/
lemma dotProduct_mulVec_le_of_idem {P : Matrix ι ι ℝ} (hP : Pᵀ * P = P) (x : ι → ℝ) :
    x ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ x := by
  have h1 : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hP, dotProduct_comm]
  have h2 : 0 ≤ (x - P *ᵥ x) ⬝ᵥ (x - P *ᵥ x) := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, dotProduct_comm (P *ᵥ x) x] at h2
  linarith

/-- If `U Uᵀ = 1` then `‖U x‖² ≤ ‖x‖²` (`U` is a partial isometry, hence a contraction). -/
lemma dotProduct_mulVec_self_le {U : Matrix g ι ℝ} (hU : U * Uᵀ = 1) (x : ι → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ x) ≤ x ⬝ᵥ x := by
  have hP : (Uᵀ * U)ᵀ * (Uᵀ * U) = Uᵀ * U := by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU,
      Matrix.one_mul]
  have := dotProduct_mulVec_le_of_idem hP x
  rwa [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose] at this

end contraction

/-! ### `C = √(L Lᵀ)`, the factorisation `L = C U`, and the volume bound -/

section sqrtFactor
open scoped MatrixOrder
variable {g ι : Type*} [Fintype g] [Fintype ι] [DecidableEq g] [DecidableEq ι]

/-- The positive square root of `L Lᵀ`. -/
noncomputable def sqrtGram (L : Matrix g ι ℝ) : Matrix g g ℝ := CFC.sqrt (L * Lᵀ)

variable {L : Matrix g ι ℝ} (hM : (L * Lᵀ).PosDef)
include hM

lemma sqrtGram_mul_self : sqrtGram L * sqrtGram L = L * Lᵀ :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef)

lemma sqrtGram_posSemidef : (sqrtGram L).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

lemma sqrtGram_transpose : (sqrtGram L)ᵀ = sqrtGram L := by
  have := (sqrtGram_posSemidef hM).1.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma det_sqrtGram : (sqrtGram L).det = Real.sqrt (L * Lᵀ).det := by
  unfold sqrtGram
  rw [PosSemidef.det_sqrt hM.posSemidef, RCLike.sqrt_real]

lemma det_sqrtGram_pos : 0 < (sqrtGram L).det := by
  rw [det_sqrtGram hM]; exact Real.sqrt_pos.mpr hM.det_pos

lemma isUnit_det_sqrtGram : IsUnit (sqrtGram L).det := (det_sqrtGram_pos hM).ne'.isUnit

/-- `U = C⁻¹ L` has orthonormal rows. -/
lemma sqrtGram_inv_mul_mul_transpose :
    ((sqrtGram L)⁻¹ * L) * ((sqrtGram L)⁻¹ * L)ᵀ = 1 := by
  have hu := isUnit_det_sqrtGram hM
  rw [transpose_mul, transpose_nonsing_inv, sqrtGram_transpose hM, Matrix.mul_assoc,
    ← Matrix.mul_assoc L, sqrtGram_mul_self hM |>.symm, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]

lemma sqrtGram_mul_inv_mul : sqrtGram L * ((sqrtGram L)⁻¹ * L) = L := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_sqrtGram hM), Matrix.one_mul]

/-- **Image inclusion**: `L '' S ⊆ C '' eball g R` whenever `S ⊆ eball ι R`. -/
theorem image_subset_sqrtGram_image {S : Set (ι → ℝ)} {R : ℝ} (hS : S ⊆ eball ι R) :
    (Matrix.toLin' L) '' S ⊆ (Matrix.toLin' (sqrtGram L)) '' eball g R := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨((sqrtGram L)⁻¹ * L) *ᵥ x, ?_, ?_⟩
  · exact (dotProduct_mulVec_self_le (sqrtGram_inv_mul_mul_transpose hM) x).trans (hS hx)
  · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, sqrtGram_mul_inv_mul hM]

/-- **Ellipsoid volume bound**: for `S ⊆ eball ι R` and `n = card g ≥ 1`,
`vol (L '' S) ≤ √det(L Lᵀ) · (√(2πe/n) R)^n`. -/
theorem volume_image_le {S : Set (ι → ℝ)} {R : ℝ} (hR : 0 < R) (hS : S ⊆ eball ι R)
    (hg : 0 < Fintype.card g) :
    (volume ((Matrix.toLin' L) '' S)).toReal
      ≤ Real.sqrt (L * Lᵀ).det
        * (Real.sqrt (2 * π * Real.exp 1 / Fintype.card g) * R) ^ Fintype.card g := by
  have hC : volume ((Matrix.toLin' (sqrtGram L)) '' eball g R)
      = ENNReal.ofReal (Real.sqrt (L * Lᵀ).det) * volume (eball g R) := by
    rw [Measure.addHaar_image_linearMap, LinearMap.det_toLin', det_sqrtGram hM,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hfin : volume ((Matrix.toLin' (sqrtGram L)) '' eball g R) ≠ ⊤ := by
    rw [hC]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_eball_ne_top hR.le)
  calc (volume ((Matrix.toLin' L) '' S)).toReal
      ≤ (volume ((Matrix.toLin' (sqrtGram L)) '' eball g R)).toReal :=
        ENNReal.toReal_mono hfin (measure_mono (image_subset_sqrtGram_image hM hS))
    _ = Real.sqrt (L * Lᵀ).det * (volume (eball g R)).toReal := by
        rw [hC, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    _ ≤ _ := by gcongr; exact volume_eball_le hR hg

end sqrtFactor

/-! ### The unit sup-cube lies in the Euclidean ball of radius `√(card ι)` -/

lemma closedBall_subset_eball {ι : Type*} [Fintype ι] :
    Metric.closedBall (0 : ι → ℝ) 1 ⊆ eball ι (Real.sqrt (Fintype.card ι)) := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one] at hx
  show x ⬝ᵥ x ≤ _
  rw [Real.sq_sqrt (by positivity)]
  unfold dotProduct
  calc ∑ i, x i * x i ≤ ∑ _i : ι, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hx i
        rw [Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
    _ = Fintype.card ι := by simp

end NormalNumbers.G4
