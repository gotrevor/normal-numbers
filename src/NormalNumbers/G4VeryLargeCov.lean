/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetJunk

/-!
# The very-large-prime block from a covariance bound (Erdős #257 base 2, N1–N2)

At `bb = 2` the pointwise very-large-prime bound `(log Mx / log Y) · rowL1` is useless,
`rowL1 2 K = 1`.  Here it is replaced by a second-moment bound: if the shifted very-large counts
`ω_{S,>Y}(n + ρ_i)`, centred at a common `n`-dependent `μ n`, have second moments `≤ V` and
pairwise cross moments `≤ κ` in absolute value (`VeryLargeCov`), then the block has mean
absolute value `≤ √(rowL2 · V + rowL1² · κ)`.

* N1 `blockSum_sq_le_of_cov` (abstract, `sum_sq_le_of_cov`);
* N2 `gridFrameW_subset_propD_of_cov`: `PropD` for the prime-subset frame with the pointwise
  term replaced.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

section Abstract

/-- **N1, abstract.**  Weights `c` with `∑ c = 0`, centre `μ` arbitrary: the sample mean of
`(∑ cᵢ Wᵢ)²` is at most `(∑ cᵢ²) V + (∑ |cᵢ|)² κ`. -/
theorem sum_sq_le_of_cov {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) (c : ι → ℝ)
    (hc : ∑ i, c i = 0) (W : ι → ℕ → ℝ) (μ : ℕ → ℝ) {V κ : ℝ} (hκ : 0 ≤ κ)
    (hV : ∀ i, (P.card : ℝ)⁻¹ * ∑ n ∈ P, (W i n - μ n) ^ 2 ≤ V)
    (hcov : ∀ i j, i ≠ j →
      |(P.card : ℝ)⁻¹ * ∑ n ∈ P, (W i n - μ n) * (W j n - μ n)| ≤ κ) :
    (P.card : ℝ)⁻¹ * ∑ n ∈ P, (∑ i, c i * W i n) ^ 2
      ≤ (∑ i, c i ^ 2) * V + (∑ i, |c i|) ^ 2 * κ := by
  set M : ι → ι → ℝ := fun i j => (P.card : ℝ)⁻¹ * ∑ n ∈ P, (W i n - μ n) * (W j n - μ n)
    with hM
  have hcen : ∀ n, ∑ i, c i * W i n = ∑ i, c i * (W i n - μ n) := by
    intro n
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul, sub_zero]
  have hexp : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (∑ i, c i * W i n) ^ 2
      = ∑ i, ∑ j, c i * c j * M i j := by
    simp_rw [hcen, sq, Finset.sum_mul_sum, hM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hexp]
  have hrow : ∀ i, ∑ j, c i * c j * M i j ≤ c i ^ 2 * V + ∑ j, |c i| * |c j| * κ := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag : c i * c i * M i i ≤ c i ^ 2 * V := by
      have : M i i = (P.card : ℝ)⁻¹ * ∑ n ∈ P, (W i n - μ n) ^ 2 := by
        simp only [hM, sq]
      rw [this, ← sq]
      exact mul_le_mul_of_nonneg_left (hV i) (sq_nonneg _)
    have hoff : ∑ j ∈ univ.erase i, c i * c j * M i j ≤ ∑ j, |c i| * |c j| * κ := by
      calc ∑ j ∈ univ.erase i, c i * c j * M i j
          ≤ ∑ j ∈ univ.erase i, |c i| * |c j| * κ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hij : j ≠ i := Finset.ne_of_mem_erase hj
            calc c i * c j * M i j ≤ |c i * c j * M i j| := le_abs_self _
              _ = |c i| * |c j| * |M i j| := by rw [abs_mul, abs_mul]
              _ ≤ |c i| * |c j| * κ :=
                mul_le_mul_of_nonneg_left (hcov i j hij.symm) (by positivity)
        _ ≤ ∑ j, |c i| * |c j| * κ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun j _ _ => by positivity)
    linarith
  calc ∑ i, ∑ j, c i * c j * M i j ≤ ∑ i, (c i ^ 2 * V + ∑ j, |c i| * |c j| * κ) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, c i ^ 2) * V + (∑ i, |c i|) ^ 2 * κ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, sq (∑ i, |c i|), Finset.sum_mul_sum,
          Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

end Abstract

/-- `blockSum` as a row-coefficient sum over the index set, for any weight. -/
lemma blockSum_eq_sum_rowCoeff (bb : ℕ) (G : GridParams) (w : ℕ → ℝ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G w n a = ∑ i : G.Idx, rowCoeff bb G a i * w (n + shiftAL G.B G.Q G.D₀ i) := by
  unfold blockSum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun jj _ => ?_
  show ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
      (w (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (bb : ℝ) ^ layer G.K jj)
    = ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) / (bb : ℝ) ^ layer G.K jj
      * w (n + shiftAL G.B G.Q G.D₀ (α, jj))
  ring

variable (S : ℕ → Prop) [DecidablePred S]

/-- **The covariance interface.**  The shifted `S`-very-large counts `ω_{S,>Y}(n + ρᵢ)`,
centred at a common `μ n`, have sample second moments `≤ V` and cross moments `≤ κ`. -/
def VeryLargeCov (G : GridParams) (X Y : ℕ) (V κ : ℝ) : Prop :=
  ∃ μ : ℕ → ℝ,
    (∀ i : G.Idx, ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        ((omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ i) : ℝ) - μ n) ^ 2 ≤ V) ∧
    ∀ i j : G.Idx, i ≠ j →
      |((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        ((omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ i) : ℝ) - μ n)
          * ((omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ j) : ℝ) - μ n)| ≤ κ

/-- **N1.**  The very-large block's sample second moment from `VeryLargeCov`. -/
theorem blockSum_sq_le_of_cov (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X Y : ℕ)
    (hK : 0 < G.K) {V κ : ℝ} (hV : 0 ≤ V) (hκ : 0 ≤ κ) (hcov : VeryLargeCov S G X Y V κ)
    (a : Fin G.K → Fin G.s) :
    ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        blockSum bb G (fun m => (omegaVLS S Y G.P₀ m : ℝ)) n a ^ 2
      ≤ rowL2 bb G.K * V + rowL1 bb G.K ^ 2 * κ := by
  classical
  obtain ⟨μ, hV', hC⟩ := hcov
  simp_rw [blockSum_eq_sum_rowCoeff]
  refine (sum_sq_le_of_cov (apSample X G.P₀ G.b₀) (rowCoeff bb G a)
    (sum_rowCoeff_eq_zero bb G hK a)
    (fun i n => (omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ i) : ℝ)) μ hκ hV' hC).trans ?_
  have h1 := sum_sq_rowCoeff_le bb hbb G a
  have h2 := sum_abs_rowCoeff_le bb hbb G a
  have h2' : 0 ≤ ∑ i : G.Idx, |rowCoeff bb G a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  gcongr

/-- **`bigAvgS` with the very-large block bounded in mean square.** -/
theorem bigAvgS_le_of_cov (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hRY : R ≤ Y) {V κ : ℝ} (hV : 0 ≤ V) (hκ : 0 ≤ κ)
    (hcov : VeryLargeCov S G X Y V κ) :
    bigAvgS S bb G X R
      ≤ Real.sqrt (medBudget bb G X R Y)
        + Real.sqrt (rowL2 bb G.K * V + rowL1 bb G.K ^ 2 * κ) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set wmed : ℕ → ℝ := fun m => (omegaOn ((medPrimes R Y G.P₀).filter S) m : ℝ) with hwmed
  set wvl : ℕ → ℝ := fun m => (omegaVLS S Y G.P₀ m : ℝ) with hwvl
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
  have hswap : ∀ w : ℕ → ℝ, (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G w n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |blockSum bb G w n (G.rowEquiv.symm ν)| := by
    intro w
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
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
    _ ≤ _ := by
        rw [hswap wmed, hswap wvl, ← hr]
        refine add_le_add ?_ ?_
        · refine avg_le_of_forall_le _ _ (Real.sqrt_nonneg _) fun ν _ => ?_
          exact sampleAvg_abs_blockSum_sub_le bb hbb G X R Y hne hK _ (Finset.filter_subset _ _)
        · refine avg_le_of_forall_le _ _ (Real.sqrt_nonneg _) fun ν _ => ?_
          refine (sampleAvg_abs_le_sqrt _ _).trans (Real.sqrt_le_sqrt ?_)
          exact blockSum_sq_le_of_cov S bb hbb G X Y hK hV hκ hcov _

/-- **N2.  `PropD` for the prime-subset frame from `VeryLargeCov`**: the pointwise
very-large term `(log Mx / log Y) · rowL1` of `gridFrameW_subset_propD_of_bounds` becomes
`√(rowL2 · V + rowL1² · κ)`. -/
theorem gridFrameW_subset_propD_of_cov (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y)
    {V κ : ℝ} (hV : 0 ≤ V) (hκ : 0 ≤ κ) (hcov : VeryLargeCov S G X Y V κ)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δfar : ℝ}
    (hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + Real.sqrt (rowL2 bb G.K * V + rowL1 bb G.K ^ 2 * κ) ≤ δbig * (ε * η))
    (hfar : (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farC G X Dm)
        ≤ δfar * (ε * η)) :
    (gridFrameW (TWeight.subset S) bb hbb G X hne ((smallPrimes R G.P₀).filter S)
      (frozenGammaS S bb G) hη hε D).PropD (δbig + δfar) := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  refine gridFrameW_subset_propD S bb hbb G X hne R hη hε D
    ((bigAvgS_le_of_cov S bb hbb G X R Y hne hK hRY hV hκ hcov).trans (le_trans ?_ hbig))
    ((farAvgS_le S bb hbb G X hne hDm).trans hfar)
  gcongr
  unfold medBudget
  have hcard : ((medPrimes R Y G.P₀).card : ℝ) ≤ Y := by exact_mod_cast card_medPrimes_le R Y G.P₀
  have h1 := sum_inv_medPrimes_le (P₀ := G.P₀) hR hRY
  have h2 := rowL2_nonneg hbr G.K
  have h3 := rowL1_nonneg hbr G.K
  have h4 : (0 : ℝ) ≤ ((medPrimes R Y G.P₀).card : ℝ) := by positivity
  gcongr

end NormalNumbers.G4
