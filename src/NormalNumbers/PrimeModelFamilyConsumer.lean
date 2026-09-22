import NormalNumbers.PrimeModelFamilyL4

/-!
# The abstract consumer: fresh reciprocal mass in the cutoff window

Along the schedule `J₁ = ⌊L₃N⌋₊`, `ε = J₁^{-4}`, `y_N = ⌊N^ε⌋₊`, `J_N = min(J₁, ⌊S_P(y_N)/8⌋₊)`, the
only place a property of `P` beyond `DivergentRecip` enters is the fresh reciprocal mass
`recipSumIoc P y_N (2N)`: the transfer term needs it `→ 0` (it dominates the mass to `N`), the
mass-limited tail branch needs it `≤ 1`, and the cap branch uses the universal crude prime mass.
So (Astra, mail 20260922T190707Z):

    DivergentRecip P → (recipSumIoc P y_N (2N) → 0) → IsNormal 4 (subsetLambert P 4).

Every density class (`Sparse`, `SparseIter`, `SparseIter3`, `SparseIterPow`, `SparseL4o`) is a
dominated-Abel corollary, and the theorem also reaches sets of limsup relative density `1`
(prime-bursts example, paper Part VI).
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyIter

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilySharp

variable (P : ℕ → Prop) [DecidablePred P]

/-- **The route's invariant**: the fresh reciprocal mass in the cutoff window tends to `0`. -/
def FreshMassZero : Prop :=
  Tendsto (fun N : ℕ => recipSumIoc P (yI N) (2 * N)) atTop (𝓝 0)

/-- `recipSumIoc` is monotone in the upper endpoint. -/
theorem recipSumIoc_mono_right {y a b : ℕ} (hab : a ≤ b) :
    recipSumIoc P y a ≤ recipSumIoc P y b := by
  unfold recipSumIoc
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hab)) ?_
  intro p _ _
  positivity

theorem fresh_mass_of_freshMassZero (hF : FreshMassZero P) :
    Tendsto (fun N : ℕ => recipSumIoc P (yI N) N) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun N => recipSumIoc_nonneg P _ _)
    (Eventually.of_forall fun N => ?_) hF
  exact recipSumIoc_mono_right P (by omega)

theorem fresh_mass_two_of_freshMassZero (hF : FreshMassZero P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) (2 * N) ≤ 1 := by
  exact ((tendsto_order.1 hF).2 1 (by norm_num)).mono fun N h => h.le

theorem term_one_fresh (hF : FreshMassZero P) (h : ℤ) :
    Tendsto (fun N : ℕ => (4 * Real.pi * |(h : ℝ)| / 3) *
      (2 * recipSumIoc P (yI N) N + (JI P N : ℝ) / N)) atTop (𝓝 0) := by
  have hR := fresh_mass_of_freshMassZero P hF
  have hlogdiv : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_log_div_rpow (r := (1 : ℝ)) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one] using h1
  have hJN : Tendsto (fun N : ℕ => (JI P N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hlogdiv
    · filter_upwards [eventually_ge_atTop 1] with N hN
      positivity
    · filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
        JI_le_L3 P] with N hN hL hJ
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hlogN : 1 < Real.log N := logN_gt_one hN
      have hL2 : L2 N ≤ Real.log N := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log N by linarith)
        have he : L2 N = Real.log (Real.log N) := rfl
        rw [he]; linarith
      have hL3le : L3 N ≤ L2 N := by
        have hpos : (0 : ℝ) < L2 N := by linarith
        have h := Real.log_le_sub_one_of_pos hpos
        have he : L3 N = Real.log (L2 N) := rfl
        rw [he]; linarith
      exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hsum := ((hR.const_mul (2 : ℝ)).add hJN).const_mul (4 * Real.pi * |(h : ℝ)| / 3)
  simpa using hsum

theorem tail_fresh (hF : FreshMassZero P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ JI P N)
      atTop (𝓝 0) := by
  set ρ : ℝ := Real.log 4 - 1 with hρdef
  have hlog4 : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hf : Tendsto (fun N : ℕ => (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JI_tendsto P hP))
    simp only [Function.comp_apply, pow_one, pow_zero]
    ring
  have hgt : Tendsto (fun N : ℕ => 120 * (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hρ0).comp L2_tendsto
      simpa [Function.comp_def] using this
    simpa using h1.const_mul (120 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (by simpa using hf.add hgt)
  · have := recipSumLe_nonneg P (2 * N)
    positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JI_le_L3 P,
    fresh_mass_two_of_freshMassZero P hF, yI_facts] with N hN hL hJle hfm2 hyf
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  obtain ⟨-, -, hyN, -⟩ := hyf
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ (-ρ) := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JI P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 120 * (L2 N) ^ (-ρ) := by positivity
  rcases le_total (J1 N) (⌊recipSumLe P (yI N) / 8⌋₊) with hcase | hcase
  · have hJlow : L3 N - 1 ≤ (JI P N : ℝ) := JI_lower P hcase (by linarith)
    have hpow : (L2 N) ^ Real.log 4 / 4 ≤ (4 : ℝ) ^ (JI P N) := by
      have h1 : (4 : ℝ) ^ (JI P N) = (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N - 1) ≤ (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (4 : ℝ) ^ (L3 N - 1) = (L2 N) ^ Real.log 4 / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        congr 1
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), Real.rpow_def_of_pos ht0, hulog]
        congr 1
        ring
      rw [h1, ← h3]; exact h2
    have hL2two : L2 (2 * N) ≤ L2 N + 1 := by
      have hlogN : 1 < Real.log N := logN_gt_one hN
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
      have hNne : ((N : ℝ)) ≠ 0 := by
        have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        exact ne_of_gt (by linarith)
      have hlog2N : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
        rw [hcast, Real.log_mul (by norm_num) hNne]
      have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by rw [hlog2N]; linarith
      have h1 : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by rw [hlog2N]; linarith
      have h2 : L2 (2 * N) ≤ Real.log (2 * Real.log N) := Real.log_le_log hlog2Npos h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h4 : Real.log (Real.log N) = L2 N := rfl
      linarith [h2, h4.le, h4.ge]
    have hcrude : recipSumLe P (2 * N) ≤ 12 * L2 (2 * N) + 21 :=
      recipSumLe_le_crude P (by omega)
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 30 * L2 N := by
      have h5 : (JI P N : ℝ) ≤ L3 N := hJle
      linarith
    have h30 : (0 : ℝ) ≤ 30 * L2 N := by linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) :=
      div_le_div₀ h30 hnum (by positivity) hpow
    have hfin : (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) = 120 * (L2 N) ^ (-ρ) := by
      rw [hρdef, show -(Real.log 4 - 1) = 1 - Real.log 4 by ring, Real.rpow_sub ht0,
        Real.rpow_one]
      field_simp
      norm_num
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · have hJeq : JI P N = ⌊recipSumLe P (yI N) / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P (yI N) < 8 * (JI P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P (yI N) / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P (yI N) + recipSumIoc P (yI N) (2 * N) :=
      recipSumLe_add_recipSumIoc P (le_trans hyN (by omega))
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 13 * (JI P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]

theorem tailOK_fresh (hF : FreshMassZero P) (hP : DivergentRecip P) : TailOK P (JI P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_fresh P hF hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JI P N) N hN

theorem kmt_along_fresh (hF : FreshMassZero P) (hP : DivergentRecip P) : KMT_along P (JI P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      (4 * Real.pi * |(h : ℝ)| / 3) * (2 * recipSumIoc P (yI N) N + (JI P N : ℝ) / N)
        + Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N))
        + (2 * (JI P N : ℝ) ^ 2 + 2 * (JI P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
            * Real.exp (-1 / (8 * (JI P N : ℝ) ^ 2 * epsI N))) atTop (𝓝 0) := by
    have := ((term_one_fresh P hF h).add (term_two_iter3 P hP)).add (term_three_iter3 P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [regime_iter3 P hP,
    (JI_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hR hJ
  have hntw : NontrivialWindow (JI P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := window_bound_regime_h P h hntw hR
  have hy : yOf N (epsI N) = yI N := rfl
  rw [hy] at hb
  linarith [hb]

/-- **Abstract consumer.**  Divergent reciprocal sum plus vanishing fresh mass in the cutoff
window give a normal base-4 Lambert constant.  No density hypothesis. -/
theorem isNormal_subsetLambert_of_freshMassZero (hF : FreshMassZero P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JI P) (tailOK_fresh P hF hP) (kmt_along_fresh P hF hP)

/-- The little-o density hypothesis implies vanishing fresh mass (dominated Abel to `2N`). -/
theorem freshMassZero_of_sparseL4o (hS : SparseL4o P) : FreshMassZero P := by
  rw [FreshMassZero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hη : (0 : ℝ) < ε / 200 := by linarith
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, L4_tendsto.eventually_ge_atTop 1,
    yI_facts, J1_facts, fresh_bound_L4o P hS hη] with N hN _hL hL3 hv1 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hj0 : (0 : ℝ) < ((J1 N : ℕ) : ℝ) := by linarith
  have hv0 : (0 : ℝ) < L4 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hratio2 : Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N) ≤ 4 * ((J1 N : ℕ) : ℝ) ^ 4 := by
    rw [div_le_iff₀ hlogypos]
    rw [div_le_iff₀ hlogypos] at hratio
    linarith
  have hlr : Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
      ≤ Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4) :=
    Real.log_le_log (div_pos hlog2Npos hlogypos) hratio2
  have hexp : Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4)
      = Real.log 4 + 4 * Real.log (J1 N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hb := hfb (2 * N) (le_trans hyN (by omega))
  have hδ0 : (0 : ℝ) ≤ 2 * (ε / 200) / L4 N := by positivity
  have hstep : recipSumIoc P (yI N) (2 * N)
      ≤ (2 * (ε / 200) / L4 N) * (9 + 12 * (2 + 4 * L4 N)) := by
    refine le_trans hb ?_
    have h9 : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
        ≤ 9 + 12 * (2 + 4 * L4 N) := by
      rw [hexp] at hlr; linarith
    exact mul_le_mul_of_nonneg_left h9 hδ0
  have hfin : (2 * (ε / 200) / L4 N) * (9 + 12 * (2 + 4 * L4 N)) < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hv0]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hv1)]
  have hnn := recipSumIoc_nonneg P (yI N) (2 * N)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

end NormalNumbers.PrimeModel.FamilyIter
