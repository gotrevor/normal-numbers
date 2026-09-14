/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Wiring
import NormalNumbers.G4LocalContraction

/-!
# G4 disjunctivity, §4E: product Fejér smoothing of the separating test (`PropJackson`)

Brief §4E / draft (9.2): the clipped test `f = min(1, dAv(·, E)/ρ)` is `1/ρ`-Lipschitz for the
**average** coordinate metric `dAv`, so smoothing it with a *product* kernel costs only the
one-dimensional first moment — the error is dimension-free.  We use the Fejér kernel

  `F_D(t) = ‖∑_{k ≤ D} e(kt)‖² / (D+1) ≥ 0`,   `∫ F_D = 1`,

with the two pointwise bounds `F_D ≤ D+1` and `‖t‖ · ‖∑_{k≤D} e(kt)‖ ≤ 1/2` (geometric sum and
Jordan's inequality).  Splitting at `‖t‖ = a` gives the *pointwise* estimate
`‖t‖ F_D(t) ≤ a F_D(t) + 1/(4(D+1)a)`, hence the first moment `∫ ‖t‖ F_D ≤ 1/√(D+1)` at
`a = 1/(2√(D+1))` — no interval integral is ever evaluated.  (`O(1/√D)` instead of the draft's
`O(1/D)`; the schedule only needs `D` polynomial in `1/(εη)`, so this is harmless.)

The Fourier expansion `F_D = ∑_{|m| ≤ D} c_m e(mt)` is obtained by counting fibres of
`(k,l) ↦ k − l`; we only use `0 ≤ c_m ≤ 1` and `c_0 = 1`, never the closed form `1 − |m|/(D+1)`.

Main result: `Frame.propJackson`: every frame satisfies
`PropJackson (1/(res · √(D+1))) ((2D+1)^r)`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### The one-dimensional Fejér kernel -/

/-- The partial sum `∑_{k ≤ D} e(kt)`. -/
noncomputable def dirSum (D : ℕ) (t : UnitAddCircle) : ℂ :=
  ∑ k ∈ range (D + 1), fourier (k : ℤ) t

/-- The Fejér kernel `‖∑_{k ≤ D} e(kt)‖² / (D+1)`. -/
noncomputable def fejer (D : ℕ) (t : UnitAddCircle) : ℝ := ‖dirSum D t‖ ^ 2 / (D + 1)

lemma continuous_dirSum (D : ℕ) : Continuous (dirSum D) := by
  unfold dirSum; fun_prop

lemma continuous_fejer (D : ℕ) : Continuous (fejer D) :=
  ((continuous_dirSum D).norm.pow 2).div_const _

lemma fejer_nonneg (D : ℕ) (t : UnitAddCircle) : 0 ≤ fejer D t := by
  unfold fejer; positivity

lemma norm_dirSum_le (D : ℕ) (t : UnitAddCircle) : ‖dirSum D t‖ ≤ D + 1 := by
  unfold dirSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (D + 1), ‖fourier (k : ℤ) t‖ ≤ ∑ _k ∈ range (D + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => by rw [fourier_apply]; exact (Circle.norm_coe _).le
    _ = D + 1 := by simp

lemma fejer_le (D : ℕ) (t : UnitAddCircle) : fejer D t ≤ D + 1 := by
  unfold fejer
  rw [div_le_iff₀ (by positivity)]
  have h := norm_dirSum_le D t
  have h0 := norm_nonneg (dirSum D t)
  nlinarith

/-- `fourier k (x : 𝕋) = e(x)^k`. -/
lemma fourier_natCast_coe (k : ℕ) (x : ℝ) :
    fourier (k : ℤ) (x : UnitAddCircle) = ee x ^ k := by
  rw [fourier_coe_apply, ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖e(x) − 1‖ ≥ 4 dist(x, ℤ)`. -/
lemma four_mul_distZ_le_norm_ee_sub_one (x : ℝ) : 4 * distZ x ≤ ‖ee x - 1‖ := by
  have h1 : ‖ee x - 1‖ ^ 2 = 2 * (1 - Real.cos (2 * Real.pi * x)) := by
    rw [normSq_expand]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ee_re, sub_zero]
    have him : (ee x).im = Real.sin (2 * Real.pi * x) := Complex.exp_ofReal_mul_I_im _
    rw [him]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
  have h2 := eight_mul_distZ_sq_le_one_sub_cos x
  have h3 : (4 * distZ x) ^ 2 ≤ ‖ee x - 1‖ ^ 2 := by rw [h1]; nlinarith
  have := distZ_nonneg x
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3

/-- The geometric-sum bound: `‖t‖ · ‖∑_{k ≤ D} e(kt)‖ ≤ 1/2`. -/
lemma norm_mul_norm_dirSum_le (D : ℕ) (t : UnitAddCircle) : ‖t‖ * ‖dirSum D t‖ ≤ 1 / 2 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hgeom : dirSum D (x : UnitAddCircle) * (ee x - 1) = ee x ^ (D + 1) - 1 := by
    unfold dirSum
    simp_rw [fourier_natCast_coe]
    exact geom_sum_mul (ee x) (D + 1)
  have hnorm : ‖dirSum D (x : UnitAddCircle)‖ * ‖ee x - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖ee x ^ (D + 1) - 1‖ ≤ ‖ee x ^ (D + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ee]; norm_num
  have hd := four_mul_distZ_le_norm_ee_sub_one x
  rw [← distZ_eq_norm]
  have h0 := norm_nonneg (dirSum D (x : UnitAddCircle))
  have h1 := distZ_nonneg x
  nlinarith

/-- The pointwise split: `‖t‖ F_D(t) ≤ a F_D(t) + 1/(4(D+1)a)` for every `a > 0`. -/
lemma norm_mul_fejer_le (D : ℕ) {a : ℝ} (ha : 0 < a) (t : UnitAddCircle) :
    ‖t‖ * fejer D t ≤ a * fejer D t + 1 / (4 * (D + 1) * a) := by
  have hF := fejer_nonneg D t
  have hD : (0 : ℝ) < D + 1 := by positivity
  by_cases hta : ‖t‖ ≤ a
  · have : ‖t‖ * fejer D t ≤ a * fejer D t := mul_le_mul_of_nonneg_right hta hF
    have : 0 ≤ 1 / (4 * (D + 1) * a) := by positivity
    linarith
  · push Not at hta
    have hgeo := norm_mul_norm_dirSum_le D t
    have h0 := norm_nonneg (dirSum D t)
    have ht0 : 0 < ‖t‖ := ha.trans hta
    -- ‖t‖ F = (‖t‖‖S‖)² / ((D+1)‖t‖) ≤ (1/4) / ((D+1) ‖t‖) ≤ 1/(4(D+1)a)
    have key : ‖t‖ * fejer D t ≤ 1 / (4 * (D + 1) * a) := by
      unfold fejer
      rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
      have hsq : (‖t‖ * ‖dirSum D t‖) ^ 2 ≤ (1 / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hgeo 2
      have : ‖t‖ * ‖dirSum D t‖ ^ 2 * a ≤ (‖t‖ * ‖dirSum D t‖) ^ 2 := by
        rw [mul_pow]
        have : ‖t‖ * ‖dirSum D t‖ ^ 2 * a = ‖t‖ ^ 2 * ‖dirSum D t‖ ^ 2 * (a / ‖t‖) := by
          field_simp
        rw [this]
        have hle : a / ‖t‖ ≤ 1 := by rw [div_le_one ht0]; exact hta.le
        exact mul_le_of_le_one_right (by positivity) hle
      nlinarith
    have : 0 ≤ a * fejer D t := by positivity
    linarith

/-! ### Fourier expansion of the Fejér kernel -/

/-- The fibre of `(k,l) ↦ k − l` over `m` in `[0,D]²`. -/
def fejerFibre (D : ℕ) (m : ℤ) : Finset (ℕ × ℕ) :=
  (range (D + 1) ×ˢ range (D + 1)).filter fun kl => ((kl.1 : ℤ) - kl.2) = m

/-- The Fejér coefficient `c_m = #fibre / (D+1)`. -/
noncomputable def fejerCoeff (D : ℕ) (m : ℤ) : ℝ := (fejerFibre D m).card / (D + 1)

lemma fejerCoeff_nonneg (D : ℕ) (m : ℤ) : 0 ≤ fejerCoeff D m := by
  unfold fejerCoeff; positivity

lemma card_fejerFibre_le (D : ℕ) (m : ℤ) : (fejerFibre D m).card ≤ D + 1 := by
  have : (fejerFibre D m).card ≤ (range (D + 1)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro kl hkl
      unfold fejerFibre at hkl
      rw [Finset.mem_coe, mem_filter, mem_product] at hkl
      exact hkl.1.1
    · intro kl hkl kl' hkl' h
      rw [Finset.mem_coe] at hkl hkl'
      unfold fejerFibre at hkl hkl'
      rw [mem_filter] at hkl hkl'
      have h1 := hkl.2
      have h2 := hkl'.2
      ext
      · exact h
      · omega
  simpa using this

lemma fejerCoeff_le_one (D : ℕ) (m : ℤ) : fejerCoeff D m ≤ 1 := by
  unfold fejerCoeff
  rw [div_le_one (by positivity)]
  exact_mod_cast card_fejerFibre_le D m

lemma fejerFibre_zero (D : ℕ) : fejerFibre D 0 = (range (D + 1)).image fun k => (k, k) := by
  ext ⟨k, l⟩
  simp only [fejerFibre, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hk, hl⟩, h⟩
    exact ⟨k, hk, rfl, by omega⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    exact ⟨⟨ha, ha⟩, by simp⟩

lemma fejerCoeff_zero (D : ℕ) : fejerCoeff D 0 = 1 := by
  unfold fejerCoeff
  rw [fejerFibre_zero, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp only [card_range]
  push_cast
  exact div_self (by positivity)

/-- `F_D(t) = ∑_{|m| ≤ D} c_m e(mt)`. -/
lemma fejer_expand (D : ℕ) (t : UnitAddCircle) :
    (fejer D t : ℂ) = ∑ m ∈ Icc (-(D : ℤ)) D, (fejerCoeff D m : ℂ) * fourier m t := by
  have hsq : (fejer D t : ℂ) = dirSum D t * (starRingEnd ℂ) (dirSum D t) / (D + 1) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    unfold fejer
    push_cast
    ring
  rw [hsq]
  unfold dirSum
  rw [map_sum, Finset.sum_mul_sum]
  simp_rw [← fourier_neg, ← fourier_add]
  rw [← Finset.sum_product']
  have hmaps : ∀ kl ∈ range (D + 1) ×ˢ range (D + 1),
      ((kl.1 : ℤ) - kl.2) ∈ Icc (-(D : ℤ)) D := by
    intro kl hkl
    simp only [mem_product, mem_range] at hkl
    simp only [mem_Icc]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ kl ∈ (range (D + 1) ×ˢ range (D + 1)).filter (fun kl => ((kl.1 : ℤ) - kl.2) = m),
      fourier ((kl.1 : ℤ) + -(kl.2 : ℤ)) t = fourier m t := by
    intro kl hkl
    simp only [mem_filter] at hkl
    rw [← hkl.2]; ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_const]
  unfold fejerCoeff fejerFibre
  simp only [nsmul_eq_mul]
  push_cast
  ring

lemma integrable_fourier (m : ℤ) : Integrable (fun t : UnitAddCircle => fourier m t) volume :=
  Integrable.of_bound (fourier m).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => by rw [fourier_apply]; exact (Circle.norm_coe _).le)

/-- `∫ F_D = 1` (the constant coefficient). -/
lemma integral_fejer (D : ℕ) : ∫ t : UnitAddCircle, fejer D t = 1 := by
  have hc : ∫ t : UnitAddCircle, (fejer D t : ℂ) = 1 := by
    simp_rw [fejer_expand]
    rw [integral_finsetSum _ (fun m _ => (integrable_fourier m).const_mul _)]
    have h0 : (0 : ℤ) ∈ Icc (-(D : ℤ)) D := by simp
    rw [← Finset.add_sum_erase _ _ h0]
    rw [Finset.sum_eq_zero, add_zero]
    · rw [integral_const_mul, fejerCoeff_zero]
      simp
    · intro m hm
      rw [integral_const_mul, integral_fourier_eq_zero (Finset.ne_of_mem_erase hm), mul_zero]
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

/-! ### The product kernel on the torus -/

/-- The product Fejér kernel `P(w) = ∏_ν F_D(w_ν)`. -/
noncomputable def jackKer (r D : ℕ) (w : Torus r) : ℝ := ∏ ν, fejer D (w ν)

/-- Its Fourier coefficient `∏_ν c_{q_ν}`. -/
noncomputable def jackCoeff (r D : ℕ) (q : Fin r → ℤ) : ℝ := ∏ ν, fejerCoeff D (q ν)

lemma continuous_jackKer (r D : ℕ) : Continuous (jackKer r D) :=
  continuous_finsetProd _ fun ν _ => (continuous_fejer D).comp (continuous_apply ν)

lemma jackKer_nonneg (r D : ℕ) (w : Torus r) : 0 ≤ jackKer r D w :=
  Finset.prod_nonneg fun ν _ => fejer_nonneg D (w ν)

lemma jackCoeff_nonneg (r D : ℕ) (q : Fin r → ℤ) : 0 ≤ jackCoeff r D q :=
  Finset.prod_nonneg fun ν _ => fejerCoeff_nonneg D (q ν)

lemma jackCoeff_le_one (r D : ℕ) (q : Fin r → ℤ) : jackCoeff r D q ≤ 1 :=
  Finset.prod_le_one (fun ν _ => fejerCoeff_nonneg D (q ν)) fun ν _ => fejerCoeff_le_one D (q ν)

/-- Continuous functions on the (compact) torus are integrable. -/
lemma integrable_of_continuous_torus {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Torus r → E} (hf : Continuous f) : Integrable f volume :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- `P(w) = ∑_{q ∈ box} (∏ c_{q_ν}) χ_q(w)`. -/
lemma jackKer_expand (r D : ℕ) (w : Torus r) :
    (jackKer r D w : ℂ) = ∑ q ∈ fourierBox r D, (jackCoeff r D q : ℂ) * torusChar q w := by
  unfold jackKer jackCoeff fourierBox torusChar
  push_cast
  simp_rw [fejer_expand]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]

lemma integral_jackKer (r D : ℕ) : ∫ w : Torus r, jackKer r D w = 1 := by
  unfold jackKer
  rw [integral_fintype_prod_volume_eq_prod (fun _ t => fejer D t)]
  simp [integral_fejer]

/-- **Coordinate first moment**: `∫ ‖w_ν‖ P(w) dw ≤ 1/√(D+1)`. -/
lemma integral_norm_mul_jackKer_le (r D : ℕ) (ν : Fin r) :
    ∫ w : Torus r, ‖w ν‖ * jackKer r D w ≤ 1 / Real.sqrt (D + 1) := by
  have hsq : 0 < Real.sqrt (D + 1) := Real.sqrt_pos.2 (by positivity)
  set a : ℝ := 1 / (2 * Real.sqrt (D + 1)) with ha_def
  have ha : 0 < a := by positivity
  set b : ℝ := 1 / (4 * (D + 1) * a) with hb_def
  have hb : 0 ≤ b := by positivity
  -- the "all but ν" product
  let g : Torus r → ℝ := fun w => ∏ μ, (if μ = ν then 1 else fejer D (w μ))
  have hg_eq : ∀ w, g w = ∏ μ ∈ univ.erase ν, fejer D (w μ) := by
    intro w
    simp only [g]
    rw [← Finset.mul_prod_erase univ _ (mem_univ ν), if_pos rfl, one_mul]
    exact Finset.prod_congr rfl fun μ hμ => if_neg (Finset.ne_of_mem_erase hμ)
  have hg_int : ∫ w, g w = 1 := by
    simp only [g]
    rw [integral_fintype_prod_volume_eq_prod (fun μ t => if μ = ν then (1 : ℝ) else fejer D t)]
    refine Finset.prod_eq_one fun μ _ => ?_
    by_cases h : μ = ν
    · simp [h]
    · simp [h, integral_fejer]
  have hg_cont : Continuous g :=
    continuous_finsetProd _ fun μ _ => by
      by_cases h : μ = ν
      · simp [h]; exact continuous_const
      · simp only [h, if_false]; exact (continuous_fejer D).comp (continuous_apply μ)
  -- pointwise
  have hpt : ∀ w : Torus r, ‖w ν‖ * jackKer r D w ≤ a * jackKer r D w + b * g w := by
    intro w
    unfold jackKer
    rw [hg_eq, ← Finset.mul_prod_erase univ _ (mem_univ ν)]
    have hR : 0 ≤ ∏ μ ∈ univ.erase ν, fejer D (w μ) :=
      Finset.prod_nonneg fun μ _ => fejer_nonneg D _
    have h1 := norm_mul_fejer_le D ha (w ν)
    rw [← hb_def] at h1
    calc ‖w ν‖ * (fejer D (w ν) * ∏ μ ∈ univ.erase ν, fejer D (w μ))
        = (‖w ν‖ * fejer D (w ν)) * ∏ μ ∈ univ.erase ν, fejer D (w μ) := by ring
      _ ≤ (a * fejer D (w ν) + b) * ∏ μ ∈ univ.erase ν, fejer D (w μ) :=
          mul_le_mul_of_nonneg_right h1 hR
      _ = _ := by ring
  have hint1 : Integrable (fun w : Torus r => ‖w ν‖ * jackKer r D w) volume :=
    integrable_of_continuous_torus (((continuous_apply ν).norm).mul (continuous_jackKer r D))
  have hint2 : Integrable (fun w : Torus r => a * jackKer r D w + b * g w) volume :=
    integrable_of_continuous_torus
      ((continuous_const.mul (continuous_jackKer r D)).add (continuous_const.mul hg_cont))
  calc ∫ w : Torus r, ‖w ν‖ * jackKer r D w
      ≤ ∫ w : Torus r, (a * jackKer r D w + b * g w) := integral_mono hint1 hint2 hpt
    _ = a * 1 + b * 1 := by
        rw [integral_add (f := fun w => a * jackKer r D w) (g := fun w => b * g w)
          (integrable_of_continuous_torus (continuous_const.mul (continuous_jackKer r D)))
          (integrable_of_continuous_torus (continuous_const.mul hg_cont)),
          integral_const_mul, integral_const_mul, integral_jackKer, hg_int]
    _ = 1 / Real.sqrt (D + 1) := by
        rw [hb_def, ha_def]
        have hs : Real.sqrt (D + 1) ^ 2 = D + 1 := Real.sq_sqrt (by positivity)
        field_simp
        nlinarith [hs]

/-! ### Evenness of the coefficients -/

lemma card_fejerFibre_neg (D : ℕ) (m : ℤ) : (fejerFibre D (-m)).card = (fejerFibre D m).card := by
  refine Finset.card_bij' (fun kl _ => kl.swap) (fun kl _ => kl.swap) ?_ ?_ ?_ ?_
  · intro kl hkl
    unfold fejerFibre at hkl ⊢
    rw [mem_filter, mem_product] at hkl ⊢
    simp only [Prod.fst_swap, Prod.snd_swap]
    exact ⟨⟨hkl.1.2, hkl.1.1⟩, by linarith [hkl.2]⟩
  · intro kl hkl
    unfold fejerFibre at hkl ⊢
    rw [mem_filter, mem_product] at hkl ⊢
    simp only [Prod.fst_swap, Prod.snd_swap]
    exact ⟨⟨hkl.1.2, hkl.1.1⟩, by linarith [hkl.2]⟩
  · intro kl _; simp
  · intro kl _; simp

lemma fejerCoeff_neg (D : ℕ) (m : ℤ) : fejerCoeff D (-m) = fejerCoeff D m := by
  unfold fejerCoeff; rw [card_fejerFibre_neg]

lemma jackCoeff_neg (r D : ℕ) (q : Fin r → ℤ) : jackCoeff r D (-q) = jackCoeff r D q := by
  unfold jackCoeff
  simp_rw [Pi.neg_apply, fejerCoeff_neg]

lemma neg_mem_fourierBox {r D : ℕ} {q : Fin r → ℤ} (hq : q ∈ fourierBox r D) :
    -q ∈ fourierBox r D := by
  rw [mem_fourierBox] at hq ⊢
  intro ν; rw [Pi.neg_apply, abs_neg]; exact hq ν

/-- Reindexing a box sum by `q ↦ −q`. -/
lemma sum_fourierBox_neg {r D : ℕ} (f : (Fin r → ℤ) → ℂ) :
    ∑ q ∈ fourierBox r D, f (-q) = ∑ q ∈ fourierBox r D, f q :=
  Finset.sum_nbij' (fun q => -q) (fun q => -q) (fun q hq => neg_mem_fourierBox hq)
    (fun q hq => neg_mem_fourierBox hq) (fun q _ => neg_neg q) (fun q _ => neg_neg q)
    (fun q _ => by simp)

/-! ### Characters of a difference -/

lemma fourier_arg_add (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fourier_arg_neg (n : ℤ) (x : UnitAddCircle) : fourier n (-x) = fourier (-n) x := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

lemma torusChar_sub {r : ℕ} (q : Fin r → ℤ) (z y : Torus r) :
    torusChar q (z - y) = torusChar q z * torusChar (-q) y := by
  unfold torusChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [Pi.sub_apply, sub_eq_add_neg, fourier_arg_add, fourier_arg_neg, Pi.neg_apply]

/-! ### Lipschitz control of the clipped test in the average metric -/

lemma dAv_comm {r : ℕ} (y y' : Torus r) : dAv y y' = dAv y' y := by
  unfold dAv; simp_rw [dist_comm]

lemma abs_clipTest_sub_le {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (y y' : Torus r) : |clipTest E ρ y - clipTest E ρ y'| ≤ dAv y y' / ρ := by
  unfold clipTest
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, ← sub_div, abs_div, abs_of_pos hρ]
  refine max_le (div_nonneg (dAv_nonneg _ _) hρ.le) (div_le_div_of_nonneg_right ?_ hρ.le)
  have h1 := dAvSet_sub_le hE y y'
  have h2 := dAvSet_sub_le hE y' y
  rw [dAv_comm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma dAv_add_left {r : ℕ} (y w : Torus r) : dAv (y + w) y = (∑ ν, ‖w ν‖) / r := by
  unfold dAv
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Pi.add_apply]
  exact dist_self_add_left (w ν) (y ν)

/-! ### The smoothed test and `PropJackson` -/

lemma norm_integral_le_one_of_le_one {r : ℕ} {h : Torus r → ℂ} (hh : ∀ w, ‖h w‖ ≤ 1) :
    ‖∫ w : Torus r, h w‖ ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus r)))
    (Filter.Eventually.of_forall hh)
  simpa using this

namespace Frame

variable (fr : Frame)

/-- The Fourier coefficients of the smoothed test `y ↦ ∫ f(y+w) P(w) dw`:
`c_q = (∏ c_{q_ν}) · ∫ f · χ_{−q}`. -/
noncomputable def jackC (q : Fin fr.r → ℤ) : ℂ :=
  (jackCoeff fr.r fr.D q : ℂ) * ∫ z : Torus fr.r, (fr.test z : ℂ) * torusChar (-q) z

lemma continuous_test : Continuous fr.test := continuous_clipTest fr.image_nonempty fr.res

lemma test_nonneg (y : Torus fr.r) : 0 ≤ fr.test y := clipTest_nonneg _ fr.res_pos y

lemma test_le_one (y : Torus fr.r) : fr.test y ≤ 1 := clipTest_le_one _ _ y

/-- The smoothed test `∫ f(y+w) P(w) dw` is the trigonometric polynomial `∑_q c_q χ_q`. -/
theorem sum_jackC_eq (y : Torus fr.r) :
    ∑ q ∈ fourierBox fr.r fr.D, fr.jackC q * torusChar q y
      = ∫ w : Torus fr.r, (fr.test (y + w) : ℂ) * (jackKer fr.r fr.D w : ℂ) := by
  -- translate `w = z − y`
  have hsub : ∫ w : Torus fr.r, (fr.test (y + w) : ℂ) * (jackKer fr.r fr.D w : ℂ)
      = ∫ z : Torus fr.r, (fr.test z : ℂ) * (jackKer fr.r fr.D (z - y) : ℂ) := by
    rw [← integral_add_left_eq_self (fun z => (fr.test z : ℂ) * (jackKer fr.r fr.D (z - y) : ℂ)) y]
    simp only [add_sub_cancel_left]
  rw [hsub]
  simp_rw [jackKer_expand, torusChar_sub, Finset.mul_sum]
  rw [integral_finsetSum (fourierBox fr.r fr.D)
    (f := fun q z => (fr.test z : ℂ) * ((jackCoeff fr.r fr.D q : ℂ) * (torusChar q z * torusChar (-q) y)))
    fun q _ => integrable_of_continuous_torus
      ((Complex.continuous_ofReal.comp fr.continuous_test).mul
        (continuous_const.mul ((continuous_torusChar q).mul continuous_const)))]
  rw [← sum_fourierBox_neg]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold jackC
  rw [neg_neg, jackCoeff_neg, mul_assoc, ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- **Uniform approximation**: the smoothed test is within `1/(res √(D+1))` of the test. -/
theorem norm_sum_jackC_sub_le (y : Torus fr.r) :
    ‖(∑ q ∈ fourierBox fr.r fr.D, fr.jackC q * torusChar q y) - (fr.test y : ℂ)‖
      ≤ 1 / (fr.res * Real.sqrt (fr.D + 1)) := by
  have hρ := fr.res_pos
  have hsq : 0 < Real.sqrt (fr.D + 1) := Real.sqrt_pos.2 (by positivity)
  rw [sum_jackC_eq]
  -- the difference is the real integral `∫ (f(y+w) − f(y)) P(w)`
  have hK := integral_jackKer fr.r fr.D
  have hcont_shift : Continuous fun w : Torus fr.r => fr.test (y + w) :=
    fr.continuous_test.comp (continuous_const.add continuous_id)
  have hreal : (∫ w : Torus fr.r, (fr.test (y + w) : ℂ) * (jackKer fr.r fr.D w : ℂ))
      - (fr.test y : ℂ)
      = ((∫ w : Torus fr.r, (fr.test (y + w) - fr.test y) * jackKer fr.r fr.D w : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have h1 : (fr.test y : ℂ) = ∫ w : Torus fr.r, ((fr.test y * jackKer fr.r fr.D w : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul, hK, mul_one]
    rw [h1, ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only
      push_cast
      ring
    · exact integrable_of_continuous_torus
        ((Complex.continuous_ofReal.comp hcont_shift).mul
          (Complex.continuous_ofReal.comp (continuous_jackKer _ _)))
    · exact integrable_of_continuous_torus
        (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_jackKer _ _)))
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  -- pointwise: |f(y+w) − f(y)| P(w) ≤ (∑_ν ‖w_ν‖ / r) P(w) / res
  have hpt : ∀ w : Torus fr.r, |(fr.test (y + w) - fr.test y) * jackKer fr.r fr.D w|
      ≤ ((∑ ν, ‖w ν‖) / fr.r) / fr.res * jackKer fr.r fr.D w := by
    intro w
    rw [abs_mul, abs_of_nonneg (jackKer_nonneg _ _ _)]
    refine mul_le_mul_of_nonneg_right ?_ (jackKer_nonneg _ _ _)
    have := abs_clipTest_sub_le fr.image_nonempty hρ (y + w) y
    rwa [dAv_add_left] at this
  have hint_abs : Integrable (fun w : Torus fr.r =>
      |(fr.test (y + w) - fr.test y) * jackKer fr.r fr.D w|) volume :=
    integrable_of_continuous_torus
      (((hcont_shift.sub continuous_const).mul (continuous_jackKer _ _)).abs)
  have hint_maj : Integrable (fun w : Torus fr.r =>
      ((∑ ν, ‖w ν‖) / fr.r) / fr.res * jackKer fr.r fr.D w) volume :=
    integrable_of_continuous_torus
      ((((continuous_finsetSum _ fun ν _ => (continuous_apply ν).norm).div_const _).div_const _).mul
        (continuous_jackKer _ _))
  calc |∫ w : Torus fr.r, (fr.test (y + w) - fr.test y) * jackKer fr.r fr.D w|
      ≤ ∫ w : Torus fr.r, |(fr.test (y + w) - fr.test y) * jackKer fr.r fr.D w| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w : Torus fr.r, ((∑ ν, ‖w ν‖) / fr.r) / fr.res * jackKer fr.r fr.D w :=
        integral_mono hint_abs hint_maj hpt
    _ = (1 / fr.res) * ((1 / fr.r) * ∑ ν, ∫ w : Torus fr.r, ‖w ν‖ * jackKer fr.r fr.D w) := by
        rw [← integral_finsetSum, ← integral_const_mul, ← integral_const_mul]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
          exact Finset.sum_congr rfl fun ν _ => by ring
        · intro ν _
          exact integrable_of_continuous_torus ((continuous_apply ν).norm.mul (continuous_jackKer _ _))
    _ ≤ (1 / fr.res) * ((1 / fr.r) * ∑ _ν : Fin fr.r, 1 / Real.sqrt (fr.D + 1)) := by
        gcongr with ν _
        exact integral_norm_mul_jackKer_le fr.r fr.D ν
    _ ≤ 1 / (fr.res * Real.sqrt (fr.D + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hr : (1 / (fr.r : ℝ)) * (fr.r : ℝ) ≤ 1 := by
          rcases Nat.eq_zero_or_pos fr.r with h | h
          · simp [h]
          · rw [one_div, inv_mul_cancel₀ (by exact_mod_cast h.ne')]
        calc (1 / fr.res) * ((1 / fr.r) * ((fr.r : ℝ) * (1 / Real.sqrt (fr.D + 1))))
            = (1 / fr.res) * (1 / Real.sqrt (fr.D + 1)) * ((1 / (fr.r : ℝ)) * fr.r) := by ring
          _ ≤ (1 / fr.res) * (1 / Real.sqrt (fr.D + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = 1 / (fr.res * Real.sqrt (fr.D + 1)) := by rw [mul_one, one_div_mul_one_div]

lemma norm_jackC_le_one (q : Fin fr.r → ℤ) : ‖fr.jackC q‖ ≤ 1 := by
  unfold jackC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jackCoeff_nonneg _ _ _)]
  refine mul_le_one₀ (jackCoeff_le_one _ _ _) (norm_nonneg _) ?_
  refine norm_integral_le_one_of_le_one fun z => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fr.test_nonneg z)]
  exact mul_le_one₀ (fr.test_le_one z) (norm_nonneg _) (norm_torusChar_le _ _)

lemma card_fourierBox (r D : ℕ) : (fourierBox r D).card = (2 * D + 1) ^ r := by
  unfold fourierBox
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  omega

/-- **`PropJackson` holds for every frame**, with `κ = 1/(res √(D+1))` and
`Λ = (2D+1)^r`. -/
theorem propJackson :
    fr.PropJackson (1 / (fr.res * Real.sqrt (fr.D + 1))) (((2 * fr.D + 1) ^ fr.r : ℕ) : ℝ) := by
  refine ⟨fr.jackC, fr.norm_sum_jackC_sub_le, ?_⟩
  calc ∑ q ∈ (fourierBox fr.r fr.D).erase 0, ‖fr.jackC q‖
      ≤ ∑ _q ∈ (fourierBox fr.r fr.D).erase 0, (1 : ℝ) :=
        Finset.sum_le_sum fun q _ => fr.norm_jackC_le_one q
    _ = ((fourierBox fr.r fr.D).erase 0).card := by simp
    _ ≤ (fourierBox fr.r fr.D).card := by exact_mod_cast Finset.card_erase_le
    _ = _ := by rw [card_fourierBox]

end Frame

end NormalNumbers.G4
