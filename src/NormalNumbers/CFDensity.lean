/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw
import NormalNumbers.CFContraction

/-!
# W3 — the conditional density identity (route step 1)

Proves `volume_inter_preimage_aux`: for any digit word `w` (including `[]`)
and measurable `A ⊆ (0,1)`,

  `|I_w ∩ T^{-|w|}(A)| = (∫_A h_{t(w)}) · |I_w|`,

with `t(w) = qₙ₋₁/qₙ` (`tParam`).  This is the exact statement of the
frozen `volume_inter_preimage_eq_integral` extended to the empty word
(`t([]) = 0`, uniform density) so that induction can run.

**Method** (supersedes the `cylMap` plan of the HANDOFF — no composite
Jacobians): reverse induction on `w`.  Appending a digit `b` at the end
replaces `A` by `I_{[b]} ∩ T⁻¹A`, which up to the (null) rationals is the
image of `A` under the single smooth branch `y ↦ 1/(b+y)`; one
one-dimensional change of variables plus the exact pointwise identity

  `h_t(1/(b+y)) / (b+y)² = (1+t)/((b+t)(b+1+t)) · h_{1/(b+t)}(y)`

turns `∫_{I_{[b]} ∩ T⁻¹A} h_t` into `weight · ∫_A h_{t'}` with
`t' = 1/(b + t)` — exactly the tail-parameter chain of `CFContraction`.
The same single-branch lemmas feed `measurePreserving_gaussMap` and the
`G_{k+1} = P G_k` recursion behind `cylinder_mixing`.
-/

namespace NormalNumbers

open MeasureTheory

/-- The inverse branch of the Gauss map for digit `b`: `y ↦ 1/(b+y)`. -/
noncomputable def branchMap (b : ℕ) (y : ℝ) : ℝ := ((b : ℝ) + y)⁻¹

/-- The tail parameter of a word: `t(w) = K(w⁻)/K(w)`, with the junk-free
value `0` at the empty word (uniform density). -/
noncomputable def tParam (w : List ℕ) : ℝ :=
  if w = [] then 0 else (cfK w.dropLast : ℝ) / (cfK w : ℝ)

lemma tParam_nil : tParam [] = 0 := if_pos rfl

lemma tParam_mem_Icc (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    tParam w ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_ne w [] with rfl | hw
  · rw [tParam_nil]; constructor <;> norm_num
  · rw [tParam, if_neg hw]
    have h1 : (1 : ℕ) ≤ cfK w := one_le_cfK w hpos
    have h2 : cfK w.dropLast ≤ cfK w := cfK_dropLast_le w hpos
    have h1R : (0 : ℝ) < (cfK w : ℝ) := by exact_mod_cast h1
    constructor
    · positivity
    · rw [div_le_one h1R]
      exact_mod_cast h2

/-- Euler gluing on the tail parameter: appending digit `b` sends
`t ↦ 1/(b+t)`. -/
lemma tParam_concat (w : List ℕ) (b : ℕ) (hb : 1 ≤ b)
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    tParam (w ++ [b]) = ((b : ℝ) + tParam w)⁻¹ := by
  rcases eq_or_ne w [] with rfl | hw
  · simp only [List.nil_append, tParam_nil, add_zero]
    rw [tParam, if_neg (by simp)]
    simp [cfK]
  · have hK : (1 : ℕ) ≤ cfK w := one_le_cfK w hpos
    have hKR : (0 : ℝ) < (cfK w : ℝ) := by exact_mod_cast hK
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hden : (0 : ℝ) < (b : ℝ) * (cfK w : ℝ) + (cfK w.dropLast : ℝ) := by
      have h0 : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
      nlinarith
    have hden2 : (0 : ℝ) < (b : ℝ) + (cfK w.dropLast : ℝ) / (cfK w : ℝ) := by
      have h0 : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) / (cfK w : ℝ) := by positivity
      linarith
    rw [tParam, if_neg (by simp), tParam, if_neg hw]
    rw [List.dropLast_concat, cfK_concat w b hw]
    have h1 : (cfK w : ℝ) ≠ 0 := hKR.ne'
    have h2 : (b : ℝ) + (cfK w.dropLast : ℝ) / (cfK w : ℝ) ≠ 0 := hden2.ne'
    push_cast
    field_simp

/-! ## Sets modulo the rationals -/

/-- Two sets that agree on irrationals are a.e. equal. -/
lemma ae_eq_of_irrational_iff {S₁ S₂ : Set ℝ}
    (h : ∀ x : ℝ, Irrational x → (x ∈ S₁ ↔ x ∈ S₂)) :
    S₁ =ᵐ[volume] S₂ := by
  have hnull : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range _).measure_zero _
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null (fun x hx => ?_) hnull
    by_contra hxq
    exact hx.2 ((h x hxq).mp hx.1)
  · apply measure_mono_null (fun x hx => ?_) hnull
    by_contra hxq
    exact hx.2 ((h x hxq).mpr hx.1)

/-! ## Single-branch facts -/

lemma branchMap_mem_Ioo {b : ℕ} (hb : 1 ≤ b) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : branchMap b y ∈ Set.Ioo (0 : ℝ) 1 := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · rw [branchMap]; positivity
  · rw [branchMap, inv_lt_one_iff₀]
    right; linarith

lemma cfDigit_branchMap {b : ℕ} (hb : 1 ≤ b) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : cfDigit (branchMap b y) 0 = b := by
  rw [cfDigit_zero_eq_iff (branchMap_mem_Ioo hb hy) hb]
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · rw [branchMap, div_lt_iff₀ (by linarith), inv_mul_eq_div,
      lt_div_iff₀ (by linarith)]
    linarith
  · rw [branchMap, inv_le_comm₀ (by linarith) (by
      rw [one_div]; positivity), one_div, inv_inv]
    linarith

lemma gaussMap_branchMap {b : ℕ} (hb : 1 ≤ b) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : gaussMap (branchMap b y) = y := by
  have hx := branchMap_mem_Ioo hb hy
  rw [gaussMap, if_neg hx.1.ne', branchMap, inv_inv]
  rw [show (b : ℝ) + y = y + ((b : ℕ) : ℝ) by push_cast; ring,
    Int.fract_add_natCast]
  exact Int.fract_eq_self.mpr ⟨hy.1.le, hy.2⟩

lemma branchMap_gaussMap {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    branchMap (cfDigit x 0) (gaussMap x) = x := by
  rw [gaussMap_eq_inv_sub hx, branchMap]
  rw [add_sub_cancel, inv_inv]

lemma irrational_branchMap {b : ℕ} (hb : 1 ≤ b) {y : ℝ}
    (hy : Irrational y) : Irrational (branchMap b y) := by
  have h1 : Irrational ((b : ℝ) + y) := hy.natCast_add b
  simpa [branchMap] using h1.inv

/-- Membership in the one-digit cylinder. -/
lemma mem_cfCylinder_singleton {b : ℕ} {x : ℝ} :
    x ∈ cfCylinder [b] ↔ x ∈ Set.Ioo (0 : ℝ) 1 ∧ cfDigit x 0 = b := by
  constructor
  · rintro ⟨hx, hd⟩
    exact ⟨hx, by simpa using hd 0 (by simp)⟩
  · rintro ⟨hx, h0⟩
    refine ⟨hx, fun i hi => ?_⟩
    have h0' : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
    subst h0'
    simpa using h0

/-- The branch image realizes the one-step conditional set, up to the
rationals: `I_{[b]} ∩ T⁻¹(A)` agrees with `branchMap b '' A` on
irrationals. -/
lemma branch_inter_ae (b : ℕ) (hb : 1 ≤ b) (A : Set ℝ)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    (cfCylinder [b] ∩ gaussMap ⁻¹' A : Set ℝ) =ᵐ[volume] branchMap b '' A := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨hcyl, hTA⟩
    obtain ⟨hx, hd⟩ := mem_cfCylinder_singleton.mp hcyl
    refine ⟨gaussMap x, hTA, ?_⟩
    rw [← hd]
    exact branchMap_gaussMap hx
  · rintro ⟨y, hyA, rfl⟩
    have hy := hA1 hyA
    refine ⟨mem_cfCylinder_singleton.mpr
      ⟨branchMap_mem_Ioo hb hy, cfDigit_branchMap hb hy⟩, ?_⟩
    show gaussMap (branchMap b y) ∈ A
    rw [gaussMap_branchMap hb hy]
    exact hyA

/-! ## The substitution -/

/-- **Single-branch change of variables** (the measure-theory kernel):
`∫_{branchMap b '' A} h_t = (1+t)/((b+t)(b+1+t)) · ∫_A h_{1/(b+t)}`. -/
lemma setIntegral_tailDensity_branch (b : ℕ) (hb : 1 ≤ b) {A : Set ℝ}
    (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y in branchMap b '' A, tailDensity t y =
      (1 + t) / (((b : ℝ) + t) * ((b : ℝ) + 1 + t)) *
        ∫ y in A, tailDensity (((b : ℝ) + t)⁻¹) y := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  obtain ⟨ht0, ht1⟩ := ht
  -- change of variables
  have hderiv : ∀ y ∈ A, HasDerivWithinAt (branchMap b)
      (-(((b : ℝ) + y) ^ 2)⁻¹) A y := by
    intro y hy
    have hy0 := (hA1 hy).1
    have hne : (b : ℝ) + y ≠ 0 := by positivity
    have h1 : HasDerivAt (fun z : ℝ => (b : ℝ) + z) 1 y := by
      simpa using (hasDerivAt_id y).const_add (b : ℝ)
    have h2 := h1.inv hne
    have h3 : -(1 : ℝ) / ((b : ℝ) + y) ^ 2 = -(((b : ℝ) + y) ^ 2)⁻¹ := by
      ring
    rw [h3] at h2
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (branchMap b) A := by
    intro y1 h1 y2 h2 heq
    have := inv_injective heq
    linarith [this]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul hA hderiv hinj]
  -- pointwise algebra on A
  rw [show ((1 + t) / (((b : ℝ) + t) * ((b : ℝ) + 1 + t)) *
      ∫ y in A, tailDensity (((b : ℝ) + t)⁻¹) y) =
      ∫ y in A, (1 + t) / (((b : ℝ) + t) * ((b : ℝ) + 1 + t)) *
        tailDensity (((b : ℝ) + t)⁻¹) y from
    (MeasureTheory.integral_const_mul _ _).symm]
  apply MeasureTheory.setIntegral_congr_fun hA
  intro y hy
  obtain ⟨hy0, hy1⟩ := hA1 hy
  have hby : (0 : ℝ) < (b : ℝ) + y := by positivity
  have hbt : (0 : ℝ) < (b : ℝ) + t := by positivity
  have hbty : (0 : ℝ) < (b : ℝ) + t + y := by positivity
  simp only [branchMap, tailDensity]
  rw [abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < ((b : ℝ) + y) ^ 2)]
  rw [smul_eq_mul]
  have hden1 : 1 + t * ((b : ℝ) + y)⁻¹ = ((b : ℝ) + y + t) / ((b : ℝ) + y) := by
    field_simp
  have hden2 : 1 + ((b : ℝ) + t)⁻¹ * y = ((b : ℝ) + t + y) / ((b : ℝ) + t) := by
    field_simp
  rw [hden1, hden2]
  rw [div_pow, div_pow]
  field_simp
  ring

/-! ## The conditional density identity -/

/-- `cfCylinder [] = (0,1)`. -/
lemma cfCylinder_nil : cfCylinder ([] : List ℕ) = Set.Ioo (0 : ℝ) 1 := by
  ext x
  simp [cfCylinder]

/-- Digits read along the orbit: `cfDigit x (n + i) = cfDigit (Tⁿx) i`. -/
lemma cfDigit_add (x : ℝ) (n i : ℕ) :
    cfDigit x (n + i) = cfDigit (gaussMap^[n] x) i := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + i = (m + i) + 1 by ring, cfDigit_succ,
        ih (gaussMap x), Function.iterate_succ_apply]

/-- Splitting the last digit: on irrationals of `(0,1)`,
`x ∈ I_{w++[b]} ∩ T^{-(n+1)}A ↔ x ∈ I_w ∧ Tⁿx ∈ I_{[b]} ∩ T⁻¹A`. -/
lemma concat_inter_ae (w : List ℕ) (b : ℕ) (A : Set ℝ) :
    (cfCylinder (w ++ [b]) ∩ (gaussMap^[w.length + 1]) ⁻¹' A : Set ℝ) =ᵐ[volume]
      ((cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹'
        (cfCylinder [b] ∩ gaussMap ⁻¹' A) : Set ℝ)) := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨hcyl, hTA⟩
    have hx : x ∈ Set.Ioo (0 : ℝ) 1 := hcyl.1
    have horb := irrational_orbit x hirr hx w.length
    refine ⟨cfCylinder_append_subset w [b] hcyl, ?_⟩
    rw [Set.mem_preimage]
    constructor
    · rw [mem_cfCylinder_singleton]
      refine ⟨horb.2, ?_⟩
      have hd := hcyl.2 w.length (by simp)
      rw [← cfDigit_add x w.length 0, Nat.add_zero]
      rw [hd, List.getD_append_right _ _ _ _ (le_refl w.length)]
      simp
    · rw [Set.mem_preimage]
      rw [← Function.iterate_succ_apply' gaussMap w.length x]
      exact hTA
  · rintro ⟨hcylw, horbmem⟩
    have hx : x ∈ Set.Ioo (0 : ℝ) 1 := hcylw.1
    rw [Set.mem_preimage] at horbmem
    obtain ⟨hb_cyl, hb_T⟩ := horbmem
    obtain ⟨horb_io, hdig⟩ := mem_cfCylinder_singleton.mp hb_cyl
    constructor
    · refine ⟨hx, fun i hi => ?_⟩
      have hi' : i < w.length + 1 := by simpa using hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | heq
      · rw [List.getD_append _ _ _ _ hlt]
        exact hcylw.2 i hlt
      · rw [heq, List.getD_append_right _ _ _ _ (le_refl w.length)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [show w.length = w.length + 0 from rfl, cfDigit_add x w.length 0]
        exact hdig
    · rw [Set.mem_preimage, Function.iterate_succ_apply' gaussMap w.length x]
      exact hb_T

/-- Volume ratio of a one-digit extension, in tail-parameter form:
`|I_{w++[b]}| = (1+t)/((b+t)(b+1+t)) · |I_w|` with `t = tParam w`. -/
lemma volume_cfCylinder_concat (w : List ℕ) (b : ℕ) (hb : 1 ≤ b)
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder (w ++ [b])) =
      ENNReal.ofReal ((1 + tParam w) /
        (((b : ℝ) + tParam w) * ((b : ℝ) + 1 + tParam w))) *
        volume (cfCylinder w) := by
  sorry

/-- **The conditional density identity, all words** (`[]` included): the
distribution of `T^{|w|}x` conditioned on `I_w` has density
`tailDensity (tParam w)`. -/
theorem volume_inter_preimage_aux (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a)
    (A : Set ℝ) (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    volume (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' A) =
      ENNReal.ofReal (∫ y in A, tailDensity (tParam w) y) *
        volume (cfCylinder w) := by
  sorry

end NormalNumbers
