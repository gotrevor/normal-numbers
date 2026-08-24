/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFCylinder

/-!
# W2 — digit laws + the Markov length substitute (scaffold)

Work package W2 of expedition B5′ (`KHINCHIN.md`): the single-digit law, the
relative-order-`n` partition calculus, the Gauss/Lebesgue two-sided
comparison, and the elementary substitute for B–Y Lemma 5 (Morita/Vallée
CLT) — `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md`,
"Efficiency-free substitute".  Stated here and left `sorry` for the campaign.

Statement plan (provenance in each docstring):
* `volume_digit_cylinder` — `|I_{[k]}| = 1/(k(k+1))` (Lebesgue digit law).
* `cfCylinder_disjoint` — same-length distinct words have disjoint cylinders.
* `volume_eq_tsum_extensions` — genuine `n`-digit extensions partition a
  genuine cylinder up to a null set; measures add exactly.
* `gaussMeasure_le_volume`, `volume_le_gaussMeasure` — the density window
  `1/(2 log 2) ≤ 1/((1+x) log 2) ≤ 1/log 2` as a two-sided measure
  comparison.
* `gaussMeasure_univ` — `γ` is a probability measure.
* `cfK_le_prod` — `K(a₁…aₙ) ≤ ∏(aᵢ+1)`, so `log qₙ ≤ Σ log(aᵢ+1)`.
* `tsum_mul_log_cfK_le` — conditional expected log-continuant grows at most
  linearly: `Σ_u |I_{wu}|·log K(u) ≤ C·n·|I_w|`.
* `half_mass_long_extensions` — **the Lemma-5 substitute** (Markov): at
  least half the mass of a genuine cylinder lies in extensions with
  `K(u) ≤ e^{Cn}`, i.e. relative length `≥ e^{-2Cn}/2`.
* `volume_append_mul_fib_le` — the free deterministic upper bound: every
  relative-order-`n` extension shrinks length by `≥ fib(n+1)²/2`.

Hand-checked anchors (frozen with the statements, per the planted-scaffold
doctrine): `K(3)·(K(3)+K()) = 12` matches `|I_{[3]}| = |(1/4, 1/3]| = 1/12`;
`K(1,2,3) = 10 ≤ 24 = 2·3·4`; `[1,2] ∈ genWords 2` while `[1,0] ∉`
(digit `0` is the junk marker, `CFDefs.lean` conventions).
-/

namespace NormalNumbers

open MeasureTheory

/-- The genuine digit words of length `n`: every digit `≥ 1` (digit `0` is
the junk marker for rationals/out-of-range, see `CFDefs.lean`).  The
cylinders `cfCylinder (w ++ u)`, `u ∈ genWords n`, partition `cfCylinder w`
up to a null set. -/
def genWords (n : ℕ) : Set (List ℕ) := {u | u.length = n ∧ ∀ a ∈ u, 1 ≤ a}

/-! ## Anchors (kernel-checked) -/

example : cfK [3] * (cfK [3] + cfK ([3].dropLast)) = 12 := by decide
example : cfK [1, 2, 3] ≤ (([1, 2, 3] : List ℕ).map (· + 1)).prod := by decide
example : ([1, 2] : List ℕ) ∈ genWords 2 := ⟨rfl, by decide⟩
example : ([1, 0] : List ℕ) ∉ genWords 2 := by
  intro h
  exact absurd (h.2 0 (by simp)) (by decide)

/-! ## Digit law and partition calculus -/

/-- **Single-digit cylinder length** (the Lebesgue precursor of Gauss–Kuzmin):
`|I_{[k]}| = 1/(k(k+1))`, i.e. `P(a₁ = k) = 1/(k(k+1))` under Lebesgue.
Specializes `volume_cfCylinder` (`cfK [k] = k`, `cfK [] = 1`).
Anchor: `k = 3` gives `1/12 = |(1/4, 1/3]|`. -/
theorem volume_digit_cylinder (k : ℕ) (hk : 1 ≤ k) :
    volume (cfCylinder [k]) =
      ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  rw [volume_cfCylinder [k] (by simp) (by simpa using hk)]
  norm_num [cfK]

/-- Distinct words of the same length read incompatible digits, so their
cylinders are disjoint.  No digit-positivity needed. -/
theorem cfCylinder_disjoint {w w' : List ℕ} (hlen : w.length = w'.length)
    (hne : w ≠ w') : Disjoint (cfCylinder w) (cfCylinder w') := by
  rw [Set.disjoint_left]
  rintro x ⟨hx1, hd1⟩ ⟨hx2, hd2⟩
  apply hne
  apply List.ext_getElem hlen
  intro i h1 h2
  have e1 := hd1 i h1
  have e2 := hd2 i (hlen ▸ h1)
  rw [List.getD_eq_getElem w 0 h1] at e1
  rw [List.getD_eq_getElem w' 0 h2] at e2
  rw [← e1, ← e2]

/-- **Relative-order-`n` partition**: the genuine `n`-digit extensions of a
genuine cylinder exhaust it up to a null set (irrationals have genuine
digits; the rational junk is countable), and they are pairwise disjoint, so
the measures add exactly.  This identity turns the distortion pair (B–Y
Lemma 3.2, W1) into a conditional-probability calculus. -/
lemma measurable_gaussMap : Measurable gaussMap := by
  unfold gaussMap
  exact Measurable.ite (MeasurableSet.singleton 0) measurable_const
    (measurable_fract.comp measurable_inv)

lemma measurable_cfDigit (n : ℕ) : Measurable (cfDigit · n) := by
  unfold cfDigit
  exact Nat.measurable_floor.comp
    (measurable_inv.comp (measurable_gaussMap.iterate n))

lemma measurableSet_cfCylinder (w : List ℕ) :
    MeasurableSet (cfCylinder w) := by
  have heq : cfCylinder w = Set.Ioo (0 : ℝ) 1 ∩
      ⋂ i, ⋂ _ : i < w.length, (cfDigit · i) ⁻¹' {w.getD i 0} := by
    ext x
    simp only [cfCylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [heq]
  exact measurableSet_Ioo.inter (MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun _ =>
      (measurable_cfDigit i) (measurableSet_singleton _))

/-- Prefix property: extending the word shrinks the cylinder. -/
lemma cfCylinder_append_subset (w u : List ℕ) :
    cfCylinder (w ++ u) ⊆ cfCylinder w := by
  rintro x ⟨hx, hd⟩
  refine ⟨hx, fun i hi => ?_⟩
  have h := hd i (by simp only [List.length_append]; omega)
  rwa [List.getD_append _ _ _ _ hi] at h

/-- Irrationals in `(0,1)` keep irrational, in-range Gauss orbits. -/
lemma irrational_orbit (x : ℝ) (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    Irrational (gaussMap^[k] x) ∧ gaussMap^[k] x ∈ Set.Ioo (0 : ℝ) 1 := by
  induction k with
  | zero => exact ⟨hirr, hx⟩
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact irrational_gaussMap ih.1 ih.2

/-- Every digit of an irrational in `(0,1)` is genuine (`≥ 1`). -/
lemma one_le_cfDigit (x : ℝ) (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) : 1 ≤ cfDigit x k := by
  obtain ⟨hkirr, hk0, hk1⟩ := irrational_orbit x hirr hx k
  rw [cfDigit]
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_inv_comm₀ one_pos hk0]
  simpa using hk1.le

theorem volume_eq_tsum_extensions (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (n : ℕ) :
    volume (cfCylinder w) =
      ∑' u : genWords n, volume (cfCylinder (w ++ (u : List ℕ))) := by
  have hcount : (genWords n).Countable :=
    Set.Countable.mono (Set.subset_univ _) (Set.countable_univ)
  -- pairwise disjoint
  have hdisj : (genWords n).PairwiseDisjoint
      fun u : List ℕ => cfCylinder (w ++ u) := by
    intro u hu u' hu' hne
    exact cfCylinder_disjoint
      (by simp [hu.1, hu'.1]) (fun h => hne (List.append_cancel_left h))
  -- the biUnion computes the tsum
  have hbiu : volume (⋃ u ∈ genWords n, cfCylinder (w ++ u)) =
      ∑' u : genWords n, volume (cfCylinder (w ++ (u : List ℕ))) :=
    measure_biUnion hcount hdisj fun u _ => measurableSet_cfCylinder _
  rw [← hbiu]
  -- squeeze: the union is inside the cylinder and covers its irrationals
  apply le_antisymm
  · -- cover up to the countable rationals
    have hcover : cfCylinder w ⊆
        (⋃ u ∈ genWords n, cfCylinder (w ++ u)) ∪ Set.range ((↑) : ℚ → ℝ) := by
      intro x hx
      by_cases hirr : Irrational x
      · left
        obtain ⟨hx01, hd⟩ := hx
        set u : List ℕ := (List.range n).map fun i => cfDigit x (w.length + i)
          with hu_def
        have hulen : u.length = n := by simp [hu_def]
        have hugen : u ∈ genWords n := by
          refine ⟨hulen, fun a ha => ?_⟩
          simp only [hu_def, List.mem_map, List.mem_range] at ha
          obtain ⟨i, _, rfl⟩ := ha
          exact one_le_cfDigit x hirr hx01 _
        refine Set.mem_biUnion hugen ⟨hx01, fun i hi => ?_⟩
        rcases lt_or_ge i w.length with h | h
        · rw [List.getD_append _ _ _ _ h]
          exact hd i h
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
          have hj : j < n := by
            simp only [List.length_append, hulen] at hi
            omega
          rw [List.getD_append_right _ _ _ _ h]
          simp [hu_def, hj, List.getD_eq_getElem?_getD]
      · right
        rw [Irrational] at hirr
        push_neg at hirr
        exact hirr
    calc volume (cfCylinder w)
        ≤ volume ((⋃ u ∈ genWords n, cfCylinder (w ++ u)) ∪
            Set.range ((↑) : ℚ → ℝ)) := measure_mono hcover
      _ ≤ volume (⋃ u ∈ genWords n, cfCylinder (w ++ u)) +
            volume (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
      _ = volume (⋃ u ∈ genWords n, cfCylinder (w ++ u)) := by
          rw [(Set.countable_range _).measure_zero, add_zero]
  · exact measure_mono (Set.iUnion₂_subset fun u _ =>
      cfCylinder_append_subset w u)

/-! ## Gauss measure vs Lebesgue -/

/-- Upper comparison: the Gauss density is at most `1/log 2`, so
`γ(s) ≤ (1/log 2)·|s|`. -/
theorem gaussMeasure_le_volume (s : Set ℝ) (hs : MeasurableSet s) :
    gaussMeasure s ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume s := by
  rw [gaussMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]
  calc ∫⁻ x in s ∩ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹) ∂volume
      ≤ ∫⁻ _ in s ∩ Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (Real.log 2)⁻¹ ∂volume := by
        apply setLIntegral_mono measurable_const
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hx0 : (0 : ℝ) < x := hx.2.1
        exact inv_anti₀ hlog (by nlinarith)
    _ = ENNReal.ofReal (Real.log 2)⁻¹ * volume (s ∩ Set.Ioo (0 : ℝ) 1) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume s := by
        gcongr
        exact Set.inter_subset_left

/-- Lower comparison on `(0,1)`: the Gauss density is at least
`1/(2 log 2)` there, so `(1/(2 log 2))·|s| ≤ γ(s)`. -/
theorem volume_le_gaussMeasure (s : Set ℝ) (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (2 * Real.log 2)⁻¹ * volume s ≤ gaussMeasure s := by
  rw [gaussMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs,
    Set.inter_eq_self_of_subset_left hsub]
  calc ENNReal.ofReal (2 * Real.log 2)⁻¹ * volume s
      = ∫⁻ _ in s, ENNReal.ofReal (2 * Real.log 2)⁻¹ ∂volume :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹) ∂volume := by
        apply setLIntegral_mono
          (by fun_prop)
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hx1 : x < 1 := (hsub hx).2
        have hx0 : (0 : ℝ) < x := (hsub hx).1
        exact inv_anti₀ (by nlinarith) (by nlinarith)

/-- `γ` is a probability measure:
`γ(0,1) = (1/log 2)·∫₀¹ dx/(1+x) = log 2/log 2 = 1`. -/
theorem gaussMeasure_univ : gaussMeasure Set.univ = 1 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < (1 + x) * Real.log 2 := by
    intro x hx
    nlinarith [hx.1]
  set g : ℝ → ℝ := fun x => ((1 + x) * Real.log 2)⁻¹ with hg
  have hc : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact (hpos x hx).ne'
  have hInt : MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) 1) volume :=
    (hc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have := hpos x (Set.Ioo_subset_Icc_self hx)
    positivity
  have hval : ∫ x in Set.Ioo (0 : ℝ) 1, g x ∂volume = 1 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hsplit : ∀ x : ℝ, g x = (Real.log 2)⁻¹ * (1 + x)⁻¹ := by
      intro x
      simp only [hg]
      rw [mul_inv, mul_comm]
    simp only [hsplit]
    have hint : ∫ x in (0 : ℝ)..1, (1 + x)⁻¹ = Real.log 2 := by
      rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y⁻¹) 1,
        show (1 : ℝ) + 0 = 1 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num,
        integral_inv_of_pos one_pos two_pos]
      norm_num
    rw [intervalIntegral.integral_const_mul, hint]
    exact inv_mul_cancel₀ hlog.ne'
  rw [gaussMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, hval,
    ENNReal.ofReal_one]

/-- **Gauss measure of a subinterval**: `γ(u,v) = (log(1+v) - log(1+u))/log 2`
for `0 ≤ u ≤ v ≤ 1` — the closed form behind the Gauss–Kuzmin single-digit
law.  Same route as `gaussMeasure_univ`, generalized from `(0,1)` to `(u,v)`. -/
theorem gaussMeasure_Ioo {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    gaussMeasure (Set.Ioo u v) =
      ENNReal.ofReal ((Real.log (1 + v) - Real.log (1 + u)) / Real.log 2) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ x ∈ Set.Icc u v, (0 : ℝ) < (1 + x) * Real.log 2 := by
    intro x hx
    nlinarith [hx.1, hu]
  set g : ℝ → ℝ := fun x => ((1 + x) * Real.log 2)⁻¹ with hg
  have hc : ContinuousOn g (Set.Icc u v) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact (hpos x hx).ne'
  have hIooss : Set.Ioo u v ⊆ Set.Icc u v := Set.Ioo_subset_Icc_self
  have hInt : MeasureTheory.IntegrableOn g (Set.Ioo u v) volume :=
    (hc.integrableOn_Icc).mono_set hIooss
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo u v)] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have := hpos x (hIooss hx)
    positivity
  have hval : ∫ x in Set.Ioo u v, g x ∂volume
      = (Real.log (1 + v) - Real.log (1 + u)) / Real.log 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le huv]
    have hsplit : ∀ x : ℝ, g x = (Real.log 2)⁻¹ * (1 + x)⁻¹ := by
      intro x
      simp only [hg]
      rw [mul_inv, mul_comm]
    simp only [hsplit]
    have hint : ∫ x in u..v, (1 + x)⁻¹ = Real.log (1 + v) - Real.log (1 + u) := by
      rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y⁻¹) 1,
        integral_inv_of_pos (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)]
    rw [intervalIntegral.integral_const_mul, hint, div_eq_inv_mul]
  have hsubset : Set.Ioo u v ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt hu hx.1, lt_of_lt_of_le hx.2 hv⟩
  rw [gaussMeasure, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left hsubset,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, hval]

/-! ## The Markov substitute for B–Y Lemma 5 -/

/-- The continuant is at most the product of (digit + 1):
`K(a₁…aₙ) ≤ ∏(aᵢ+1)`, hence `log qₙ ≤ Σ log(aᵢ+1)` — the elementary
observable replacing B–Y Lemma 4's CLT.  No positivity hypothesis needed. -/
theorem cfK_le_prod (w : List ℕ) : cfK w ≤ (w.map (· + 1)).prod := by
  induction w using cfK.induct with
  | case1 => simp [cfK]
  | case2 a => simp [cfK]
  | case3 a b l ih1 ih2 =>
      simp only [List.map_cons, List.prod_cons] at *
      have hP : (List.map (· + 1) l).prod ≤ (b + 1) * (List.map (· + 1) l).prod :=
        Nat.le_mul_of_pos_left _ (by omega)
      calc cfK (a :: b :: l) = a * cfK (b :: l) + cfK l := rfl
        _ ≤ a * ((b + 1) * (List.map (· + 1) l).prod) +
              (b + 1) * (List.map (· + 1) l).prod :=
            Nat.add_le_add (Nat.mul_le_mul_left a ih1) (le_trans ih2 hP)
        _ = (a + 1) * ((b + 1) * (List.map (· + 1) l).prod) := by ring

/-- **Lower bound: the continuant dominates the digit product**
`∏ aᵢ ≤ K(a₁…aₙ)`.  Feeds the Khinchin-typicality uniform-integrability
bound: combined with the schedule's `cfK u ≤ exp(goodC·n)` payload, this
bounds each stage's average `log`-digit by `goodC`. -/
theorem prod_le_cfK (w : List ℕ) : w.prod ≤ cfK w := by
  induction w using cfK.induct with
  | case1 => simp [cfK]
  | case2 a => simp [cfK]
  | case3 a b l ih1 ih2 =>
      simp only [List.prod_cons] at *
      calc a * (b * l.prod) ≤ a * cfK (b :: l) := by
            exact Nat.mul_le_mul_left a (by simpa [List.prod_cons] using ih1)
        _ ≤ a * cfK (b :: l) + cfK l := Nat.le_add_right _ _
        _ = cfK (a :: b :: l) := rfl

/-! ### Scaffolding for the conditional log-continuant bound -/

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h0 : (0 : ℝ) < x := by linarith
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 h0
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt h0.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  nlinarith

private lemma digitLog_nonneg (j : ℕ) :
    0 ≤ Real.log ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)

/-- The summable majorant series `Σⱼ log(j+2)/((j+1)(j+2))` (digit `k = j+1`). -/
private noncomputable def digitLogSum : ℝ :=
  ∑' j : ℕ, Real.log ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 2))

private lemma summable_digitLog :
    Summable (fun j : ℕ =>
      Real.log ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  have hp : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
    have h := (Real.summable_one_div_nat_rpow (p := (3 : ℝ) / 2)).2 (by norm_num)
    have h1 := (summable_nat_add_iff 1).2 h
    apply h1.congr
    intro j
    push_cast
    ring
  apply Summable.of_nonneg_of_le digitLog_nonneg (fun j => ?_)
    (hp.mul_left (2 * Real.sqrt 2))
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hx0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hsx : (0 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_nonneg _
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hlog : Real.log ((j : ℝ) + 2) ≤
      2 * (Real.sqrt 2 * Real.sqrt ((j : ℝ) + 1)) := by
    calc Real.log ((j : ℝ) + 2) ≤ 2 * Real.sqrt ((j : ℝ) + 2) :=
          log_le_two_sqrt (by linarith)
      _ ≤ 2 * (Real.sqrt 2 * Real.sqrt ((j : ℝ) + 1)) := by
          have := Real.sqrt_le_sqrt
            (show (j : ℝ) + 2 ≤ 2 * ((j : ℝ) + 1) by linarith)
          rw [Real.sqrt_mul (by norm_num)] at this
          linarith
  have hkey : Real.sqrt ((j : ℝ) + 1) * ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) =
      ((j : ℝ) + 1) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0,
      show (1 : ℝ) / 2 + 3 / 2 = 2 by norm_num, Real.rpow_two]
  have hr0 : (0 : ℝ) < ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hx0 _
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hr0]
  have hmul : Real.log ((j : ℝ) + 2) * ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤
      (2 * (Real.sqrt 2 * Real.sqrt ((j : ℝ) + 1))) *
        ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
    apply mul_le_mul_of_nonneg_right hlog hr0.le
  calc Real.log ((j : ℝ) + 2) * ((j : ℝ) + 1) ^ ((3 : ℝ) / 2)
      ≤ (2 * (Real.sqrt 2 * Real.sqrt ((j : ℝ) + 1))) *
          ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) := hmul
    _ = 2 * Real.sqrt 2 *
          (Real.sqrt ((j : ℝ) + 1) * ((j : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by ring
    _ = 2 * Real.sqrt 2 * ((j : ℝ) + 1) ^ 2 := by rw [hkey]
    _ ≤ 2 * Real.sqrt 2 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by nlinarith

private lemma digitLogSum_nonneg : 0 ≤ digitLogSum :=
  tsum_nonneg digitLog_nonneg

/-- Reindex `ℕ` onto the genuine digits `{k // 1 ≤ k}`. -/
private def succEquiv : ℕ ≃ {k : ℕ // 1 ≤ k} where
  toFun j := ⟨j + 1, Nat.succ_le_succ (Nat.zero_le _)⟩
  invFun k := (k : ℕ) - 1
  left_inv j := by simp
  right_inv k := by
    obtain ⟨v, hv⟩ := k
    simp only [Subtype.mk.injEq]
    omega

/-- Peel the first digit: `{k // 1 ≤ k} × genWords n ≃ genWords (n+1)`. -/
private noncomputable def genConsEquiv (n : ℕ) :
    {k : ℕ // 1 ≤ k} × ↥(genWords n) ≃ ↥(genWords (n + 1)) :=
  Equiv.ofBijective
    (fun p => ⟨(p.1 : ℕ) :: (p.2 : List ℕ), by
      obtain ⟨hlen, hp⟩ := p.2.2
      refine ⟨by simp [hlen], fun a ha => ?_⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact p.1.2
      · exact hp a ha⟩)
    (by
      constructor
      · rintro ⟨⟨k, hk⟩, ⟨s, hs⟩⟩ ⟨⟨k', hk'⟩, ⟨s', hs'⟩⟩ h
        simp only [Subtype.mk.injEq, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · rintro ⟨v, hv⟩
        obtain ⟨hlen, hp⟩ := hv
        cases v with
        | nil => simp at hlen
        | cons a s =>
            exact ⟨⟨⟨a, hp a (by simp)⟩,
              ⟨s, ⟨by simpa using hlen,
                fun x hx => hp x (List.mem_cons_of_mem _ hx)⟩⟩⟩, rfl⟩)

/-- Genuine one-digit words are exactly the genuine digits. -/
private noncomputable def digitEquiv : {k : ℕ // 1 ≤ k} ≃ ↥(genWords 1) :=
  Equiv.ofBijective
    (fun k => ⟨[(k : ℕ)], by
      refine ⟨rfl, fun a ha => ?_⟩
      rw [List.mem_singleton.1 ha]
      exact k.2⟩)
    (by
      constructor
      · intro k k' h
        have h2 : ([(k : ℕ)] : List ℕ) = [(k' : ℕ)] := congrArg Subtype.val h
        exact Subtype.ext (by simpa using h2)
      · rintro ⟨v, hv⟩
        obtain ⟨hlen, hp⟩ := hv
        cases v with
        | nil => simp at hlen
        | cons a s =>
            cases s with
            | nil => exact ⟨⟨a, hp a (by simp)⟩, rfl⟩
            | cons b l => simp at hlen)

/-- `K(k::s) ≤ (k+1)·K(s)` for genuine `s` — the one-step log recursion. -/
private lemma cfK_cons_le (k : ℕ) (s : List ℕ) (hs : ∀ a ∈ s, 1 ≤ a) :
    cfK (k :: s) ≤ (k + 1) * cfK s := by
  cases s with
  | nil => simp [cfK]
  | cons b l =>
      show k * cfK (b :: l) + cfK l ≤ (k + 1) * cfK (b :: l)
      have h := cfK_drop_one_le (b :: l) hs
      simp only [List.drop_one, List.tail_cons] at h
      calc k * cfK (b :: l) + cfK l ≤ k * cfK (b :: l) + cfK (b :: l) :=
            Nat.add_le_add_left h _
        _ = (k + 1) * cfK (b :: l) := (Nat.succ_mul k _).symm

private lemma ofReal_log_cfK_cons_le (k : ℕ) (hk : 1 ≤ k) (s : List ℕ)
    (hs : ∀ a ∈ s, 1 ≤ a) :
    ENNReal.ofReal (Real.log (cfK (k :: s))) ≤
      ENNReal.ofReal (Real.log ((k : ℝ) + 1)) +
        ENNReal.ofReal (Real.log (cfK s)) := by
  have hKs : 1 ≤ cfK s := one_le_cfK s hs
  have hKsR : (1 : ℝ) ≤ (cfK s : ℝ) := by exact_mod_cast hKs
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hposN : 1 ≤ cfK (k :: s) := one_le_cfK (k :: s) (fun a ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hk
    · exact hs a ha)
  have hpos : (0 : ℝ) < (cfK (k :: s) : ℝ) := by
    have : (1 : ℝ) ≤ (cfK (k :: s) : ℝ) := by exact_mod_cast hposN
    linarith
  have h1 : (cfK (k :: s) : ℝ) ≤ ((k : ℝ) + 1) * (cfK s : ℝ) := by
    exact_mod_cast cfK_cons_le k s hs
  rw [← ENNReal.ofReal_add (Real.log_nonneg (by linarith))
    (Real.log_nonneg hKsR)]
  apply ENNReal.ofReal_le_ofReal
  calc Real.log (cfK (k :: s))
      ≤ Real.log (((k : ℝ) + 1) * (cfK s : ℝ)) := Real.log_le_log hpos h1
    _ = Real.log ((k : ℝ) + 1) + Real.log (cfK s : ℝ) :=
        Real.log_mul (by linarith) (by linarith)

/-- Order-1 partition, digit-indexed: `Σₖ |I_{w·k}| = |I_w|`. -/
private lemma tsum_digit_extension (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∑' k : {k : ℕ // 1 ≤ k}, volume (cfCylinder (w ++ [(k : ℕ)])) =
      volume (cfCylinder w) := by
  rw [volume_eq_tsum_extensions w hw hpos 1]
  exact digitEquiv.tsum_eq
    (fun u : genWords 1 => volume (cfCylinder (w ++ (u : List ℕ))))

/-- The digit-law series bound: `Σₖ |I_{[k]}|·log(k+1) ≤ digitLogSum`. -/
private lemma tsum_digit_mul_log_le :
    ∑' k : {k : ℕ // 1 ≤ k},
        volume (cfCylinder [(k : ℕ)]) *
          ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1)) ≤
      ENNReal.ofReal digitLogSum := by
  rw [← succEquiv.tsum_eq (fun k : {k : ℕ // 1 ≤ k} =>
    volume (cfCylinder [(k : ℕ)]) *
      ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1)))]
  have hterm : ∀ j : ℕ,
      volume (cfCylinder [((succEquiv j : {k : ℕ // 1 ≤ k}) : ℕ)]) *
        ENNReal.ofReal
          (Real.log ((((succEquiv j : {k : ℕ // 1 ≤ k}) : ℕ) : ℝ) + 1)) =
      ENNReal.ofReal
        (Real.log ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    intro j
    have hc : (((succEquiv j : {k : ℕ // 1 ≤ k}) : ℕ)) = j + 1 := rfl
    rw [hc, volume_digit_cylinder (j + 1) (Nat.succ_le_succ (Nat.zero_le _)),
      ← ENNReal.ofReal_mul (by positivity)]
    have harg : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    rw [harg]
    congr 1
    have h2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [h2]
    ring
  calc ∑' j : ℕ,
        volume (cfCylinder [((succEquiv j : {k : ℕ // 1 ≤ k}) : ℕ)]) *
          ENNReal.ofReal
            (Real.log ((((succEquiv j : {k : ℕ // 1 ≤ k}) : ℕ) : ℝ) + 1))
      = ∑' j : ℕ, ENNReal.ofReal
          (Real.log ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
        exact tsum_congr hterm
    _ = ENNReal.ofReal digitLogSum :=
        (ENNReal.ofReal_tsum_of_nonneg digitLog_nonneg summable_digitLog).symm
    _ ≤ ENNReal.ofReal digitLogSum := le_rfl

/-- **Conditional expected log-continuant is linear in `n`**: for some
constant `C` and every genuine base cylinder,
`Σ_u |I_{wu}|·log K(u) ≤ C·n·|I_w|` over genuine words `u` of length `n`.
Route: `cfK_le_prod` + per-digit marginals via `volume_eq_tsum_extensions`,
`volume_cylinder_append_le`, `volume_digit_cylinder`, and summability of
`Σₖ log(k+1)/(k(k+1))`. -/
theorem tsum_mul_log_cfK_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      ∑' u : genWords n,
          volume (cfCylinder (w ++ (u : List ℕ))) *
            ENNReal.ofReal (Real.log (cfK (u : List ℕ))) ≤
        ENNReal.ofReal (C * n) * volume (cfCylinder w) := by
  refine ⟨2 * digitLogSum + 1, by nlinarith [digitLogSum_nonneg], ?_⟩
  set C : ℝ := 2 * digitLogSum + 1 with hC
  have hC0 : (0 : ℝ) ≤ C := by nlinarith [digitLogSum_nonneg]
  suffices key : ∀ n : ℕ, ∀ w : List ℕ, w ≠ [] → (∀ a ∈ w, 1 ≤ a) →
      ∑' u : genWords n,
          volume (cfCylinder (w ++ (u : List ℕ))) *
            ENNReal.ofReal (Real.log (cfK (u : List ℕ))) ≤
        ENNReal.ofReal (C * n) * volume (cfCylinder w) by
    intro w hw hpos n
    exact key n w hw hpos
  intro n
  induction n with
  | zero =>
      intro w hw hpos
      have hzero : ∀ u : genWords 0,
          volume (cfCylinder (w ++ (u : List ℕ))) *
            ENNReal.ofReal (Real.log (cfK (u : List ℕ))) = 0 := by
        intro u
        have hnil : (u : List ℕ) = [] := List.length_eq_zero_iff.1 u.2.1
        rw [hnil]
        simp [cfK]
      rw [tsum_congr hzero]
      simp
  | succ n ih =>
      intro w hw hpos
      have hwk : ∀ k : {k : ℕ // 1 ≤ k}, (w ++ [(k : ℕ)]) ≠ [] := by
        intro k; simp
      have hwkpos : ∀ k : {k : ℕ // 1 ≤ k}, ∀ a ∈ w ++ [(k : ℕ)], 1 ≤ a := by
        intro k a ha
        rcases List.mem_append.1 ha with h | h
        · exact hpos a h
        · rw [List.mem_singleton.1 h]; exact k.2
      -- reindex by peeling the first digit
      rw [← (genConsEquiv n).tsum_eq (fun u : genWords (n + 1) =>
        volume (cfCylinder (w ++ (u : List ℕ))) *
          ENNReal.ofReal (Real.log (cfK (u : List ℕ))))]
      -- the reindexed term, in appended-base form
      have hassoc : ∀ (k : {k : ℕ // 1 ≤ k}) (s : genWords n),
          w ++ ((k : ℕ) :: (s : List ℕ)) = (w ++ [(k : ℕ)]) ++ (s : List ℕ) := by
        intro k s; simp
      -- pointwise: log K(k::s) ≤ log(k+1) + log K(s)
      have hsplit : ∀ (k : {k : ℕ // 1 ≤ k}) (s : genWords n),
          volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
              ENNReal.ofReal (Real.log (cfK ((k : ℕ) :: (s : List ℕ)))) ≤
            volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1)) +
              volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                ENNReal.ofReal (Real.log (cfK (s : List ℕ))) := by
        intro k s
        rw [← mul_add]
        gcongr
        exact ofReal_log_cfK_cons_le (k : ℕ) k.2 (s : List ℕ) s.2.2
      calc ∑' (c : {k : ℕ // 1 ≤ k} × ↥(genWords n)),
            volume (cfCylinder (w ++ (((genConsEquiv n) c : ↥(genWords (n+1))) : List ℕ))) *
              ENNReal.ofReal
                (Real.log (cfK (((genConsEquiv n) c : ↥(genWords (n+1))) : List ℕ)))
          = ∑' (c : {k : ℕ // 1 ≤ k} × ↥(genWords n)),
              volume (cfCylinder ((w ++ [(c.1 : ℕ)]) ++ (c.2 : List ℕ))) *
                ENNReal.ofReal (Real.log (cfK ((c.1 : ℕ) :: (c.2 : List ℕ)))) := by
            apply tsum_congr; rintro ⟨k, s⟩
            rw [show (((genConsEquiv n) (k, s) : ↥(genWords (n+1))) : List ℕ) =
              (k : ℕ) :: (s : List ℕ) from rfl, hassoc k s]
        _ = ∑' (k : {k : ℕ // 1 ≤ k}) (s : genWords n),
              volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                ENNReal.ofReal (Real.log (cfK ((k : ℕ) :: (s : List ℕ)))) := by
            exact ENNReal.tsum_prod
              (f := fun (k : {k : ℕ // 1 ≤ k}) (s : ↥(genWords n)) =>
                volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                  ENNReal.ofReal (Real.log (cfK ((k : ℕ) :: (s : List ℕ)))))
        _ ≤ ∑' (k : {k : ℕ // 1 ≤ k}) (s : genWords n),
              (volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                  ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1)) +
                volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                  ENNReal.ofReal (Real.log (cfK (s : List ℕ)))) := by
            apply ENNReal.tsum_le_tsum; intro k
            apply ENNReal.tsum_le_tsum; intro s
            exact hsplit k s
        _ = ∑' k : {k : ℕ // 1 ≤ k},
              (volume (cfCylinder (w ++ [(k : ℕ)])) *
                  ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1)) +
                ∑' s : genWords n,
                  volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                    ENNReal.ofReal (Real.log (cfK (s : List ℕ)))) := by
            apply tsum_congr; intro k
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
              ← volume_eq_tsum_extensions (w ++ [(k : ℕ)]) (hwk k) (hwkpos k) n]
        _ = (∑' k : {k : ℕ // 1 ≤ k},
              volume (cfCylinder (w ++ [(k : ℕ)])) *
                ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1))) +
            ∑' k : {k : ℕ // 1 ≤ k},
              ∑' s : genWords n,
                volume (cfCylinder ((w ++ [(k : ℕ)]) ++ (s : List ℕ))) *
                  ENNReal.ofReal (Real.log (cfK (s : List ℕ))) :=
            ENNReal.tsum_add
        _ ≤ (∑' k : {k : ℕ // 1 ≤ k},
              2 * (volume (cfCylinder w) * volume (cfCylinder [(k : ℕ)])) *
                ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1))) +
            ∑' k : {k : ℕ // 1 ≤ k},
              ENNReal.ofReal (C * n) * volume (cfCylinder (w ++ [(k : ℕ)])) := by
            gcongr with k k
            · exact volume_cylinder_append_le w [(k : ℕ)] hw (by simp) hpos
                (fun a ha => by rw [List.mem_singleton.1 ha]; exact k.2)
            · exact ih (w ++ [(k : ℕ)]) (hwk k) (hwkpos k)
        _ = 2 * volume (cfCylinder w) *
              (∑' k : {k : ℕ // 1 ≤ k},
                volume (cfCylinder [(k : ℕ)]) *
                  ENNReal.ofReal (Real.log (((k : ℕ) : ℝ) + 1))) +
            ENNReal.ofReal (C * n) * volume (cfCylinder w) := by
            rw [← ENNReal.tsum_mul_left, ENNReal.tsum_mul_left (a := ENNReal.ofReal (C * n)),
              tsum_digit_extension w hw hpos]
            congr 1
            apply tsum_congr; intro k
            ring
        _ ≤ 2 * volume (cfCylinder w) * ENNReal.ofReal digitLogSum +
            ENNReal.ofReal (C * n) * volume (cfCylinder w) := by
            gcongr
            exact tsum_digit_mul_log_le
        _ ≤ ENNReal.ofReal (C * (n + 1)) * volume (cfCylinder w) := by
            have h1 : 2 * volume (cfCylinder w) * ENNReal.ofReal digitLogSum =
                ENNReal.ofReal (2 * digitLogSum) * volume (cfCylinder w) := by
              rw [show (2 : ENNReal) = ENNReal.ofReal 2 from
                  (ENNReal.ofReal_ofNat 2).symm,
                ENNReal.ofReal_mul (by norm_num)]
              ring
            rw [h1, ← add_mul, ← ENNReal.ofReal_add (by nlinarith [digitLogSum_nonneg])
              (by positivity)]
            gcongr
            simp only [hC]
            push_cast
            nlinarith [digitLogSum_nonneg]
        _ = ENNReal.ofReal (C * ((n + 1 : ℕ) : ℝ)) * volume (cfCylinder w) := by
            norm_cast

/-- **The Lemma-5 substitute** (B–Y Lemma 5 without Morita/Vallée, worse
constants, no complexity claim): for some `C`, at least half the mass of any
genuine cylinder lies in genuine relative-order-`n` extensions with
`K(u) ≤ e^{Cn}` — whose relative length is therefore `≥ e^{-2Cn}/2` by the
volume formula and distortion.  Markov's inequality on
`tsum_mul_log_cfK_le` with threshold `e^{Cn}`. -/
theorem half_mass_long_extensions :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤
        2 * ∑' u : genWords n,
          (if (cfK (u : List ℕ) : ℝ) ≤ Real.exp (C * n)
            then volume (cfCylinder (w ++ (u : List ℕ))) else 0) := by
  obtain ⟨C₀, hC₀, hbound⟩ := tsum_mul_log_cfK_le
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro w hw hpos n
  have hfin : volume (cfCylinder w) ≠ ⊤ := by
    have h1 : volume (cfCylinder w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono fun x hx => hx.1
    rw [Real.volume_Ioo] at h1
    exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
  set T : ↥(genWords n) → ENNReal :=
    fun u => volume (cfCylinder (w ++ (u : List ℕ))) with hT
  set P : ↥(genWords n) → Prop :=
    fun u => (cfK (u : List ℕ) : ℝ) ≤ Real.exp (2 * C₀ * n) with hP
  have hsplitfun : ∀ u : genWords n,
      T u = (if P u then T u else 0) + (if P u then 0 else T u) := by
    intro u
    by_cases h : P u <;> simp [h]
  have hpart : volume (cfCylinder w) =
      (∑' u : genWords n, if P u then T u else 0) +
        ∑' u : genWords n, if P u then 0 else T u := by
    rw [volume_eq_tsum_extensions w hw hpos n]
    calc ∑' u : genWords n, T u
        = ∑' u : genWords n,
            ((if P u then T u else 0) + (if P u then 0 else T u)) :=
          tsum_congr hsplitfun
      _ = _ := ENNReal.tsum_add
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: everything is good (K([]) = 1 ≤ e⁰)
    have hall : ∀ u : genWords 0, (if P u then T u else 0) = T u := by
      intro u
      have hnil : (u : List ℕ) = [] := List.length_eq_zero_iff.1 u.2.1
      have : P u := by
        rw [hP]
        simp only [hnil]
        norm_num [cfK]
      rw [if_pos this]
    calc volume (cfCylinder w)
        = ∑' u : genWords 0, T u := volume_eq_tsum_extensions w hw hpos 0
      _ = 1 * ∑' u : genWords 0, (if P u then T u else 0) := by
          rw [one_mul, tsum_congr hall]
      _ ≤ 2 * ∑' u : genWords 0, (if P u then T u else 0) := by
          gcongr
          exact one_le_two
  · -- n ≥ 1: Markov on the log-continuant bound
    have hCn : (0 : ℝ) < 2 * C₀ * n := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    set d : ENNReal := ENNReal.ofReal (2 * C₀ * n) with hd
    have hd0 : d ≠ 0 := by
      rw [hd]
      simp [ENNReal.ofReal_eq_zero, not_le, hCn]
    have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
    -- bad mass · d ≤ C₀·n·|I_w|
    have hbadmul : (∑' u : genWords n, if P u then 0 else T u) * d ≤
        ENNReal.ofReal (C₀ * n) * volume (cfCylinder w) := by
      rw [← ENNReal.tsum_mul_right]
      refine le_trans (ENNReal.tsum_le_tsum fun u => ?_) (hbound w hw hpos n)
      by_cases h : P u
      · simp [h]
      · rw [if_neg h]
        have hKpos : 1 ≤ cfK (u : List ℕ) := one_le_cfK _ u.2.2
        have hKR : (0 : ℝ) < (cfK (u : List ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ (cfK (u : List ℕ) : ℝ) := by exact_mod_cast hKpos
          linarith
        have hlt : Real.exp (2 * C₀ * n) < (cfK (u : List ℕ) : ℝ) := by
          rw [hP] at h
          push_neg at h
          exact h
        have hlog : 2 * C₀ * n ≤ Real.log (cfK (u : List ℕ)) := by
          have h2 := Real.log_lt_log (Real.exp_pos _) hlt
          rw [Real.log_exp] at h2
          linarith
        show T u * d ≤ T u * ENNReal.ofReal (Real.log (cfK (u : List ℕ)))
        gcongr
        rw [hd]
        exact ENNReal.ofReal_le_ofReal hlog
    -- hence bad mass ≤ |I_w|/2
    have hbad : (∑' u : genWords n, if P u then 0 else T u) ≤
        ENNReal.ofReal (1 / 2) * volume (cfCylinder w) := by
      rw [← ENNReal.mul_le_mul_iff_left hd0 hdtop]
      calc (∑' u : genWords n, if P u then 0 else T u) * d
          ≤ ENNReal.ofReal (C₀ * n) * volume (cfCylinder w) := hbadmul
        _ = ENNReal.ofReal (1 / 2) * volume (cfCylinder w) * d := by
            rw [hd, mul_comm (ENNReal.ofReal (1 / 2) * volume (cfCylinder w)) _,
              ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring
    -- cancel: |I_w| + |I_w| ≤ 2·good + |I_w|
    have htwo : (2 : ENNReal) * ENNReal.ofReal (1 / 2) = 1 := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 from
        (ENNReal.ofReal_ofNat 2).symm, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [← ENNReal.add_le_add_iff_right hfin]
    calc volume (cfCylinder w) + volume (cfCylinder w)
        = 2 * volume (cfCylinder w) := (two_mul _).symm
      _ = 2 * ((∑' u : genWords n, if P u then T u else 0) +
            ∑' u : genWords n, if P u then 0 else T u) := by rw [← hpart]
      _ = 2 * (∑' u : genWords n, if P u then T u else 0) +
            2 * ∑' u : genWords n, if P u then 0 else T u := mul_add _ _ _
      _ ≤ 2 * (∑' u : genWords n, if P u then T u else 0) +
            2 * (ENNReal.ofReal (1 / 2) * volume (cfCylinder w)) := by
          gcongr
      _ = 2 * (∑' u : genWords n, if P u then T u else 0) +
            volume (cfCylinder w) := by
          rw [← mul_assoc, htwo, one_mul]

/-- **Deterministic relative-length upper bound** (the free half of Lemma 5):
every genuine relative-order-`n` extension shrinks a cylinder by at least
`fib(n+1)²/2` — from `volume_cylinder_append_le`, `volume_cfCylinder`, and
`fib_le_cfK` (W1).  Multiplicative form to stay division-free in `ℝ≥0∞`. -/
theorem volume_append_mul_fib_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder (w ++ u)) * (Nat.fib (u.length + 1) : ENNReal) ^ 2 ≤
      2 * volume (cfCylinder w) := by
  have hdist := volume_cylinder_append_le w u hw hu hwpos hupos
  have hKu : 1 ≤ cfK u := one_le_cfK u hupos
  have hfib : Nat.fib (u.length + 1) ≤ cfK u := fib_le_cfK u hupos
  have hkey : volume (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2 ≤ 1 := by
    rw [volume_cfCylinder u hu hupos,
      show ((Nat.fib (u.length + 1) : ENNReal)) ^ 2 =
        ENNReal.ofReal ((Nat.fib (u.length + 1) : ℝ) ^ 2) from by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    have hKuR : (1 : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast hKu
    have hfibR : (Nat.fib (u.length + 1) : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast hfib
    have hfib0 : (0 : ℝ) ≤ (Nat.fib (u.length + 1) : ℝ) := by positivity
    have hK' : (0 : ℝ) ≤ (cfK u.dropLast : ℝ) := by positivity
    rw [div_mul_eq_mul_div, div_le_one (by nlinarith)]
    nlinarith
  calc volume (cfCylinder (w ++ u)) * (Nat.fib (u.length + 1) : ENNReal) ^ 2
      ≤ 2 * (volume (cfCylinder w) * volume (cfCylinder u)) *
          (Nat.fib (u.length + 1) : ENNReal) ^ 2 := by gcongr
    _ = 2 * volume (cfCylinder w) *
          (volume (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2) := by
        ring
    _ ≤ 2 * volume (cfCylinder w) * 1 := by gcongr
    _ = 2 * volume (cfCylinder w) := mul_one _

end NormalNumbers
