/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyRenewal
import NormalNumbers.CFDigitLaw

/-!
# The gap-zero Rényi comparison — the brick the class Doeblin step needs

`VandeheyRenewal.lean` leaves the crux of Vandehey 2017 Theorem 1.1 as a *contraction*: the class
kernel `ν_m(d,d') = γ(classEvent D m d d')` must converge to `1/|ℙ¹(ℤ/D)|`.  Every route to that
contraction needs a **Doeblin minorization**: a uniform lower bound

> `γ(E ∩ T^{-n}(classEvent D M d d')) ≥ α · γ(E)`  for every past event `E` that is a union of
> genuine length-`n` cylinders,

with `α > 0` independent of `E`, `d`, `d'`.  And this is exactly where the repo's ψ-mixing pin
*cannot* be used.

**The adjacency obstruction.**  `gaussMeasure_cylinder_psi_mixing` compares
`γ(I_v ∩ T^{-(|v|+g)}A)` with `γ(I_v)·γ(A)` up to a multiplicative error `(79/100)^g`.  At `g = 0`
that error is `1` and the bound degenerates to `γ(I_v ∩ T^{-|v|}A) ≥ 0`.  But the class block and
the past block are **adjacent**: the class after `n` digits is a function of digits `1 … n`, and
the Doeblin word occupies digits `n+1 … n+M`.  There is no gap to spend, and inserting one does not
help, because the gap digits themselves move the class (every `classStep D · a` is a *bijection*,
so nothing is ever forgotten — `VandeheyRenewal.classStep_bijective`).

**The substitute.**  Run the same mixture representation with `g = 0` and keep a *constant* instead
of a decaying error.  `horizonIntegral A 0 t = ∫_A h_t` with `h_t(y) = (1+t)/(1+ty)²`, and on
`[0,1]²` one has `h_t(y) ∈ [1/4, 2]`; comparing with the Gauss density `1/((1+y)\log 2) ≤ 1/\log 2`
gives `horizonIntegral A 0 t ≥ (\log 2/4)·γ(A)` — a bound with **no** `t`-dependence.  Feeding it
through the very mixture identity that proves ψ-mixing yields

> **`gaussMeasure_cylinder_renyi_lower`**: `(\log 2/4)·γ(I_v)·γ(A) ≤ γ(I_v ∩ T^{-|v|}A)`,

the classical Rényi bounded-distortion inequality for continued fractions, in the exact form the
class renewal consumes.  The countable-family version (`gaussMeasure_familySetC_renyi_lower`) is
the one the past event actually needs, since "the class after `n` digits is `d`" is a countable
union of length-`n` cylinders and never a single cylinder.
-/

namespace NormalNumbers

namespace VandeheyRenyi

open MeasureTheory VandeheyMix

/-! ## The constant -/

/-- The Rényi constant `log 2 / 4`: `1/4` from `h_t ≥ 1/4` on `[0,1]²`, `log 2` from
`γ(A) ≤ |A|/log 2`. -/
noncomputable def renyiConst : ℝ := Real.log 2 / 4

lemma renyiConst_pos : 0 < renyiConst := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [renyiConst]; linarith

/-! ## The conditional density is bounded below on the unit square -/

/-- `h_t(y) = (1+t)/(1+ty)² ≥ 1/4` for `t, y ∈ [0,1]`: the numerator is `≥ 1` and the
denominator `≤ 4`. -/
lemma tailDensity_ge_quarter {t y : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : (1 : ℝ) / 4 ≤ tailDensity t y := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hy0, hy1⟩ := hy
  have hty : t * y ≤ 1 := by nlinarith
  have hty0 : 0 ≤ t * y := mul_nonneg ht0 hy0
  have hden : (0 : ℝ) < (1 + t * y) ^ 2 := by nlinarith
  rw [tailDensity, le_div_iff₀ hden]
  nlinarith

/-! ## The `g = 0` horizon integral -/

lemma horizonSet_zero {A : Set ℝ} (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) : horizonSet A 0 = A := by
  rw [horizonSet, Function.iterate_zero, Set.preimage_id,
    Set.inter_eq_self_of_subset_right hA1]

/-- **The gap-zero pin, with a constant.**  `G_0(t) ≥ (log 2/4)·γ(A)` for every `t ∈ [0,1]`.
This is the replacement for `horizonIntegral_pin_geom` at `g = 0`, where the geometric error is
vacuous. -/
lemma horizonIntegral_zero_ge {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    renyiConst * (gaussMeasure A).toReal ≤ horizonIntegral A 0 t := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hvolfin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (hA1.trans Set.Ioo_subset_Icc_self))
    simp [Real.volume_Icc]
  -- `γ(A) ≤ |A| / log 2`
  have hγle : (gaussMeasure A).toReal ≤ (Real.log 2)⁻¹ * (volume A).toReal := by
    have h := gaussMeasure_le_volume A hA
    have hfin : ENNReal.ofReal (Real.log 2)⁻¹ * volume A ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hvolfin
    have := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  -- `∫_A h_t ≥ |A|/4`
  have hint : IntegrableOn (tailDensity t) A volume :=
    (integrableOn_tailDensity ht.1).mono_set hA1
  have hge : (1 : ℝ) / 4 * (volume A).toReal ≤ ∫ y in A, tailDensity t y := by
    have := setIntegral_ge_of_const_le_real (μ := volume) (s := A) (c := (1 : ℝ) / 4)
      (f := tailDensity t) hA hvolfin
      (fun y hy => tailDensity_ge_quarter ht (Set.Ioo_subset_Icc_self (hA1 hy))) hint
    simpa [Measure.real] using this
  have hrw : horizonIntegral A 0 t = ∫ y in A, tailDensity t y := by
    rw [horizonIntegral, horizonSet_zero hA1]
  rw [hrw]
  refine le_trans ?_ hge
  have hvol0 : (0 : ℝ) ≤ (volume A).toReal := ENNReal.toReal_nonneg
  calc renyiConst * (gaussMeasure A).toReal
      ≤ renyiConst * ((Real.log 2)⁻¹ * (volume A).toReal) :=
        mul_le_mul_of_nonneg_left hγle (le_of_lt renyiConst_pos)
    _ = (1 : ℝ) / 4 * (volume A).toReal := by
        rw [renyiConst]; field_simp

/-! ## The Rényi comparison for a single cylinder -/

/-- **The gap-zero Rényi inequality.**  `γ(I_v ∩ T^{-|v|}A) ≥ (log 2/4)·γ(I_v)·γ(A)`.

This is the classical bounded-distortion (Rényi) lower bound for continued fractions, obtained by
running the ψ-mixing mixture representation at gap `0` and replacing the geometric pin
`horizonIntegral_pin_geom` (vacuous there) by the constant pin `horizonIntegral_zero_ge`.  Unlike
ψ-mixing it needs no gap, which is what makes it usable for the **adjacent** blocks of the class
renewal. -/
theorem gaussMeasure_cylinder_renyi_lower (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    renyiConst * (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure A).toReal
      ≤ (gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' A)).toReal := by
  set X : Set ℝ := cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' A with hX
  have hXmeas : MeasurableSet X :=
    (measurableSet_cfCylinder v).inter ((measurable_gaussMap.iterate v.length) hA)
  have hX1 : X ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => hx.1.1
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  have hV1 := cfCylinder_subset_Ioo v
  set M : ℝ → ℝ := fun s => ∫ y in cfCylinder v, tailDensity s y with hM
  set γA : ℝ := (gaussMeasure A).toReal with hγA
  have hγA0 : 0 ≤ γA := ENNReal.toReal_nonneg
  -- the two mixture representations
  have hmixX : (gaussMeasure X).toReal
      = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * ∫ y in X, tailDensity s y := by
    rw [gaussMeasure_toReal_eq hXmeas hX1, integral_gaussDensityReal_eq_mix hXmeas hX1]
  have hmixV : (gaussMeasure (cfCylinder v)).toReal
      = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * M s := by
    rw [gaussMeasure_toReal_eq hVmeas hV1, integral_gaussDensityReal_eq_mix hVmeas hV1]
  -- the conditional factorization at gap zero
  have hfact : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∫ y in X, tailDensity s y
      = horizonIntegral A 0 (tChain s v) * M s := by
    intro s hs
    have hset : cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' A
        = cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (horizonSet A 0) := by
      rw [horizonSet_zero hA1]
    rw [hX, hset, setIntegral_inter_preimage v hpos hs (horizonSet A 0)
        (measurableSet_horizonSet hA 0) (horizonSet_subset A 0)]
    rfl
  -- nonnegativity and continuity ingredients
  have hM0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M s := by
    intro s hs
    rw [hM]
    refine setIntegral_nonneg hVmeas fun y hy => ?_
    have := tailDensity_ge_quarter hs (Set.Ioo_subset_Icc_self (hV1 hy))
    linarith
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hcontM : ContinuousOn M (Set.Icc (0 : ℝ) 1) := by
    have h := continuousOn_horizonIntegral hVmeas hV1 0
    have hB0 : horizonSet (cfCylinder v) 0 = cfCylinder v := horizonSet_zero hV1
    have heq : M = horizonIntegral (cfCylinder v) 0 := by
      funext s; rw [hM, horizonIntegral, hB0]
    rw [heq]; exact h
  have hcontτ := continuousOn_tChain v hpos
  have hτmap : Set.MapsTo (fun s => tChain s v) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => tChain_mem_Icc hs v hpos
  have hcontG : ContinuousOn (fun s => horizonIntegral A 0 (tChain s v))
      (Set.Icc (0 : ℝ) 1) := (continuousOn_horizonIntegral hA hA1 0).comp hcontτ hτmap
  have hcont1 : ContinuousOn
      (fun s => gaussDensityReal s * (horizonIntegral A 0 (tChain s v) * M s))
      (Set.Icc (0 : ℝ) 1) := hcontw.mul (hcontG.mul hcontM)
  have hcont2 : ContinuousOn (fun s => gaussDensityReal s * (renyiConst * γA * M s))
      (Set.Icc (0 : ℝ) 1) := hcontw.mul (continuousOn_const.mul hcontM)
  have hint1 : IntegrableOn
      (fun s => gaussDensityReal s * (horizonIntegral A 0 (tChain s v) * M s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (hcont1.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun s => gaussDensityReal s * (renyiConst * γA * M s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (hcont2.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  -- the pointwise inequality, then integrate
  have hmono : ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (renyiConst * γA * M s)
      ≤ ∫ s in Set.Ioo (0 : ℝ) 1,
          gaussDensityReal s * (horizonIntegral A 0 (tChain s v) * M s) := by
    refine setIntegral_mono_on hint2 hint1 measurableSet_Ioo fun s hs => ?_
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hs
    have hw0 : 0 ≤ gaussDensityReal s := by
      have := hs.1
      simp only [gaussDensityReal]
      have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hw0
    refine mul_le_mul_of_nonneg_right ?_ (hM0 s hsIcc)
    exact horizonIntegral_zero_ge hA hA1 (hτmap hsIcc)
  have hLHS : ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (renyiConst * γA * M s)
      = renyiConst * γA * (gaussMeasure (cfCylinder v)).toReal := by
    have hfun : (fun s => gaussDensityReal s * (renyiConst * γA * M s))
        = fun s => (renyiConst * γA) * (gaussDensityReal s * M s) := by
      funext s; ring
    rw [hfun, integral_const_mul, ← hmixV]
  have hRHS : ∫ s in Set.Ioo (0 : ℝ) 1,
      gaussDensityReal s * (horizonIntegral A 0 (tChain s v) * M s)
      = (gaussMeasure X).toReal := by
    rw [hmixX]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    rw [hfact s (Set.Ioo_subset_Icc_self hs)]
  calc renyiConst * (gaussMeasure (cfCylinder v)).toReal * γA
      = renyiConst * γA * (gaussMeasure (cfCylinder v)).toReal := by ring
    _ = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (renyiConst * γA * M s) := hLHS.symm
    _ ≤ ∫ s in Set.Ioo (0 : ℝ) 1,
          gaussDensityReal s * (horizonIntegral A 0 (tChain s v) * M s) := hmono
    _ = (gaussMeasure X).toReal := hRHS

/-! ## The Rényi comparison against a countable family

The past event of the class renewal — "the class after `n` digits is `d`" — is a countable union of
length-`n` cylinders, never a single cylinder.  As with ψ-mixing, the *multiplicative* shape of the
bound is exactly what survives summation over the family. -/

lemma familySetC_subset_Ioo (S : Set (List ℕ)) : familySetC S ⊆ Set.Ioo (0 : ℝ) 1 := by
  refine Set.iUnion₂_subset fun w _ => cfCylinder_subset_Ioo w

/-- **The gap-zero Rényi inequality against a countable family.** -/
theorem gaussMeasure_familySetC_renyi_lower {S : Set (List ℕ)} (hct : S.Countable) {n : ℕ}
    (hlen : ∀ w ∈ S, w.length = n) (hpos : ∀ w ∈ S, ∀ a ∈ w, 1 ≤ a)
    {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    renyiConst * (gaussMeasure (familySetC S)).toReal * (gaussMeasure A).toReal
      ≤ (gaussMeasure (familySetC S ∩ (gaussMap^[n]) ⁻¹' A)).toReal := by
  classical
  set P : Set ℝ := (gaussMap^[n]) ⁻¹' A with hP
  have hPmeas : MeasurableSet P := (measurable_gaussMap.iterate n) hA
  set γA : ℝ := (gaussMeasure A).toReal with hγA
  have hγA0 : 0 ≤ γA := ENNReal.toReal_nonneg
  set b : S → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ))).toReal with hbdef
  set a : S → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ) ∩ P)).toReal with hadef
  have htotb : (gaussMeasure (familySetC S)).toReal = ∑' w : S, b w := by
    rw [gaussMeasure_familySetC hct hlen, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have htota : (gaussMeasure (familySetC S ∩ P)).toReal = ∑' w : S, a w := by
    rw [gaussMeasure_familySetC_inter hct hlen hPmeas,
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have hsumb : Summable b := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC hct hlen]
    exact measure_ne_top _ _
  have hsuma : Summable a := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC_inter hct hlen hPmeas]
    exact measure_ne_top _ _
  have hterm : ∀ w : S, renyiConst * γA * b w ≤ a w := by
    intro w
    have h := gaussMeasure_cylinder_renyi_lower (w : List ℕ) (hpos _ w.2) hA hA1
    rw [hlen _ w.2] at h
    calc renyiConst * γA * b w = renyiConst * b w * γA := by ring
      _ ≤ a w := h
  have hsumbnd : Summable fun w : S => renyiConst * γA * b w := hsumb.mul_left _
  calc renyiConst * (gaussMeasure (familySetC S)).toReal * γA
      = ∑' w : S, renyiConst * γA * b w := by
        rw [htotb, tsum_mul_left]; ring
    _ ≤ ∑' w : S, a w := Summable.tsum_le_tsum hterm hsumbnd hsuma
    _ = (gaussMeasure (familySetC S ∩ P)).toReal := htota.symm

/-! ## Doeblin: three digits connect every pair of classes

`VandeheyClass.exists_word_reach` gives a connecting word of length `≤ 3`; the minorization needs
a **fixed** length, so every pair must be connected in length *exactly* `3`.  That is true, and the
parity trap is real: `some 0` reaches `∞` in one step and in three, but **never** in two. -/

namespace Doeblin

open VandeheyAut VandeheyClass VandeheyRenewal VandeheyMix

variable {D : ℕ}

private lemma mem_three {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ∀ x ∈ [a, b, c], 1 ≤ x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h <;> subst h <;> assumption

/-- **Doeblin transitivity at length exactly three.**  For prime `D` every pair of classes is
connected by a genuine CF word of length `3`.  The four cases use the three-step skeleton
`· → some 0 → ∞ → ·` (or `· → some 1 → some 0 → ∞` when the target is `∞`), which is available
precisely because `ZMod D` is a field. -/
theorem exists_classWord_three [Fact (Nat.Prime D)] (c c' : ClassSpace D) :
    ∃ w : List ℕ, w.length = 3 ∧ (∀ x ∈ w, 1 ≤ x) ∧ classSigma D w c = c' := by
  have hD : 1 ≤ D := le_of_lt (Fact.out : Nat.Prime D).one_lt
  have hone : (1 : ZMod D) ≠ 0 := one_ne_zero
  obtain ⟨z0, hz0, hz0c⟩ := exists_digit_cast D hD 0
  obtain ⟨m1, hm1, hm1c⟩ := exists_digit_cast D hD (-1)
  cases c with
  | none =>
    cases c' with
    | none =>
      -- `∞ → some 1 → some 0 → ∞`
      refine ⟨[1, m1, 1], rfl, mem_three le_rfl hm1 le_rfl, ?_⟩
      show classStep D (classStep D (classStep D none 1) m1) 1 = none
      rw [classStep_none, Nat.cast_one, classStep_some_of_ne D hone, hm1c, inv_one]
      simp
    | some z =>
      -- `∞ → some 0 → ∞ → some z`
      obtain ⟨az, haz, hazc⟩ := exists_digit_cast D hD z
      refine ⟨[z0, 1, az], rfl, mem_three hz0 le_rfl haz, ?_⟩
      show classStep D (classStep D (classStep D none z0) 1) az = some z
      rw [classStep_none, hz0c, classStep_zero, classStep_none, hazc]
  | some s =>
    by_cases hs : s = 0
    · subst hs
      cases c' with
      | none =>
        -- `some 0 → ∞ → some 0 → ∞`
        refine ⟨[1, z0, 1], rfl, mem_three le_rfl hz0 le_rfl, ?_⟩
        show classStep D (classStep D (classStep D (some 0) 1) z0) 1 = none
        rw [classStep_zero, classStep_none, hz0c, classStep_zero]
      | some z =>
        -- `some 0 → ∞ → some 1 → some z`
        obtain ⟨az, haz, hazc⟩ := exists_digit_cast D hD (z - 1)
        refine ⟨[1, 1, az], rfl, mem_three le_rfl le_rfl haz, ?_⟩
        show classStep D (classStep D (classStep D (some 0) 1) 1) az = some z
        rw [classStep_zero, classStep_none, Nat.cast_one,
          classStep_some_of_ne D hone, hazc, inv_one]
        congr 1
        ring
    · cases c' with
      | none =>
        -- `some s → some 1 → some 0 → ∞`
        obtain ⟨a1, ha1, ha1c⟩ := exists_digit_cast D hD (1 - s⁻¹)
        refine ⟨[a1, m1, 1], rfl, mem_three ha1 hm1 le_rfl, ?_⟩
        show classStep D (classStep D (classStep D (some s) a1) m1) 1 = none
        rw [classStep_some_of_ne D hs, ha1c]
        have h1 : (1 : ZMod D) - s⁻¹ + s⁻¹ = 1 := by ring
        rw [h1, classStep_some_of_ne D hone, hm1c, inv_one]
        have h2 : (-1 : ZMod D) + 1 = 0 := by ring
        rw [h2, classStep_zero]
      | some z =>
        -- `some s → some 0 → ∞ → some z`
        obtain ⟨a0, ha0, ha0c⟩ := exists_digit_cast D hD (-s⁻¹)
        obtain ⟨az, haz, hazc⟩ := exists_digit_cast D hD z
        refine ⟨[a0, 1, az], rfl, mem_three ha0 le_rfl haz, ?_⟩
        show classStep D (classStep D (classStep D (some s) a0) 1) az = some z
        rw [classStep_some_of_ne D hs, ha0c]
        have h1 : (-s⁻¹ : ZMod D) + s⁻¹ = 0 := by ring
        rw [h1, classStep_zero, classStep_none, hazc]

/-! ## A genuine cylinder has positive Gauss mass

(The same two-line argument as `CFScheduleA.gaussMeasure_cfCylinder_toReal_pos`, replayed here so
the Vandehey chain does not have to import the schedule file.) -/

lemma volume_cfCylinder_toReal_pos (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    0 < (volume (cfCylinder w)).toReal := by
  have hK1 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hpos
  have hKd : (cfK w.dropLast : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast cfK_dropLast_le w hpos
  have hKd0 : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  rw [volume_cfCylinder w hw hpos, ENNReal.toReal_ofReal (by positivity)]
  have hden : (0 : ℝ) < (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by nlinarith
  exact div_pos one_pos hden

lemma gaussMeasure_cfCylinder_toReal_pos (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) : 0 < (gaussMeasure (cfCylinder w)).toReal := by
  have hsub : cfCylinder w ⊆ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo w
  have hmeas : MeasurableSet (cfCylinder w) := measurableSet_cfCylinder w
  have hvolpos : 0 < (volume (cfCylinder w)).toReal := volume_cfCylinder_toReal_pos w hw hpos
  have hle := volume_le_gaussMeasure (cfCylinder w) hmeas hsub
  have hmono := ENNReal.toReal_mono (measure_ne_top gaussMeasure (cfCylinder w)) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hmono
  refine lt_of_lt_of_le ?_ hmono
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hvolpos

/-! ## The Doeblin constant, and the conditional minorization -/

/-- **The Doeblin constant.**  Every length-`3` class-transition event has mass bounded below by a
single positive `β`, uniformly over the (finitely many) pairs of classes. -/
theorem exists_doeblin_const (D : ℕ) [Fact (Nat.Prime D)] :
    ∃ β : ℝ, 0 < β ∧ ∀ d d' : ClassSpace D,
      β ≤ (gaussMeasure (classEvent D 3 d d')).toReal := by
  classical
  have hpos : ∀ p : ClassSpace D × ClassSpace D,
      0 < (gaussMeasure (classEvent D 3 p.1 p.2)).toReal := by
    intro p
    obtain ⟨w, hwlen, hwpos, hw⟩ := exists_classWord_three (D := D) p.1 p.2
    have hmem : w ∈ classWords D 3 p.1 p.2 := ⟨hwlen, hwpos, hw⟩
    have hsub : cfCylinder w ⊆ classEvent D 3 p.1 p.2 :=
      Set.subset_biUnion_of_mem (u := fun w => cfCylinder w) hmem
    have hwne : w ≠ [] := by
      intro h; rw [h] at hwlen; simp at hwlen
    refine lt_of_lt_of_le (gaussMeasure_cfCylinder_toReal_pos w hwne hwpos) ?_
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min
    (fun p : ClassSpace D × ClassSpace D => (gaussMeasure (classEvent D 3 p.1 p.2)).toReal)
  exact ⟨_, hpos p₀, fun d d' => hp₀ (d, d')⟩

/-- **The conditional Doeblin minorization** — the deliverable this whole file was built for.
For *every* past event `E` that is a countable union of genuine length-`n` cylinders, and every
pair of classes `d, d'`, the next three digits carry `d` to `d'` with conditional probability at
least `α = (log 2/4)·β > 0`, uniformly in `E`, `n`, `d`, `d'`.

The uniformity in `E` is the whole point: `E` may encode arbitrary information about the class at
time `n` and about the digits that produced it, and the bound is unaffected.  This is the
hypothesis of the Doeblin coupling for a *non-Markov* chain, and it is available here only because
the Rényi bound needs no gap (ψ-mixing would be vacuous, the blocks being adjacent). -/
theorem exists_minorization_const (D : ℕ) [Fact (Nat.Prime D)] :
    ∃ α : ℝ, 0 < α ∧ ∀ (S : Set (List ℕ)) (n : ℕ), S.Countable → (∀ w ∈ S, w.length = n) →
      (∀ w ∈ S, ∀ a ∈ w, 1 ≤ a) → ∀ d d' : ClassSpace D,
      α * (gaussMeasure (familySetC S)).toReal
        ≤ (gaussMeasure (familySetC S ∩ (gaussMap^[n]) ⁻¹' classEvent D 3 d d')).toReal := by
  obtain ⟨β, hβ0, hβ⟩ := exists_doeblin_const D
  refine ⟨renyiConst * β, mul_pos renyiConst_pos hβ0, fun S n hct hlen hposS d d' => ?_⟩
  have hAmeas : MeasurableSet (classEvent D 3 d d') :=
    measurableSet_familySetC (countable_wordSet _)
  have hA1 : classEvent D 3 d d' ⊆ Set.Ioo (0 : ℝ) 1 := familySetC_subset_Ioo _
  have hkey := gaussMeasure_familySetC_renyi_lower hct hlen hposS hAmeas hA1
  refine le_trans ?_ hkey
  have hE0 : (0 : ℝ) ≤ (gaussMeasure (familySetC S)).toReal := ENNReal.toReal_nonneg
  have hmul : renyiConst * β * (gaussMeasure (familySetC S)).toReal
      = renyiConst * (gaussMeasure (familySetC S)).toReal * β := by ring
  rw [hmul]
  exact mul_le_mul_of_nonneg_left (hβ d d') (mul_nonneg (le_of_lt renyiConst_pos) hE0)

end Doeblin

end VandeheyRenyi

end NormalNumbers
