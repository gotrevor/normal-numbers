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
theorem volume_eq_tsum_extensions (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (n : ℕ) :
    volume (cfCylinder w) =
      ∑' u : genWords n, volume (cfCylinder (w ++ (u : List ℕ))) := by
  sorry

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
  sorry

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
  sorry

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
