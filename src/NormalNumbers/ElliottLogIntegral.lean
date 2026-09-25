import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The calculus core of the `ζ'/ζ` route (lap 99)

Laps 97–98 turned `archCorr v X` into the Dirichlet series `∑_p p^{-1-δ-iv}` (`δ = 1/log X`) up to
an absolute constant.  The route recorded in `ElliottDamped` continues

  `∑_p p^{-s} = ∫_0^∞ (−ζ'/ζ)(s+w) dw + O(1)`  (from `1/log n = ∫_0^∞ n^{-w} dw`),

so that a bound on `ζ'/ζ` on the half-plane `σ > 1` becomes a bound on the correlation by a single
integration.  **This file is that integration**, isolated from the ζ input so it can be proved
first and reused for both soft bands:

* sub-unit band `|v| ≤ 1`: the pole bound `|ζ'/ζ(σ+w+iv)| ≤ min((δ+w)^{-1}, |v|^{-1})` gives
  `T = |v|` and the conclusion `log(1/|v|) + O(1)` — exactly `ShiftedMertensSmall`;
* moderate band `|v| > 1`: the de la Vallée Poussin bound `|ζ'/ζ| ≤ C log|v|` gives
  `T = 1/(C log|v|)` and the conclusion `log log |v| + O(1)` — exactly `ArchCorrModerate`.

So a *single* elementary lemma converts either ζ input into the corresponding band bound, and the
two bands differ only in the value of `T`.  The shape is the familiar one: the integrand is capped
at `T^{-1}` on `[0,T]` (contributing `≤ 1`) and is at most `w^{-1}` on `[T,1]` (contributing
`log(1/T)`).  The range `w ≥ 1` contributes `O(1)` for a different, purely elementary reason
(`|ζ'/ζ(σ)| ≤ 2^{-(σ-2)}∑_n Λ(n)n^{-2}` for `σ ≥ 2`), and is not part of this file.
-/

open MeasureTheory intervalIntegral

namespace NormalNumbers.ElliottLogIntegral

noncomputable section

/-- **The capped-integrand bound.**  A nonnegative function which is at most `T⁻¹` and at most
`(δ+w)⁻¹` on `[0,1]` has integral at most `1 + log(1/T)`.

This is the whole `log` in `log(1/|v|)` and in `log log|v|`: the cap contributes an absolute
constant, and the tail of the harmonic integrand contributes the logarithm of the cap's width. -/
theorem integral_le_one_add_log {f : ℝ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hδT : δ ≤ T) (hT1 : T ≤ 1)
    (hf : IntervalIntegrable f volume 0 1)
    (hnn : ∀ w ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f w)
    (hcap : ∀ w ∈ Set.Icc (0 : ℝ) T, f w ≤ T⁻¹)
    (hharm : ∀ w ∈ Set.Icc T 1, f w ≤ w⁻¹) :
    ∫ w in (0 : ℝ)..1, f w ≤ 1 + Real.log (1 / T) := by
  have hT0 : 0 < T := lt_of_lt_of_le hδ hδT
  have hsplit : (∫ w in (0 : ℝ)..1, f w)
      = (∫ w in (0 : ℝ)..T, f w) + ∫ w in T..(1 : ℝ), f w := by
    refine (integral_add_adjacent_intervals ?_ ?_).symm
    · exact hf.mono_set (Set.uIcc_subset_uIcc_left
        (Set.mem_uIcc.mpr (Or.inl ⟨hT0.le, hT1⟩)))
    · exact hf.mono_set (Set.uIcc_subset_uIcc_right
        (Set.mem_uIcc.mpr (Or.inl ⟨hT0.le, hT1⟩)))
  have hint1 : IntervalIntegrable f volume 0 T :=
    hf.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.mpr (Or.inl ⟨hT0.le, hT1⟩)))
  have hint2 : IntervalIntegrable f volume T 1 :=
    hf.mono_set (Set.uIcc_subset_uIcc_right (Set.mem_uIcc.mpr (Or.inl ⟨hT0.le, hT1⟩)))
  -- the capped piece
  have hpiece1 : (∫ w in (0 : ℝ)..T, f w) ≤ 1 := by
    have hmono : (∫ w in (0 : ℝ)..T, f w) ≤ ∫ _w in (0 : ℝ)..T, T⁻¹ := by
      refine integral_mono_on hT0.le hint1 intervalIntegrable_const ?_
      intro w hw
      exact hcap w hw
    have : (∫ _w in (0 : ℝ)..T, T⁻¹) = 1 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      field_simp
      ring
    linarith [hmono, this ▸ hmono]
  -- the harmonic piece
  have hpiece2 : (∫ w in T..(1 : ℝ), f w) ≤ Real.log (1 / T) := by
    have hmono : (∫ w in T..(1 : ℝ), f w) ≤ ∫ w in T..(1 : ℝ), w⁻¹ := by
      refine integral_mono_on hT1 hint2 ?_ ?_
      · refine intervalIntegral.intervalIntegrable_inv ?_ continuousOn_id
        intro x hx
        have : T ≤ x := (Set.mem_uIcc.mp hx).elim (fun h => h.1) (fun h => le_trans hT1 h.1)
        exact ne_of_gt (lt_of_lt_of_le hT0 this)
      · intro w hw
        exact hharm w hw
    have hval : (∫ w in T..(1 : ℝ), w⁻¹) = Real.log (1 / T) := by
      rw [integral_inv_of_pos hT0 (by norm_num)]
    linarith [hval ▸ hmono]
  rw [hsplit]
  linarith

end

end NormalNumbers.ElliottLogIntegral
