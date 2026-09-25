import NormalNumbers.ElliottBridge
import NormalNumbers.ElliottZetaPole

/-!
# (c′-I) CLOSED: the sub-unit cap clause is a theorem

Laps 103–111 reduced input (c′-I) to the single `Prop` `ElliottDamped.SliceCapSmall` and proved
every ingredient of it.  This file performs the assembly:

1. `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` reads `L ↗Λ s = −ζ'/ζ(s)` for `1 < Re s`;
2. splitting `L ↗Λ s` at the finite set `primesUpTo Y` and using `ElliottBridge.slice_eq_sum_term`
   identifies the finite part with `logWeightedSlice`, so the difference is the tail `T`;
3. `ElliottBridge.sum_complement_le` bounds every finite partial sum of `‖T‖` by `1 + ppCost`,
   hence `‖T‖ ≤ 1 + ppCost` by `tsum_le_of_sum_le`;
4. `exists_band_logDeriv_bound` (this file: `ElliottZetaPole.exists_subunit_logDeriv_bound` with
   the right edge `Re s ≤ 2` widened to an arbitrary `B`, needed because `Re s = 1 + δ + w` can
   exceed `2` by `δ` inside the cap band) supplies `‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K`, and in the cap band
   `‖s − 1‖ ≥ max(δ + w, |v|) ≥ T`.

**No zero-free region is used anywhere**: the pole of `ζ` supplies `1/‖s−1‖` near `1`, and
compactness plus `riemannZeta_ne_zero_of_one_le_re` supplies the constant elsewhere.

EP-1 provenance note: the analytic input here is the *pole-local* bound, proved in
`ElliottZetaPole` from mathlib alone.  The de la Vallée Poussin material needed for the **moderate**
band is NOT re-derived — it is `PNTPort.ZetaBounds.LogDerivZetaBndUnif99` (in-repo, sorry-free);
import it as `PNTPort.ZetaBounds`, never as `PrimeNumberTheoremAnd.ZetaBounds`.
-/

open Finset ArithmeticFunction

namespace NormalNumbers.ElliottSliceCap

open NormalNumbers.ElliottDamped NormalNumbers.ElliottBridge NormalNumbers.ElliottZetaPole
open NormalNumbers.ElliottPrimePower Erdos67b.PrimeEstimates Erdos67b

noncomputable section

/-! ### The far band with an arbitrary right edge -/

/-- `ElliottZetaPole.exists_far_band_bound` with `Re s ≤ 2` widened to `Re s ≤ B`. -/
theorem exists_far_band_bound_le {r : ℝ} (hr : 0 < r) (B : ℝ) :
    ∃ K > 0, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ B → |s.im| ≤ 1 → r ≤ ‖s - 1‖ →
      ‖logDeriv riemannZeta s‖ ≤ K := by
  set S : Set ℂ := {s | 1 ≤ s.re} ∩ ({s | s.re ≤ B} ∩ ({s | |s.im| ≤ 1} ∩ {s | r ≤ ‖s - 1‖}))
    with hS
  have hclosed : IsClosed S := by
    rw [hS]
    refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
    refine (isClosed_le (Complex.continuous_im.abs) continuous_const).inter ?_
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |B| + 2)).subset ?_
    intro s hs
    obtain ⟨h1, h2, h3, -⟩ := hs
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    have hB : B ≤ |B| := le_abs_self B
    have hre : |s.re| ≤ |B| := by rw [abs_le]; constructor <;> [linarith; linarith]
    have hnorm : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne1 : ∀ s ∈ S, s ≠ 1 := by
    intro s hs h
    obtain ⟨-, -, -, h4⟩ := hs
    simp only [Set.mem_setOf_eq, h, sub_self, norm_zero] at h4
    linarith
  have hcont : ContinuousOn (logDeriv riemannZeta) S := by
    intro s hs
    have hs1 : s ≠ 1 := hne1 s hs
    have h1 : 1 ≤ s.re := hs.1
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
    have hanal : AnalyticAt ℂ riemannZeta s :=
      analyticOn_riemannZeta s (by simpa using hs1)
    exact ContinuousAt.continuousWithinAt
      (hanal.deriv.continuousAt.div hanal.continuousAt hz)
  obtain ⟨K₀, hK₀⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨|K₀| + 1, by positivity, ?_⟩
  intro s h1 h2 h3 h4
  have hmem : s ∈ S := ⟨h1, h2, h3, h4⟩
  have := hK₀ s hmem
  have := le_abs_self K₀
  linarith

/-- **The analytic side, on a band of arbitrary width.**  `‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K` for `s ≠ 1`,
`1 ≤ Re s ≤ B`, `|Im s| ≤ 1`.  (`ElliottZetaPole.exists_subunit_logDeriv_bound` is `B = 2`; the cap
band needs `B = 3` because `Re s = 1 + δ + w` with `w` up to `max(|v|, δ) ≤ 1`.) -/
theorem exists_band_logDeriv_bound (B : ℝ) :
    ∃ K > 0, ∀ s : ℂ, s ≠ 1 → 1 ≤ s.re → s.re ≤ B → |s.im| ≤ 1 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ 1 / ‖s - 1‖ + K := by
  obtain ⟨r, hr, K₁, hK₁, hpole⟩ := exists_pole_local_bound
  obtain ⟨K₂, hK₂, hfar⟩ := exists_far_band_bound_le hr B
  refine ⟨max K₁ K₂, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro s hs h1 h2 h3
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
  refine ⟨hz, ?_⟩
  rcases le_or_gt ‖s - 1‖ r with hle | hgt
  · have hb : ‖logDeriv riemannZeta s‖ ≤ 1 / ‖s - 1‖ + K₁ := (hpole s hs hle).2
    have hmax : K₁ ≤ max K₁ K₂ := le_max_left _ _
    linarith
  · have hbound := hfar s h1 h2 h3 hgt.le
    have hnn : 0 ≤ 1 / ‖s - 1‖ := by positivity
    have hmax : K₂ ≤ max K₁ K₂ := le_max_right _ _
    linarith

/-! ### The arithmetic side: the slice is `−ζ'/ζ` up to `1 + ppCost` -/

/-- The terms of `L ↗Λ` that the slice *misses*: primes past `Y`, and all higher prime powers. -/
def tailFun (Y : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if n ∈ primesUpTo Y then 0 else LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n

theorem norm_term_vonMangoldt (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n‖
      = (vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (by positivity),
      div_eq_mul_inv]

theorem norm_tailFun_le (Y : ℕ) (s : ℂ) (n : ℕ) :
    ‖tailFun Y s n‖ ≤ ‖LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n‖ := by
  rw [tailFun]
  split
  · simpa using norm_nonneg _
  · exact le_rfl

/-- **THE ARITHMETIC BRIDGE, ASSEMBLED.**  `logWeightedSlice = −ζ'/ζ(sliceAbscissa) + O(1)`, with
the absolute constant `1 + ppCost`. -/
theorem norm_slice_add_logDeriv_le {X Y : ℕ} (hX : 1048576 ≤ X) (hY : sliceCut X ≤ Y)
    (v w : ℝ) (hw : 0 ≤ w) :
    ‖logWeightedSlice v X Y w + logDeriv riemannZeta (sliceAbscissa X w v)‖ ≤ 1 + ppCost := by
  classical
  set s : ℂ := sliceAbscissa X w v with hs
  have hX2 : 2 ≤ X := by omega
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hδ : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hre : s.re = 1 + (Real.log (X : ℝ))⁻¹ + w := by rw [hs]; exact sliceAbscissa_re w v
  have hσ1 : 1 < s.re := by rw [hre]; linarith
  have hσge : 1 + (Real.log (X : ℝ))⁻¹ ≤ s.re := by rw [hre]; linarith
  -- summability
  have hsum : Summable (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσ1
  have hsumn : Summable (fun n => ‖LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n‖) :=
    summable_norm_iff.mpr hsum
  have htailn : Summable (fun n => ‖tailFun Y s n‖) :=
    hsumn.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_tailFun_le Y s)
  have htail : Summable (tailFun Y s) := summable_norm_iff.mp htailn
  -- the finite part
  have hfin : Summable (fun n => if n ∈ primesUpTo Y then
      LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n else 0) :=
    summable_of_ne_finset_zero (s := primesUpTo Y) (fun b hb => by simp [hb])
  have hsplit : ∀ n : ℕ, LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n
      = (if n ∈ primesUpTo Y then
          LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n else 0) + tailFun Y s n := by
    intro n
    rw [tailFun]
    split <;> simp
  have hLS : LSeries (fun m => ((vonMangoldt m : ℝ) : ℂ)) s
      = logWeightedSlice v X Y w + ∑' n, tailFun Y s n := by
    rw [LSeries]
    rw [tsum_congr hsplit, hfin.tsum_add htail]
    congr 1
    rw [tsum_eq_sum (s := primesUpTo Y) (fun b hb => by simp [hb])]
    rw [slice_eq_sum_term v X Y w]
    exact Finset.sum_congr rfl (fun p hp => by rw [if_pos hp, hs])
  -- the analytic identification
  have hzeta : LSeries (fun m => ((vonMangoldt m : ℝ) : ℂ)) s = - logDeriv riemannZeta s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ1, logDeriv_apply]
    ring
  have hkey : logWeightedSlice v X Y w + logDeriv riemannZeta s = - ∑' n, tailFun Y s n := by
    have := hLS.symm.trans hzeta
    linear_combination this
  rw [hkey, norm_neg]
  refine le_trans (norm_tsum_le_tsum_norm htailn) ?_
  refine htailn.tsum_le_of_sum_le ?_
  intro G
  have hstep : ∑ n ∈ G, ‖tailFun Y s n‖
      = ∑ n ∈ G.filter (fun n => n ∉ primesUpTo Y),
          (vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [tailFun]
    by_cases hn : n ∈ primesUpTo Y
    · simp [hn]
    · rw [if_neg hn, if_pos hn, norm_term_vonMangoldt]
  rw [hstep]
  exact sum_complement_le hX hY hσge _ (fun n hn => (Finset.mem_filter.mp hn).2)

/-! ### (c′-I) -/

/-- **(c′-I) IS A THEOREM.**  `ElliottDamped.SliceCapSmall` holds with an explicit absolute
constant.  Together with `ElliottDamped.sliceBoundSmall_of_cap` (lap 106) and
`dampedSeriesBoundSmall_of_sliceBound` (lap 102) this discharges the whole sub-unit Archimedean
input of the Elliott consumer. -/
theorem exists_sliceCapSmall : ∃ K : ℝ, 0 ≤ K ∧ SliceCapSmall K := by
  obtain ⟨K₀, hK₀, hband⟩ := exists_band_logDeriv_bound 3
  refine ⟨K₀ + (1 + ppCost), by have := ppCost_nonneg; linarith, ?_⟩
  intro X Y v hX hY hv0 hv1 w hw
  have hX2 : 2 ≤ X := by omega
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have hXR' : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    linarith
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hδ1 : (Real.log (X : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hlogX1
  set T : ℝ := max |v| (Real.log (X : ℝ))⁻¹ with hT
  have hT0 : 0 < T := lt_of_lt_of_le hv0 (le_max_left _ _)
  have hT1 : T ≤ 1 := max_le hv1 hδ1
  have hw0 : 0 ≤ w := hw.1
  have hwT : w ≤ T := hw.2
  set s : ℂ := sliceAbscissa X w v with hsdef
  have hre : s.re = 1 + (Real.log (X : ℝ))⁻¹ + w := by rw [hsdef]; exact sliceAbscissa_re w v
  have him : s.im = v := by rw [hsdef]; exact sliceAbscissa_im w v
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hre1 : 1 ≤ s.re := by rw [hre]; linarith
  have hre3 : s.re ≤ 3 := by rw [hre]; linarith
  have him1 : |s.im| ≤ 1 := by rw [him]; exact hv1
  -- the pole distance dominates `T`
  have hdre : (s - 1).re = (Real.log (X : ℝ))⁻¹ + w := by
    rw [Complex.sub_re, Complex.one_re, hre]; ring
  have hdim : (s - 1).im = v := by rw [Complex.sub_im, Complex.one_im, him]; ring
  have hnormge : T ≤ ‖s - 1‖ := by
    rcases le_total |v| (Real.log (X : ℝ))⁻¹ with hcase | hcase
    · have : T = (Real.log (X : ℝ))⁻¹ := by rw [hT]; exact max_eq_right hcase
      rw [this]
      have h1 : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
      rw [hdre, abs_of_nonneg (by linarith)] at h1
      linarith
    · have : T = |v| := by rw [hT]; exact max_eq_left hcase
      rw [this]
      have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
      rwa [hdim] at h1
  have hinv : 1 / ‖s - 1‖ ≤ T⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hT0 hnormge
  obtain ⟨-, hlog⟩ := hband s hs1 hre1 hre3 him1
  have harith := norm_slice_add_logDeriv_le hX hY v w hw0
  have htri : ‖logWeightedSlice v X Y w‖
      ≤ ‖logWeightedSlice v X Y w + logDeriv riemannZeta s‖ + ‖logDeriv riemannZeta s‖ := by
    have := norm_sub_le (logWeightedSlice v X Y w + logDeriv riemannZeta s)
      (logDeriv riemannZeta s)
    simpa using this
  rw [← hsdef] at harith
  linarith

/-- **(c′-I) DISCHARGED END TO END.**  `ElliottArchBands.ShiftedMertensSmall` — the sub-unit
Archimedean input of the Elliott consumer — is a THEOREM, with an absolute constant.  Chain:
`exists_sliceCapSmall` (this file) → `sliceBoundSmall_of_cap` (lap 106) →
`dampedSeriesBoundSmall_of_sliceBound` (lap 102) → `shiftedMertensSmall_of_dampedSeriesBound`. -/
theorem exists_shiftedMertensSmall :
    ∃ K : ℝ, NormalNumbers.ElliottArchBands.ShiftedMertensSmall K := by
  obtain ⟨K, hK0, hcap⟩ := exists_sliceCapSmall
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hK1 : (0 : ℝ) ≤ K + (Real.log 4 + 4) := by linarith
  exact ⟨_, shiftedMertensSmall_of_dampedSeriesBound
    (dampedSeriesBoundSmall_of_sliceBound hK1 (sliceBoundSmall_of_cap hK0 hcap))⟩

/-- **THE CONSUMER, ON THREE INPUTS.**  With (c′-I) proved, `TwoPointElliottLog` rests on exactly
three named classical `Prop`s:

| input | depth |
|---|---|
| `ElliottCharRigidity.PrimeDensityAP A` | Mertens in progressions — reachable from the in-repo `G4MertensAP.mertensRate_residueClass` |
| `ElliottArchBands.ArchCorrModerate K₁` | de la Vallée Poussin — reachable from the in-repo `PNTPort.ZetaBounds.LogDerivZetaBndUnif99` |
| `ElliottArchBands.ArchCorrNearMaxHeight A ν η₂ K₂` | **Vinogradov–Korobov**, near-maximal height only | -/
theorem twoPointElliottLog_of_two_bands {b p q : ℕ} {t : ℝ} {K₁ K₂ ν η₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂) (hη₂1 : η₂ ≤ 1)
    (hdens : ∀ A : ℕ, NormalNumbers.ElliottCharRigidity.PrimeDensityAP A)
    (hmod : NormalNumbers.ElliottArchBands.ArchCorrModerate K₁)
    (hmax : ∀ A : ℕ, NormalNumbers.ElliottArchBands.ArchCorrNearMaxHeight A ν η₂ K₂) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t := by
  obtain ⟨K₀, hsmall⟩ := exists_shiftedMertensSmall
  exact NormalNumbers.ElliottArchBands.twoPointElliottLog_of_three_bands
    hp hq hpq hu hν hν1 hη₂ hη₂1 hdens hsmall hmod hmax

end

end NormalNumbers.ElliottSliceCap
