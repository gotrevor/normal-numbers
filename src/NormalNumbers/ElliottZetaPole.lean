import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The pole-local bound on `ζ'/ζ` (lap 107)

Lap 106 reduced both Archimedean inputs to their **cap clause** (`ElliottDamped.SliceCapSmall`),
i.e. to a bound `‖slice‖ ≤ C·T⁻¹ + K` on the short band `w ≤ T = max(|v|, δ)`.  Because the band has
length `T`, the *coefficient* `C` there is harmless (it contributes `C` to the integral, not to the
main term `log(1/T)`), so what is needed is

  `‖ζ'/ζ(s)‖ ≤ C/|s − 1| + K`  on  `1 < Re s ≤ 2`, `|Im s| ≤ 1`.

This file proves the pole-local half of that, and **it needs no zero-free region**: near `s = 1` the
pole of `ζ` *is* the bound.  Concretely `G := update (s ↦ (s−1)ζ(s)) 1 1` is analytic at `1` with
`G(1) = 1` (Riemann's removable singularity theorem applied to `riemannZeta_residue_one`), so on a
small closed ball `G ≠ 0`, `logDeriv G` is continuous, hence bounded by compactness, and
`logDeriv ζ = logDeriv G − 1/(s−1)` there.

The remaining region `|s − 1| ≥ r` is compact with `ζ ≠ 0` (`riemannZeta_ne_zero_of_one_le_re`) and
`ζ` analytic, so `ζ'/ζ` is bounded there too — that is the next lap.
-/

open Filter Topology Set

namespace NormalNumbers.ElliottZetaPole

noncomputable section

/-- `(s−1)·ζ(s)`, with the removable singularity at `s = 1` filled in by its limit `1`. -/
noncomputable def zetaG : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

theorem zetaG_one : zetaG 1 = 1 := by simp [zetaG]

theorem zetaG_of_ne {s : ℂ} (hs : s ≠ 1) : zetaG s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

/-- `zetaG` is analytic at `1`: Riemann's removable singularity theorem. -/
theorem analyticAt_zetaG : AnalyticAt ℂ zetaG 1 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 1 := hz
    have hdiff : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * riemannZeta s) z :=
      ((differentiable_id.sub_const 1).differentiableAt).mul (differentiableAt_riemannZeta hz')
    refine hdiff.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz'] with y hy
    exact zetaG_of_ne hy
  · exact continuousAt_update_same.mpr riemannZeta_residue_one

/-- `zetaG` is differentiable at every `s ≠ 1`. -/
theorem differentiableAt_zetaG {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaG s := by
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * riemannZeta z) s :=
    ((differentiable_id.sub_const 1).differentiableAt).mul (differentiableAt_riemannZeta hs)
  refine hdiff.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hs] with y hy
  exact zetaG_of_ne hy

/-- **The logarithmic derivative splits off the pole.**  For `s ≠ 1` with `ζ(s) ≠ 0`,
`ζ'/ζ(s) = (G'/G)(s) − 1/(s−1)`. -/
theorem logDeriv_riemannZeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv zetaG s - 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
  have hG : zetaG s ≠ 0 := by
    rw [zetaG_of_ne hs]; exact mul_ne_zero hs1 hz
  have hdG : DifferentiableAt ℂ zetaG s := differentiableAt_zetaG hs
  have hdid : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    (differentiable_id.sub_const 1).differentiableAt
  have hquot : logDeriv (fun z : ℂ => zetaG z / (z - 1)) s
      = logDeriv zetaG s - logDeriv (fun z : ℂ => z - 1) s :=
    logDeriv_div s hG hs1 hdG hdid
  have heq : riemannZeta =ᶠ[𝓝 s] (fun z : ℂ => zetaG z / (z - 1)) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with y hy
    rw [zetaG_of_ne hy]
    have : y - 1 ≠ 0 := sub_ne_zero_of_ne hy
    field_simp
  have hcongr : logDeriv riemannZeta s = logDeriv (fun z : ℂ => zetaG z / (z - 1)) s :=
    (logDeriv_congr_nhds heq).self_of_nhds
  have hid : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    have : deriv (fun z : ℂ => z - 1) s = 1 := by
      simp
    rw [this]
  rw [hcongr, hquot, hid]

/-- **THE POLE-LOCAL BOUND.**  On a punctured ball around `1` — with no zero-free region, no
compactness at height, nothing but Riemann's removable singularity theorem —

  `ζ(s) ≠ 0`  and  `‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K`.

The `1/‖s−1‖` is the pole itself, with coefficient exactly `1`; `K` bounds `logDeriv G`, which is
continuous on the ball because `G` is analytic and non-vanishing there. -/
theorem exists_pole_local_bound :
    ∃ r > 0, ∃ K > 0, ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ ≤ r →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ 1 / ‖s - 1‖ + K := by
  have h1 : ∀ᶠ z in 𝓝 (1 : ℂ), AnalyticAt ℂ zetaG z := analyticAt_zetaG.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 (1 : ℂ), zetaG z ≠ 0 := by
    refine analyticAt_zetaG.continuousAt.eventually_ne ?_
    rw [zetaG_one]; exact one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hmem : ∀ z : ℂ, ‖z - 1‖ ≤ r → AnalyticAt ℂ zetaG z ∧ zetaG z ≠ 0 := by
    intro z hz
    refine hball ?_
    rw [dist_eq_norm]
    calc ‖z - 1‖ ≤ r := hz
      _ < ε := by rw [hr]; linarith
  have hcont : ContinuousOn (logDeriv zetaG) (Metric.closedBall (1 : ℂ) r) := by
    intro z hz
    have hz' : ‖z - 1‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    obtain ⟨hanal, hne⟩ := hmem z hz'
    refine ContinuousAt.continuousWithinAt ?_
    have hd : ContinuousAt (deriv zetaG) z := hanal.deriv.continuousAt
    exact hd.div hanal.continuousAt hne
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (1 : ℂ) r).exists_bound_of_continuousOn hcont
  refine ⟨r, hr0, K₀ + 1, by linarith [norm_nonneg (logDeriv zetaG 1), hK₀ 1 (by simp [hr0.le])],
    ?_⟩
  intro s hs hsr
  obtain ⟨hanal, hne⟩ := hmem s hsr
  have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
  have hz : riemannZeta s ≠ 0 := by
    intro h
    rw [zetaG_of_ne hs, h, mul_zero] at hne
    exact hne rfl
  refine ⟨hz, ?_⟩
  have hsplit := logDeriv_riemannZeta_eq hs hz
  have hbound : ‖logDeriv zetaG s‖ ≤ K₀ := by
    refine hK₀ s ?_
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hsr
  calc ‖logDeriv riemannZeta s‖ = ‖logDeriv zetaG s - 1 / (s - 1)‖ := by rw [hsplit]
    _ ≤ ‖logDeriv zetaG s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ K₀ + 1 / ‖s - 1‖ := by
        have : ‖1 / (s - 1)‖ = 1 / ‖s - 1‖ := by rw [norm_div, norm_one]
        linarith
    _ ≤ 1 / ‖s - 1‖ + (K₀ + 1) := by linarith

/-! ### The far band: compactness plus `ζ(1+it) ≠ 0` -/

/-- **THE FAR BAND.**  On the compact region `1 ≤ Re s ≤ 2`, `|Im s| ≤ 1`, `‖s−1‖ ≥ r` the
logarithmic derivative is bounded outright: `ζ` is analytic there (`s ≠ 1`) and non-vanishing
(`riemannZeta_ne_zero_of_one_le_re` — *this* is where the non-vanishing on the `1`-line enters, and
only away from `t = 0`). -/
theorem exists_far_band_bound {r : ℝ} (hr : 0 < r) :
    ∃ K > 0, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → r ≤ ‖s - 1‖ →
      ‖logDeriv riemannZeta s‖ ≤ K := by
  set S : Set ℂ := {s | 1 ≤ s.re} ∩ ({s | s.re ≤ 2} ∩ ({s | |s.im| ≤ 1} ∩ {s | r ≤ ‖s - 1‖}))
    with hS
  have hclosed : IsClosed S := by
    rw [hS]
    refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
    refine (isClosed_le (Complex.continuous_im.abs) continuous_const).inter ?_
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 4)).subset ?_
    intro s hs
    obtain ⟨h1, h2, h3, -⟩ := hs
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    have hre : |s.re| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
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

/-- **(c′-I)'s ANALYTIC SIDE, COMPLETE ON THE SUB-UNIT BAND.**  `‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K` for every
`s ≠ 1` with `1 ≤ Re s ≤ 2` and `|Im s| ≤ 1`, together with `ζ(s) ≠ 0`.  The pole supplies the
`1/‖s−1‖` near `1` (lap 107, no zeros needed); compactness plus non-vanishing on the `1`-line
supplies the constant elsewhere. -/
theorem exists_subunit_logDeriv_bound :
    ∃ K > 0, ∀ s : ℂ, s ≠ 1 → 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ 1 / ‖s - 1‖ + K := by
  obtain ⟨r, hr, K₁, hK₁, hpole⟩ := exists_pole_local_bound
  obtain ⟨K₂, hK₂, hfar⟩ := exists_far_band_bound hr
  refine ⟨max K₁ K₂, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro s hs h1 h2 h3
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
  refine ⟨hz, ?_⟩
  rcases le_or_gt ‖s - 1‖ r with hle | hgt
  · have := (hpole s hs hle).2
    have : ‖logDeriv riemannZeta s‖ ≤ 1 / ‖s - 1‖ + K₁ := this
    have hmax : K₁ ≤ max K₁ K₂ := le_max_left _ _
    linarith
  · have hbound := hfar s h1 h2 h3 hgt.le
    have hnn : 0 ≤ 1 / ‖s - 1‖ := by positivity
    have hmax : K₂ ≤ max K₁ K₂ := le_max_right _ _
    linarith

end

end NormalNumbers.ElliottZetaPole
