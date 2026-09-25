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

end

end NormalNumbers.ElliottZetaPole
