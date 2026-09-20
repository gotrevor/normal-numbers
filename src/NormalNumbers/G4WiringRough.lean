import NormalNumbers.G4WiringCRT
import Mathlib.NumberTheory.Primorial

/-!
# N1 split: smooth (CRT, elementary) × rough (`RoughIndependence`, the crux)

`KICKOFF-2026-09-20-rough-independence-lap.md`.  After stripping the primes `p ≤ y` from `ω`, the
window mean factorises into the product of its site means up to a bounded constant with error
`≍ 1/(y log N)` (blueprint probe 6).  That is the frozen node `RoughIndependence`; the small-prime
part is genuinely elementary (periodicity mod `primorial y` + a boundary-block estimate) and is
proved here.

Frozen Props, never proved in this file: `RoughIndependence`, `SmoothRoughDecoupling`,
`SmoothNonvanishing`.
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4

open NormalNumbers.PrimeLambert

/-! ### Leaf 1: the smooth/rough split of `ω` -/

/-- Distinct prime divisors of `m` that exceed `y` (the `y`-rough part of `ω`). -/
def omegaAbove (y m : ℕ) : ℕ := (m.primeFactors.filter (fun p => y < p)).card
/-- Distinct prime divisors of `m` that are `≤ y` (the `y`-smooth part of `ω`). -/
def omegaLe (y m : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ y)).card

theorem omegaR_eq_omegaLe_add_omegaAbove (y m : ℕ) :
    omegaR m = (omegaLe y m : ℝ) + omegaAbove y m := by
  have h := Finset.card_filter_add_card_filter_not (s := m.primeFactors) (p := fun p => p ≤ y)
  have h' : omegaLe y m + omegaAbove y m = m.primeFactors.card := by
    rw [omegaLe, omegaAbove]
    refine Eq.trans ?_ h
    congr 1
    exact Finset.card_nbij id (by intro a ha; simpa using by simpa using ha)
      (fun a _ b _ hab => hab) (by
        intro a ha
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ⊢
        exact ⟨a, ⟨ha.1, by omega⟩, rfl⟩)
  rw [omegaR_eq, ← h']
  push_cast
  ring

/-- `ω_{≤y}(m)` is `primorial y`-periodic for `m ≠ 0`.

⚠️ The kickoff's verbatim form (no hypothesis on `m`) is **false** at `m = 0`: `primeFactors 0 = ∅`
so `omegaLe y 0 = 0`, while `omegaLe y (primorial y) = #{p ≤ y prime} > 0` for `y ≥ 2`.  Every use
site has `m = n + j + 1 ≥ 1`, so the hypothesis costs nothing. -/
theorem omegaLe_add_primorial (y m : ℕ) (hm : m ≠ 0) :
    omegaLe y (m + primorial y) = omegaLe y m := by
  sorry

noncomputable def smoothTail (y J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (omegaLe y (n + j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)
noncomputable def roughTail (y J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (omegaAbove y (n + j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)

theorem truncTail_eq_smooth_add_rough (y J n : ℕ) :
    truncTail J n = smoothTail y J n + roughTail y J n := by
  rw [truncTail, smoothTail, roughTail, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [omegaR_eq_omegaLe_add_omegaAbove y (n + j + 1)]
  ring

theorem ePhase_truncTail_factor (y J n : ℕ) (h : ℤ) :
    ePhase (h * truncTail J n) = ePhase (h * smoothTail y J n) * ePhase (h * roughTail y J n) := by
  rw [truncTail_eq_smooth_add_rough y J n, mul_add, ePhase_add]

theorem smoothTail_add_primorial (y J n : ℕ) :
    smoothTail y J (n + primorial y) = smoothTail y J n := by
  rw [smoothTail, smoothTail]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 2
  rw [show n + primorial y + j + 1 = (n + j + 1) + primorial y from by ring]
  exact omegaLe_add_primorial y (n + j + 1) (by omega)

/-! ### The smooth / rough means -/

noncomputable def smoothWindowMean (N J : ℕ) (h : ℤ) (y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * smoothTail y J n)) / N
noncomputable def roughWindowMean (N J : ℕ) (h : ℤ) (y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * roughTail y J n)) / N
noncomputable def smoothSiteMean (N : ℕ) (h : ℤ) (j y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)) / N
noncomputable def roughSiteMean (N : ℕ) (h : ℤ) (j y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaAbove y (n + j) / (4 : ℝ) ^ j)) / N

/-! ### Leaf 2: the schedule form of `CRTConstant` -/

/-- Schedule form of `CRTConstant`: the law only along `J = windowJ N`. -/
def CRTConstantSched (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C : ℝ), (∀ J, ‖c J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
    ‖fullWindowMean N (windowJ N) h - c (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), fullSiteMean N h j‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖

theorem crtConstantSched_of_crtConstant {h : ℤ} (hL : CRTConstant h) : CRTConstantSched h := by
  obtain ⟨c, B, C, hcB, hlaw⟩ := hL
  exact ⟨c, B, C, hcB, hlaw.mono (fun N hN => hN (windowJ N))⟩

theorem fullWindowMean_tendsto_zero_of_sched {h : ℤ} (hL : CRTConstantSched h)
    (hSite : SiteDecayFull) (hh : h ≠ 0) :
    Tendsto (fun N => fullWindowMean N (windowJ N) h) atTop (𝓝 0) := by
  sorry

/-! ### The frozen nodes -/

/-- **Frozen node N1b** (blueprint probe 6, 2026-09-20). -/
def RoughIndependence (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℕ → ℂ) (B C : ℝ), (∀ y J, ‖c y J‖ ≤ B) ∧ ∀ y : ℕ, 2 ≤ y → ∀ᶠ N : ℕ in atTop,
    ‖roughWindowMean N (windowJ N) h y
        - c y (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), roughSiteMean N h j y‖
      ≤ C / ((y : ℝ) * Real.log N) * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖roughSiteMean N h j y‖

/-- **Frozen node N1a′**: decoupling of the periodic small-prime phase from the rough phase. -/
def SmoothRoughDecoupling (h : ℤ) : Prop :=
  ∃ C : ℝ, ∀ y : ℕ, 2 ≤ y → ∀ᶠ N : ℕ in atTop,
    ‖fullWindowMean N (windowJ N) h - smoothWindowMean N (windowJ N) h y * roughWindowMean N (windowJ N) h y‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖ ∧
    ‖(∏ j ∈ Finset.Icc 1 (windowJ N), fullSiteMean N h j)
        - (∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y)
          * ∏ j ∈ Finset.Icc 1 (windowJ N), roughSiteMean N h j y‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖

/-- **Frozen, elementary** (N1a): the product of smooth site means is bounded below. -/
def SmoothNonvanishing (h : ℤ) : Prop :=
  ∀ y : ℕ, 2 ≤ y → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
    δ ≤ ∏ j ∈ Finset.Icc 1 (windowJ N), ‖smoothSiteMean N h j y‖

/-! ### Leaf 3: periodic means -/

/-- The average over `[N, 2N)` of a `P`-periodic function bounded by `1` is within `2P/N` of its
average over one period. -/
theorem periodic_mean_close (F : ℕ → ℂ) (P : ℕ) (hP : 0 < P) (hper : ∀ n, F (n + P) = F n)
    (hb : ∀ n, ‖F n‖ ≤ 1) (N : ℕ) (hN : 0 < N) :
    ‖(∑ n ∈ Finset.Ico N (2 * N), F n) / N - (∑ n ∈ Finset.range P, F n) / P‖ ≤ 2 * P / N := by
  sorry

/-! ### Leaf 4: N1a proper -/

theorem smoothWindowCRT (h : ℤ) (y : ℕ) (hy : 2 ≤ y) (hS : SmoothNonvanishing h) :
    ∃ (c' : ℕ → ℂ) (B : ℝ), (∀ J, ‖c' J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
      ‖smoothWindowMean N (windowJ N) h y
          - c' (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y‖
        ≤ B * (windowJ N : ℝ) * primorial y / N := by
  sorry

/-! ### Leaf 5–6: the wiring -/

/-- **Wiring**: N1 (schedule form) from N1a + N1a′ + N1b. -/
theorem crtConstantSched_of_rough {h : ℤ} (hR : RoughIndependence h) (hD : SmoothRoughDecoupling h)
    (hS : SmoothNonvanishing h) : CRTConstantSched h := by
  sorry

theorem isNormal_G4_of_rough
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h →
      RoughIndependence h ∧ SmoothRoughDecoupling h ∧ SmoothNonvanishing h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) := by
  refine isNormal_G4_of_windowDecay (fun h hh => ?_)
  by_cases hc : ChowlaSector h
  · exact hCh h hh hc
  · obtain ⟨hR, hD, hS⟩ := hSD h hh hc
    exact fullWindowMean_tendsto_zero_of_sched (crtConstantSched_of_rough hR hD hS) hSite hh

end NormalNumbers.G4
