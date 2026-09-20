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
  have hP : 0 < primorial y := primorial_pos y
  unfold omegaLe
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hdvd, -⟩, hpy⟩
    have hpP : p ∣ primorial y := hp.dvd_primorial_iff.2 hpy
    refine ⟨⟨hp, ?_, hm⟩, hpy⟩
    have := Nat.dvd_sub hdvd hpP
    simpa using this
  · rintro ⟨⟨hp, hdvd, -⟩, hpy⟩
    have hpP : p ∣ primorial y := hp.dvd_primorial_iff.2 hpy
    exact ⟨⟨hp, hdvd.add hpP, by omega⟩, hpy⟩

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
  obtain ⟨c, B, C, hcB, hlaw⟩ := hL
  set j₀ : ℕ := h.natAbs + 1 with hj₀def
  have hj₀1 : 1 ≤ j₀ := by omega
  have hnotint : ¬ ∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j₀ = m := by
    rintro ⟨m, hm⟩
    have h4 : ((4 : ℝ) ^ j₀) ≠ 0 := by positivity
    have hR : (h : ℝ) = (m : ℝ) * (4 : ℝ) ^ j₀ := by field_simp at hm; linarith [hm]
    have hZ : h = m * 4 ^ j₀ := by exact_mod_cast hR
    have hm0 : m ≠ 0 := by rintro rfl; simp at hZ; exact hh hZ
    have hlb : (4 : ℤ) ^ j₀ ≤ |h| := by
      rw [hZ, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 4 ^ j₀)]
      have : 1 ≤ |m| := Int.one_le_abs (by omega)
      nlinarith [abs_nonneg m, (by positivity : (0 : ℤ) < 4 ^ j₀)]
    have hub : h.natAbs < 4 ^ j₀ := by
      calc h.natAbs < 2 ^ h.natAbs := Nat.lt_two_pow_self
        _ ≤ 4 ^ (h.natAbs + 1) := by
            calc 2 ^ h.natAbs ≤ 4 ^ h.natAbs := Nat.pow_le_pow_left (by norm_num) _
              _ ≤ 4 ^ (h.natAbs + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have habs : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have : ((4 : ℤ) ^ j₀) ≤ (h.natAbs : ℤ) := by rw [habs] at hlb; exact hlb
    have hub' : ((h.natAbs : ℤ)) < 4 ^ j₀ := by exact_mod_cast hub
    omega
  have hsite := hSite h j₀ hj₀1 hnotint
  have hBnn : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hcB 0)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
    (g := fun N => (B + |C|) * ‖fullSiteMean N h j₀‖) ?_ (by simpa using hsite.const_mul (B + |C|))
  filter_upwards [hlaw, tendsto_windowJ.eventually_ge_atTop j₀, eventually_ge_atTop 3]
    with N hN hNJ hN3
  set J := windowJ N with hJ
  set P : ℝ := ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖ with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun j _ => norm_nonneg _)
  have hmem : j₀ ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨hj₀1, hNJ⟩
  have hPle : P ≤ ‖fullSiteMean N h j₀‖ := by
    rw [hP, ← Finset.prod_erase_mul _ _ hmem]
    have h1 : (∏ j ∈ (Finset.Icc 1 J).erase j₀, ‖fullSiteMean N h j‖) ≤ 1 :=
      Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => norm_fullSiteMean_le_one _ _ _)
    nlinarith [norm_nonneg (fullSiteMean N h j₀),
      Finset.prod_nonneg (fun j (_ : j ∈ (Finset.Icc 1 J).erase j₀) => norm_nonneg
        (fullSiteMean N h j))]
  have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hCbound : C / Real.log N ≤ |C| := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [le_abs_self C, abs_nonneg C]
  have hprodnorm : ‖c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖ ≤ B * P := by
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hcB J) le_rfl hPnn hBnn
  calc ‖fullWindowMean N J h‖
      ≤ ‖fullWindowMean N J h - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖
          + ‖c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖ := by
        simpa using norm_add_le (fullWindowMean N J h
          - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j)
          (c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j)
    _ ≤ C / Real.log N * P + B * P := by gcongr
    _ ≤ |C| * P + B * P := by nlinarith
    _ = (B + |C|) * P := by ring
    _ ≤ (B + |C|) * ‖fullSiteMean N h j₀‖ := by
        have : (0 : ℝ) ≤ B + |C| := by positivity
        nlinarith

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
  set A : ℂ := ∑ n ∈ Finset.range P, F n with hA
  -- every block of `P` consecutive values sums to `A`
  have hblock : ∀ a : ℕ, ∑ n ∈ Finset.Ico a (a + P), F n = A := by
    intro a
    induction a with
    | zero => rw [hA, Finset.range_eq_Ico, Nat.zero_add]
    | succ a ih =>
        have h1 : ∑ n ∈ Finset.Ico a (a + 1 + P), F n
            = F a + ∑ n ∈ Finset.Ico (a + 1) (a + 1 + P), F n :=
          Finset.sum_eq_sum_Ico_succ_bot (by omega) _
        have h2 : ∑ n ∈ Finset.Ico a (a + 1 + P), F n
            = (∑ n ∈ Finset.Ico a (a + P), F n) + F (a + P) := by
          rw [show a + 1 + P = (a + P) + 1 from by omega]
          exact Finset.sum_Ico_succ_top (by omega) _
        have h3 : F (a + P) = F a := hper a
        rw [ih] at h2
        rw [h3] at h2
        rw [h1] at h2
        have : ∑ n ∈ Finset.Ico (a + 1) (a + 1 + P), F n = A := by
          have := h2
          linear_combination (norm := ring_nf) this
        simpa using this
  -- `k` full blocks starting at `N`
  set k : ℕ := N / P with hk
  set s : ℕ := N % P with hs
  have hNks : N = k * P + s := by
    rw [hk, hs, mul_comm]; exact (Nat.div_add_mod N P).symm
  have hsP : s < P := Nat.mod_lt _ hP
  have hfull : ∀ j : ℕ, ∑ n ∈ Finset.Ico N (N + j * P), F n = (j : ℂ) * A := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show N + (j + 1) * P = (N + j * P) + P from by ring,
          ← Finset.sum_Ico_consecutive F (Nat.le_add_right N (j * P))
            (Nat.le_add_right (N + j * P) P), ih, hblock]
        push_cast
        ring
  have hsplit2 : ∑ n ∈ Finset.Ico N (2 * N), F n
      = (k : ℂ) * A + ∑ n ∈ Finset.Ico (N + k * P) (2 * N), F n := by
    rw [← hfull k]
    rw [← Finset.sum_Ico_consecutive F (by omega : N ≤ N + k * P) (by omega : N + k * P ≤ 2 * N)]
  set R : ℂ := ∑ n ∈ Finset.Ico (N + k * P) (2 * N), F n with hR
  have hRle : ‖R‖ ≤ (s : ℝ) := by
    have hcard : (Finset.Ico (N + k * P) (2 * N)).card = s := by
      rw [Nat.card_Ico]; omega
    calc ‖R‖ ≤ ∑ n ∈ Finset.Ico (N + k * P) (2 * N), ‖F n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ico (N + k * P) (2 * N), (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => hb n)
      _ = (s : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  have hAle : ‖A‖ ≤ (P : ℝ) := by
    calc ‖A‖ ≤ ∑ n ∈ Finset.range P, ‖F n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range P, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hb n)
      _ = (P : ℝ) := by simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hkey : (∑ n ∈ Finset.Ico N (2 * N), F n) / N - A / P
      = A * (((k : ℝ) * P - N : ℝ) : ℂ) / ((N : ℂ) * P) + R / N := by
    rw [hsplit2]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    field_simp
    push_cast
    ring
  have hkPN : |(k : ℝ) * P - N| ≤ (P : ℝ) := by
    have : (N : ℝ) = (k : ℝ) * P + s := by exact_mod_cast hNks
    rw [this]
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hsP' : (s : ℝ) ≤ (P : ℝ) := by exact_mod_cast hsP.le
    rw [abs_le]; constructor <;> linarith
  have hsP' : (s : ℝ) ≤ (P : ℝ) := by exact_mod_cast hsP.le
  rw [hkey]
  have h1 : ‖A * (((k : ℝ) * P - N : ℝ) : ℂ) / ((N : ℂ) * P)‖ ≤ (P : ℝ) / N := by
    rw [norm_div, norm_mul, norm_mul]
    rw [Complex.norm_real, Complex.norm_natCast, Complex.norm_natCast, Real.norm_eq_abs]
    rw [div_le_div_iff₀ (by positivity) hNR]
    have hstep : ‖A‖ * |(k : ℝ) * P - N| ≤ (P : ℝ) * P :=
      mul_le_mul hAle hkPN (abs_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hstep hNR.le]
  have h2 : ‖R / (N : ℂ)‖ ≤ (P : ℝ) / N := by
    rw [norm_div, Complex.norm_natCast, div_le_div_iff₀ hNR hNR]
    nlinarith [hRle, hsP', hNR.le]
  calc ‖A * (((k : ℝ) * P - N : ℝ) : ℂ) / ((N : ℂ) * P) + R / N‖
      ≤ ‖A * (((k : ℝ) * P - N : ℝ) : ℂ) / ((N : ℂ) * P)‖ + ‖R / (N : ℂ)‖ := norm_add_le _ _
    _ ≤ (P : ℝ) / N + (P : ℝ) / N := by linarith
    _ = 2 * P / N := by ring

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
