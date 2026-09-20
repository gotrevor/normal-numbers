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

/-- The single-`y` form of N1a.  `SmoothNonvanishing h` is definitionally
`∀ y ≥ 2, SmoothNonvanishingAt h y`, so `hS y hy : SmoothNonvanishingAt h y` for `hS` of the
frozen type.  The wiring only ever consumes `y = 2`, and at `y = 2` the node is *proved* below
(`smoothNonvanishingAt_two`), off the Chowla sector. -/
def SmoothNonvanishingAt (h : ℤ) (y : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
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

/-! ### Helpers for leaf 4 -/

/-- Telescoping product estimate: two products of unit-bounded factors differ by at most
`card · ε` if the factors differ by at most `ε`. -/
theorem norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ ε) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ s.card * ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hfg' : ∀ i ∈ s, ‖f i - g i‖ ≤ ε := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
      have hrec := ih hf' hg' hfg'
      have hma : a ∈ insert a s := Finset.mem_insert_self a s
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hid : f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i
          = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
      have hgs : ‖∏ i ∈ s, g i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
      have hcard : ((insert a s).card : ℝ) = s.card + 1 := by
        rw [Finset.card_insert_of_notMem ha]; push_cast; ring
      rw [hid, hcard]
      calc ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i‖
          ≤ ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ + ‖(f a - g a) * ∏ i ∈ s, g i‖ :=
            norm_add_le _ _
        _ = ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ + ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * ((s.card : ℝ) * ε) + ε * 1 := by
            gcongr
            · exact hf a hma
            · exact hfg a hma
        _ = ((s.card : ℝ) + 1) * ε := by ring

/-- `windowJ N / N → 0`: the schedule is `log₂ log₂ N`, far smaller than `N`. -/
theorem windowJ_div_tendsto_zero : Tendsto (fun N : ℕ => (windowJ N : ℝ) / N) atTop (𝓝 0) := by
  have hsq : ∀ L : ℕ, 4 ≤ L → L ^ 2 ≤ 2 ^ L := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ L hL ih =>
        have h1 : 2 * L + 1 ≤ L ^ 2 := by nlinarith
        have : (L + 1) ^ 2 = L ^ 2 + (2 * L + 1) := by ring
        calc (L + 1) ^ 2 = L ^ 2 + (2 * L + 1) := this
          _ ≤ 2 ^ L + 2 ^ L := by omega
          _ = 2 ^ (L + 1) := by ring
  have hlog : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨2 ^ b, fun a ha => Nat.le_log_of_pow_le (by norm_num) ha⟩)
  have hgtends : Tendsto (fun L : ℕ => 1 / (L : ℝ)) atTop (𝓝 0) := by
    have hL : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds hL
  refine squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ (hgtends.comp hlog)
  filter_upwards [eventually_ge_atTop 16] with N hN
  set L := Nat.log 2 N with hLdef
  have hL4 : 4 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 4 ≤ N)
  have hJle : windowJ N ≤ L := by
    have : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
    simpa [windowJ, ← hLdef] using this
  have hpow : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hLN : L ^ 2 ≤ N := le_trans (hsq L hL4) hpow
  have hLR : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hJR : (windowJ N : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJle
  have hLNR : ((L : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hLN
  have hNR : (0 : ℝ) < N := by positivity
  show (windowJ N : ℝ) / N ≤ 1 / (L : ℝ)
  rw [div_le_div_iff₀ hNR (by linarith)]
  nlinarith [hJR, hLNR, hLR]

/-- `windowJ N · log N / N → 0`: the schedule is `log₂ log₂ N`, so even against a factor `log N`
it is `o(N)`.  (`L³ ≤ 2^L ≤ N` and `log N ≤ L + 1`, with `L = log₂ N`.) -/
theorem windowJ_log_div_tendsto_zero :
    Tendsto (fun N : ℕ => (windowJ N : ℝ) * Real.log N / N) atTop (𝓝 0) := by
  have hcube : ∀ L : ℕ, 10 ≤ L → L ^ 3 ≤ 2 ^ L := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ L hL ih =>
        have h1 : 3 * L ^ 2 + 3 * L + 1 ≤ L ^ 3 := by nlinarith
        calc (L + 1) ^ 3 = L ^ 3 + (3 * L ^ 2 + 3 * L + 1) := by ring
          _ ≤ 2 ^ L + 2 ^ L := by omega
          _ = 2 ^ (L + 1) := by ring
  have hlog : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨2 ^ b, fun a ha => Nat.le_log_of_pow_le (by norm_num) ha⟩)
  have hgtends : Tendsto (fun L : ℕ => 2 / (L : ℝ)) atTop (𝓝 0) := by
    have hL : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds hL
  refine squeeze_zero' ?_ ?_ (hgtends.comp hlog)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg h1
    positivity
  filter_upwards [eventually_ge_atTop 1024] with N hN
  set L := Nat.log 2 N with hLdef
  have hL10 : 10 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 10 ≤ N)
  have hJle : windowJ N ≤ L := by
    have : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
    simpa [windowJ, ← hLdef] using this
  have hpow : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hLN : L ^ 3 ≤ N := le_trans (hcube L hL10) hpow
  have hN1024 : (1024 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by linarith
  have hLR : (10 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL10
  have hJR : (windowJ N : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJle
  have hLNR : ((L : ℝ)) ^ 3 ≤ (N : ℝ) := by exact_mod_cast hLN
  have hlogle : Real.log N ≤ (L : ℝ) + 1 := by
    have hlt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hltR : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast hlt.le
    calc Real.log N ≤ Real.log ((2 : ℝ) ^ (L + 1)) := Real.log_le_log hNR hltR
      _ = ((L : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ ((L : ℝ) + 1) * 1 := by
          have := Real.log_two_lt_d9
          nlinarith [hLR]
      _ = (L : ℝ) + 1 := by ring
  have hlognn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL3 : (L : ℝ) ^ 2 * 10 ≤ (L : ℝ) ^ 3 := by nlinarith
  have hJnn : (0 : ℝ) ≤ (windowJ N : ℝ) := Nat.cast_nonneg _
  show (windowJ N : ℝ) * Real.log N / N ≤ 2 / (L : ℝ)
  rw [div_le_div_iff₀ hNR (by linarith)]
  have hstep : (windowJ N : ℝ) * Real.log N ≤ (L : ℝ) * ((L : ℝ) + 1) := by
    calc (windowJ N : ℝ) * Real.log N ≤ (L : ℝ) * Real.log N := by nlinarith
      _ ≤ (L : ℝ) * ((L : ℝ) + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hstep (show (0:ℝ) ≤ (L:ℝ) by linarith), hL3, hLNR, hLR]

/-! ### Norm bounds for the smooth / rough means -/

lemma norm_smoothSiteMean_le_one (N : ℕ) (h : ℤ) (j y : ℕ) : ‖smoothSiteMean N h j y‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [smoothSiteMean]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [smoothSiteMean, norm_div, Complex.norm_natCast, div_le_one hNR]
  calc ‖∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖
      ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖ :=
        norm_sum_le _ _
    _ = (N : ℝ) := by
        rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
          mul_one, Nat.card_Ico]
        congr 1
        omega

lemma norm_roughSiteMean_le_one (N : ℕ) (h : ℤ) (j y : ℕ) : ‖roughSiteMean N h j y‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [roughSiteMean]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [roughSiteMean, norm_div, Complex.norm_natCast, div_le_one hNR]
  calc ‖∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaAbove y (n + j) / (4 : ℝ) ^ j)‖
      ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖ePhase (h * omegaAbove y (n + j) / (4 : ℝ) ^ j)‖ :=
        norm_sum_le _ _
    _ = (N : ℝ) := by
        rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
          mul_one, Nat.card_Ico]
        congr 1
        omega

/-! ### Leaf 4: N1a proper -/

theorem smoothWindowCRT' (h : ℤ) (y : ℕ) (hy : 2 ≤ y) (hS : SmoothNonvanishingAt h y) :
    ∃ (c' : ℕ → ℂ) (B : ℝ), (∀ J, ‖c' J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
      ‖smoothWindowMean N (windowJ N) h y
          - c' (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y‖
        ≤ B * (windowJ N : ℝ) * primorial y / N := by
  classical
  obtain ⟨δ, hδ, hδN⟩ := hS
  set P : ℕ := primorial y with hPdef
  have hP : 0 < P := primorial_pos y
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  -- the two period averages (independent of `N`)
  set AW : ℕ → ℂ := fun J => (∑ n ∈ Finset.range P, ePhase (h * smoothTail y J n)) / P with hAW
  set Aj : ℕ → ℂ :=
    fun j => (∑ n ∈ Finset.range P, ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)) / P with hAj
  set c' : ℕ → ℂ := fun J =>
    if ‖∏ j ∈ Finset.Icc 1 J, Aj j‖ < δ / 2 then 0
    else AW J / ∏ j ∈ Finset.Icc 1 J, Aj j with hc'
  have hAWle : ∀ J, ‖AW J‖ ≤ 1 := by
    intro J
    rw [hAW]
    simp only
    rw [norm_div, Complex.norm_natCast, div_le_one hPR]
    calc ‖∑ n ∈ Finset.range P, ePhase (h * smoothTail y J n)‖
        ≤ ∑ n ∈ Finset.range P, ‖ePhase (h * smoothTail y J n)‖ := norm_sum_le _ _
      _ = (P : ℝ) := by
          rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
            mul_one, Finset.card_range]
  have hAjle : ∀ j, ‖Aj j‖ ≤ 1 := by
    intro j
    rw [hAj]
    simp only
    rw [norm_div, Complex.norm_natCast, div_le_one hPR]
    calc ‖∑ n ∈ Finset.range P, ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖
        ≤ ∑ n ∈ Finset.range P, ‖ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖ := norm_sum_le _ _
      _ = (P : ℝ) := by
          rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
            mul_one, Finset.card_range]
  have hSitele : ∀ (N : ℕ) (j : ℕ), ‖smoothSiteMean N h j y‖ ≤ 1 := by
    intro N j
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [smoothSiteMean]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [smoothSiteMean, norm_div, Complex.norm_natCast, div_le_one hNR]
    calc ‖∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖
        ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)‖ :=
          norm_sum_le _ _
      _ = (N : ℝ) := by
          rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
            mul_one, Nat.card_Ico]
          congr 1
          omega
  refine ⟨c', 2 + 4 / δ, ?_, ?_⟩
  · intro J
    rw [hc']
    simp only
    split_ifs with hlt
    · simp only [norm_zero]; positivity
    · push_neg at hlt
      rw [norm_div]
      have hden : δ / 2 ≤ ‖∏ j ∈ Finset.Icc 1 J, Aj j‖ := hlt
      have hden0 : (0 : ℝ) < ‖∏ j ∈ Finset.Icc 1 J, Aj j‖ := lt_of_lt_of_le (by linarith) hden
      rw [div_le_iff₀ hden0]
      have h1 : ‖AW J‖ ≤ 1 := hAWle J
      have hpos : (0 : ℝ) < 2 + 4 / δ := by positivity
      have hkey : (2 + 4 / δ) * (δ / 2) = δ + 2 := by field_simp; ring
      have hmul := mul_le_mul_of_nonneg_left hden hpos.le
      linarith
  · -- the eventual estimate
    have hsmall : ∀ᶠ N : ℕ in atTop, (windowJ N : ℝ) / N ≤ δ / (8 * P) := by
      have := windowJ_div_tendsto_zero
      have hpos : (0 : ℝ) < δ / (8 * P) := by positivity
      exact this.eventually (eventually_le_nhds hpos)
    filter_upwards [hδN, hsmall, eventually_gt_atTop 0] with N hδprod hNsmall hN0
    set J := windowJ N with hJdef
    clear_value J
    have hJ1 : 1 ≤ J := by rw [hJdef, windowJ]; omega
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
    -- window mean vs its period average
    have hW : ‖smoothWindowMean N J h y - AW J‖ ≤ 2 * P / N := by
      have := periodic_mean_close (fun n => ePhase (h * smoothTail y J n)) P hP
        (fun n => by rw [smoothTail_add_primorial]) (fun n => le_of_eq (norm_ePhase _)) N hN0
      simpa [smoothWindowMean, hAW] using this
    -- site means vs their period averages
    have hSj : ∀ j, 1 ≤ j → ‖smoothSiteMean N h j y - Aj j‖ ≤ 2 * P / N := by
      intro j hj
      have hper : ∀ n : ℕ, ePhase (h * omegaLe y (n + P + j) / (4 : ℝ) ^ j)
          = ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j) := by
        intro n
        have hEq : omegaLe y (n + P + j) = omegaLe y (n + j) := by
          rw [show n + P + j = (n + j) + P from by omega]
          exact omegaLe_add_primorial y (n + j) (by omega)
        rw [hEq]
      have := periodic_mean_close (fun n => ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)) P hP
        hper (fun n => le_of_eq (norm_ePhase _)) N hN0
      simpa [smoothSiteMean, hAj] using this
    have hεnn : (0 : ℝ) ≤ 2 * P / N := by positivity
    have hcard : (Finset.Icc 1 J).card = J := by rw [Nat.card_Icc]; omega
    have hprod : ‖(∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y) - ∏ j ∈ Finset.Icc 1 J, Aj j‖
        ≤ (J : ℝ) * (2 * P / N) := by
      have := norm_prod_sub_prod_le (Finset.Icc 1 J) (fun j => smoothSiteMean N h j y) Aj
        (2 * P / N) hεnn (fun j _ => hSitele N j) (fun j _ => hAjle j)
        (fun j hj => hSj j (Finset.mem_Icc.mp hj).1)
      rwa [hcard] at this
    -- the bound `J · 2P/N ≤ δ/2`
    have hJP : (J : ℝ) * (2 * P / N) ≤ δ / 2 := by
      have h1 : (J : ℝ) / N ≤ δ / (8 * P) := hNsmall
      have : (J : ℝ) * (2 * P / N) = 2 * P * ((J : ℝ) / N) := by field_simp
      rw [this]
      calc 2 * (P : ℝ) * ((J : ℝ) / N) ≤ 2 * P * (δ / (8 * P)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = δ / 4 := by field_simp; ring
        _ ≤ δ / 2 := by linarith
    -- so the product of period averages is bounded below and `c'` takes its "else" branch
    have hnormfull : δ ≤ ‖∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y‖ := by
      rw [norm_prod]; exact hδprod
    have hAjbig : δ / 2 ≤ ‖∏ j ∈ Finset.Icc 1 J, Aj j‖ := by
      have := norm_sub_norm_le (∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y)
        (∏ j ∈ Finset.Icc 1 J, Aj j)
      linarith [hprod, hnormfull, this]
    have hne : (∏ j ∈ Finset.Icc 1 J, Aj j) ≠ 0 := by
      intro hzero
      rw [hzero] at hAjbig
      simp at hAjbig
      linarith
    have hcval : c' J = AW J / ∏ j ∈ Finset.Icc 1 J, Aj j := by
      rw [hc']; simp only; rw [if_neg (by push_neg; exact hAjbig)]
    have hcmul : c' J * ∏ j ∈ Finset.Icc 1 J, Aj j = AW J := by
      rw [hcval]; field_simp
    have hcnorm : ‖c' J‖ ≤ 2 / δ := by
      rw [hcval, norm_div, div_le_div_iff₀ (by linarith [hAjbig] : (0:ℝ) < ‖∏ j ∈ Finset.Icc 1 J, Aj j‖) hδ]
      nlinarith [hAWle J, hAjbig]
    -- assemble
    have hdecomp : smoothWindowMean N J h y - c' J * ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y
        = (smoothWindowMean N J h y - AW J)
          + c' J * ((∏ j ∈ Finset.Icc 1 J, Aj j) - ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y) := by
      rw [mul_sub, hcmul]; ring
    have hJR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
    calc ‖smoothWindowMean N J h y - c' J * ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y‖
        ≤ ‖smoothWindowMean N J h y - AW J‖
            + ‖c' J * ((∏ j ∈ Finset.Icc 1 J, Aj j)
              - ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y)‖ := by
          rw [hdecomp]; exact norm_add_le _ _
      _ ≤ 2 * P / N + (2 / δ) * ((J : ℝ) * (2 * P / N)) := by
          refine add_le_add hW ?_
          · rw [norm_mul]
            have hnn : (0 : ℝ) ≤ ‖(∏ j ∈ Finset.Icc 1 J, Aj j)
                - ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y‖ := norm_nonneg _
            have hsymm : ‖(∏ j ∈ Finset.Icc 1 J, Aj j)
                - ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j y‖ ≤ (J : ℝ) * (2 * P / N) := by
              rw [← norm_neg]; simpa using hprod
            have h2δ : (0 : ℝ) ≤ 2 / δ := by positivity
            exact mul_le_mul hcnorm hsymm hnn h2δ
      _ ≤ (2 + 4 / δ) * (J : ℝ) * P / N := by
          have e2 : (2 / δ) * ((J : ℝ) * (2 * P / N)) = (4 / δ) * (J : ℝ) * P / N := by
            field_simp; ring
          have e1 : 2 * (P : ℝ) / N ≤ 2 * (J : ℝ) * P / N := by
            rw [div_le_div_iff₀ hNR hNR]
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hJR) hPR.le) hNR.le]
          have hfield : (2 + 4 / δ) * (J : ℝ) * P / N
              - (2 * P / N + (2 / δ) * ((J : ℝ) * (2 * P / N)))
              = 2 * ((J : ℝ) - 1) * P / N := by field_simp; ring
          have hnn : (0 : ℝ) ≤ 2 * ((J : ℝ) - 1) * P / N := by
            apply div_nonneg _ hNR.le
            nlinarith [hJR, hPR.le]
          linarith [hfield, hnn, e1, e2]

/-- The kickoff's form of N1a, now a corollary of the single-`y` one. -/
theorem smoothWindowCRT (h : ℤ) (y : ℕ) (hy : 2 ≤ y) (hS : SmoothNonvanishing h) :
    ∃ (c' : ℕ → ℂ) (B : ℝ), (∀ J, ‖c' J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
      ‖smoothWindowMean N (windowJ N) h y
          - c' (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y‖
        ≤ B * (windowJ N : ℝ) * primorial y / N :=
  smoothWindowCRT' h y hy (hS y hy)

/-! ### Leaf 5–6: the wiring -/

/-- The shape of `RoughIndependence` that the wiring actually consumes: a single `y`, and a
relative error `C / log N` with no `1/y` gain. -/
def RoughIndependenceAt (h : ℤ) (y : ℕ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C : ℝ), (∀ J, ‖c J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
    ‖roughWindowMean N (windowJ N) h y
        - c (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), roughSiteMean N h j y‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖roughSiteMean N h j y‖

theorem roughIndependenceAt_of_rough {h : ℤ} (hR : RoughIndependence h) {y : ℕ} (hy : 2 ≤ y) :
    RoughIndependenceAt h y := by
  obtain ⟨c, B, C, hcB, hev⟩ := hR
  have hy0 : (0 : ℝ) < y := by
    have : (2 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  refine ⟨c y, B, C / y, fun J => hcB y J, (hev y hy).mono (fun N hN => ?_)⟩
  have : C / ((y : ℝ) * Real.log N) = C / y / Real.log N := by
    rw [div_div]
  rwa [this] at hN

set_option maxHeartbeats 1000000 in
/-- **Wiring, sharpened**: N1 (schedule form) needs `RoughIndependence` only at the *single*
value `y = 2`, and only with a `C / log N` relative error — the `1/y` gain of the frozen node is
never used.  This is the honest shape of the open obligation. -/
theorem crtConstantSched_of_roughAt {h : ℤ} (hR : RoughIndependenceAt h 2)
    (hD : SmoothRoughDecoupling h) (hS : SmoothNonvanishingAt h 2) : CRTConstantSched h := by
  classical
  obtain ⟨cR, BR, CR, hcRB, hRev⟩ := hR
  obtain ⟨CD, hDev⟩ := hD
  obtain ⟨c', B', hc'B, h4ev⟩ := smoothWindowCRT' h 2 le_rfl hS
  obtain ⟨δ, hδ, hδev⟩ := hS
  set P₀ : ℕ := primorial 2 with hP₀
  have hP₀R : (0 : ℝ) < P₀ := by rw [hP₀]; exact_mod_cast primorial_pos 2
  clear_value P₀
  have hB'nn : (0 : ℝ) ≤ B' := le_trans (norm_nonneg _) (hc'B 0)
  have hBRnn : (0 : ℝ) ≤ BR := le_trans (norm_nonneg _) (hcRB 0)
  set κ : ℝ := (1 + |CD|) / δ with hκ
  have hκnn : (0 : ℝ) ≤ κ := by rw [hκ]; positivity
  refine ⟨fun J => c' J * cR J, B' * BR,
    |CD| + (BR + |CR|) * κ + B' * |CR| * κ + B' * BR * |CD|, ?_, ?_⟩
  · intro J
    rw [norm_mul]
    exact mul_le_mul (hc'B J) (hcRB J) (norm_nonneg _) hB'nn
  · -- the `J · P₀ / N` errors are `≤ 1 / log N` eventually
    have hsmall : ∀ᶠ N : ℕ in atTop,
        (B' * P₀ + 1) * ((windowJ N : ℝ) * Real.log N / N) ≤ 1 := by
      have hlim : Tendsto (fun N : ℕ => (B' * P₀ + 1) * ((windowJ N : ℝ) * Real.log N / N))
          atTop (𝓝 0) := by
        simpa using (windowJ_log_div_tendsto_zero).const_mul (B' * P₀ + 1)
      exact (hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).mono
        (fun N hN => hN.le)
    filter_upwards [hRev, hDev 2 le_rfl, hδev, h4ev, hsmall, eventually_ge_atTop 3]
      with N hRN hDN hδN h4N hsmallN hN3
    set J := windowJ N with hJdef
    clear_value J
    have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have hNR : (0 : ℝ) < N := by linarith
    have hlogN : (1 : ℝ) ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hlogpos : (0 : ℝ) < Real.log N := by linarith
    -- abbreviations
    set SW : ℂ := smoothWindowMean N J h 2 with hSW
    set RW : ℂ := roughWindowMean N J h 2 with hRW
    set PS : ℂ := ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j 2 with hPS
    set PR : ℂ := ∏ j ∈ Finset.Icc 1 J, roughSiteMean N h j 2 with hPR
    set Pf : ℂ := ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j with hPf
    set F : ℝ := ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖ with hF
    set K : ℝ := ∏ j ∈ Finset.Icc 1 J, ‖roughSiteMean N h j 2‖ with hK
    set Sn : ℝ := ∏ j ∈ Finset.Icc 1 J, ‖smoothSiteMean N h j 2‖ with hSn
    have hFnn : (0 : ℝ) ≤ F := Finset.prod_nonneg (fun j _ => norm_nonneg _)
    have hKnn : (0 : ℝ) ≤ K := Finset.prod_nonneg (fun j _ => norm_nonneg _)
    have hPfF : ‖Pf‖ = F := by rw [hPf, hF, norm_prod]
    have hPRK : ‖PR‖ = K := by rw [hPR, hK, norm_prod]
    have hPSSn : ‖PS‖ = Sn := by rw [hPS, hSn, norm_prod]
    have hSnle : Sn ≤ 1 :=
      Finset.prod_le_one (fun j _ => norm_nonneg _)
        (fun j _ => norm_smoothSiteMean_le_one _ _ _ _)
    -- (b) of the decoupling: transfer `K` to `F`
    have hKF : K ≤ κ * F := by
      have h1 : ‖Pf - PS * PR‖ ≤ CD / Real.log N * F := hDN.2
      have h2 : ‖PS * PR‖ ≤ F + CD / Real.log N * F := by
        have hA : ‖PS * PR‖ - ‖Pf‖ ≤ ‖PS * PR - Pf‖ := norm_sub_norm_le _ _
        have hB : ‖PS * PR - Pf‖ ≤ CD / Real.log N * F := by
          rw [norm_sub_rev]; exact h1
        rw [hPfF] at hA
        linarith
      have h3 : CD / Real.log N ≤ |CD| := by
        rw [div_le_iff₀ hlogpos]; nlinarith [le_abs_self CD, abs_nonneg CD]
      have h4 : Sn * K ≤ (1 + |CD|) * F := by
        rw [← hPSSn, ← hPRK, ← norm_mul]
        nlinarith [h2, hFnn, h3]
      have h5 : δ * K ≤ Sn * K := by nlinarith [hδN, hKnn]
      rw [hκ, div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith [h4, h5]
    -- `‖R_W‖ ≤ (B_R + |C_R|) K`
    have hCRlog : CR / Real.log N ≤ |CR| := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [le_abs_self CR, abs_nonneg CR]
    have hRWK : ‖RW‖ ≤ (BR + |CR|) * K := by
      have h1 : ‖RW - cR J * PR‖ ≤ CR / Real.log N * K := by
        simpa [hRW, hPR, hK, hJdef] using hRN
      have h2 : ‖cR J * PR‖ ≤ BR * K := by
        rw [norm_mul, hPRK]
        exact mul_le_mul (hcRB J) le_rfl hKnn hBRnn
      have h3 : ‖RW‖ ≤ ‖RW - cR J * PR‖ + ‖cR J * PR‖ := by
        simpa using norm_add_le (RW - cR J * PR) (cR J * PR)
      nlinarith [h1, h2, h3, hKnn, hCRlog]
    -- the four pieces
    have hT1 : ‖fullWindowMean N J h - SW * RW‖ ≤ |CD| / Real.log N * F := by
      have h1 : ‖fullWindowMean N J h - SW * RW‖ ≤ CD / Real.log N * F := hDN.1
      have h3 : CD / Real.log N ≤ |CD| / Real.log N := by
        gcongr
        exact le_abs_self CD
      exact h1.trans (mul_le_mul_of_nonneg_right h3 hFnn)
    have hJP : B' * (J : ℝ) * P₀ / N ≤ 1 / Real.log N := by
      rw [div_le_div_iff₀ hNR hlogpos]
      have hJnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
      have hlognn : (0 : ℝ) ≤ Real.log N := by linarith
      have hJL : (0 : ℝ) ≤ (J : ℝ) * Real.log N := by positivity
      have hkey : (B' * P₀ + 1) * ((J : ℝ) * Real.log N / N) ≤ 1 := hsmallN
      have hmul : (B' * P₀ + 1) * ((J : ℝ) * Real.log N) ≤ N := by
        have hdiv : (B' * P₀ + 1) * ((J : ℝ) * Real.log N) / N ≤ 1 := by
          calc (B' * P₀ + 1) * ((J : ℝ) * Real.log N) / N
              = (B' * P₀ + 1) * ((J : ℝ) * Real.log N / N) := by ring
            _ ≤ 1 := hkey
        have := (div_le_iff₀ hNR).mp hdiv
        linarith
      nlinarith [hmul, hJL, hB'nn, hP₀R.le]
    have hT2 : ‖(SW - c' J * PS) * RW‖ ≤ (1 / Real.log N) * ((BR + |CR|) * K) := by
      have h1 : ‖SW - c' J * PS‖ ≤ B' * (J : ℝ) * P₀ / N := by
        simpa [hSW, hPS, hJdef, hP₀] using h4N
      rw [norm_mul]
      have hb : (0 : ℝ) ≤ (BR + |CR|) * K := by positivity
      exact mul_le_mul (h1.trans hJP) hRWK (norm_nonneg _) (by positivity)
    have hT3 : ‖(c' J * PS) * (RW - cR J * PR)‖ ≤ B' * (|CR| / Real.log N * K) := by
      rw [norm_mul]
      have h1 : ‖c' J * PS‖ ≤ B' := by
        rw [norm_mul, hPSSn]
        nlinarith [hc'B J, hSnle, norm_nonneg (c' J), hB'nn,
          Finset.prod_nonneg (fun j (_ : j ∈ Finset.Icc 1 J) =>
            norm_nonneg (smoothSiteMean N h j 2))]
      have h2 : ‖RW - cR J * PR‖ ≤ |CR| / Real.log N * K := by
        have := (show ‖RW - cR J * PR‖ ≤ CR / Real.log N * K by
          simpa [hRW, hPR, hK, hJdef] using hRN)
        have h3 : CR / Real.log N ≤ |CR| / Real.log N := by
          gcongr
          exact le_abs_self CR
        nlinarith [this, h3, hKnn]
      exact mul_le_mul h1 h2 (norm_nonneg _) hB'nn
    have hT4 : ‖(c' J * cR J) * (PS * PR - Pf)‖ ≤ B' * BR * (|CD| / Real.log N * F) := by
      rw [norm_mul]
      have h1 : ‖c' J * cR J‖ ≤ B' * BR := by
        rw [norm_mul]; exact mul_le_mul (hc'B J) (hcRB J) (norm_nonneg _) hB'nn
      have h2 : ‖PS * PR - Pf‖ ≤ |CD| / Real.log N * F := by
        rw [norm_sub_rev]
        have h3 : CD / Real.log N ≤ |CD| / Real.log N := by
          gcongr
          exact le_abs_self CD
        nlinarith [hDN.2, h3, hFnn]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    -- assemble
    have hdecomp : fullWindowMean N J h - (c' J * cR J) * Pf
        = (fullWindowMean N J h - SW * RW) + (SW - c' J * PS) * RW
          + (c' J * PS) * (RW - cR J * PR) + (c' J * cR J) * (PS * PR - Pf) := by
      ring
    have hKκ : K ≤ κ * F := hKF
    have hnorm4 : ∀ a b c d : ℂ, ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      intro a b c d
      calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
        _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by linarith [norm_add_le (a + b) c]
        _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by linarith [norm_add_le a b]
    calc ‖fullWindowMean N J h - (c' J * cR J) * Pf‖
        ≤ ‖fullWindowMean N J h - SW * RW‖ + ‖(SW - c' J * PS) * RW‖
            + ‖(c' J * PS) * (RW - cR J * PR)‖ + ‖(c' J * cR J) * (PS * PR - Pf)‖ := by
          rw [hdecomp]; exact hnorm4 _ _ _ _
      _ ≤ |CD| / Real.log N * F + (1 / Real.log N) * ((BR + |CR|) * K)
            + B' * (|CR| / Real.log N * K) + B' * BR * (|CD| / Real.log N * F) := by
          linarith [hT1, hT2, hT3, hT4]
      _ ≤ (|CD| + (BR + |CR|) * κ + B' * |CR| * κ + B' * BR * |CD|) / Real.log N * F := by
          have hinv : (0 : ℝ) < 1 / Real.log N := by positivity
          have e1 : (1 / Real.log N) * ((BR + |CR|) * K)
              ≤ (1 / Real.log N) * ((BR + |CR|) * (κ * F)) := by
            have hbc : (0 : ℝ) ≤ BR + |CR| := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKκ hbc) hinv.le
          have e2 : B' * (|CR| / Real.log N * K) ≤ B' * (|CR| / Real.log N * (κ * F)) := by
            have h0 : (0 : ℝ) ≤ |CR| / Real.log N := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKκ h0) hB'nn
          have e3 : (|CD| + (BR + |CR|) * κ + B' * |CR| * κ + B' * BR * |CD|)
                / Real.log N * F
              = |CD| / Real.log N * F + (1 / Real.log N) * ((BR + |CR|) * (κ * F))
                + B' * (|CR| / Real.log N * (κ * F)) + B' * BR * (|CD| / Real.log N * F) := by
            have hL0 : Real.log N ≠ 0 := ne_of_gt hlogpos
            field_simp
          rw [e3]
          linarith [e1, e2]
/-- The kickoff's wiring, now a corollary of the sharpened one. -/
theorem crtConstantSched_of_rough {h : ℤ} (hR : RoughIndependence h) (hD : SmoothRoughDecoupling h)
    (hS : SmoothNonvanishing h) : CRTConstantSched h :=
  crtConstantSched_of_roughAt (roughIndependenceAt_of_rough hR le_rfl) hD (hS 2 le_rfl)

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


/-! ### N1a **discharged** at `y = 2`

At `y = 2` the smooth site mean is, up to `O(1/N)`, the period-2 average
`(1 + e(h 4^{-j}))/2`, whose modulus is `|cos(π h 4^{-j})|`.  The product over `j ≤ J` is bounded
below uniformly in `J` exactly when no `h 4^{-j}` is a half-integer — i.e. exactly when `v₂(h)` is
even, which is the complement of `ChowlaSector`.  So the frozen node `SmoothNonvanishing`, at the
only `y` the wiring consumes, is a **theorem** on the sector where the wiring invokes it. -/

lemma omegaLe_two_eq (m : ℕ) (hm : m ≠ 0) : omegaLe 2 m = if 2 ∣ m then 1 else 0 := by
  classical
  have hfil : (m.primeFactors.filter (fun p => p ≤ 2)) = if 2 ∣ m then {2} else ∅ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    split_ifs with hd
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp, _, _⟩, hle⟩
        exact le_antisymm hle hp.two_le
      · rintro rfl
        exact ⟨⟨Nat.prime_two, hd, hm⟩, le_rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro ⟨hp, hdvd, _⟩ hle
      exact hd (le_antisymm hle hp.two_le ▸ hdvd)
  rw [omegaLe, hfil]
  split_ifs <;> simp

/-- The period-2 average that `smoothSiteMean _ h j 2` approximates. -/
noncomputable def halfAvg (h : ℤ) (j : ℕ) : ℂ := (1 + ePhase ((h : ℝ) / (4 : ℝ) ^ j)) / 2

lemma norm_halfAvg_le_one (h : ℤ) (j : ℕ) : ‖halfAvg h j‖ ≤ 1 := by
  rw [halfAvg, norm_div, Complex.norm_ofNat]
  have h1 : ‖(1 : ℂ) + ePhase ((h : ℝ) / (4 : ℝ) ^ j)‖ ≤ 2 := by
    calc ‖(1 : ℂ) + ePhase ((h : ℝ) / (4 : ℝ) ^ j)‖ ≤ ‖(1 : ℂ)‖ + ‖ePhase ((h : ℝ) / (4:ℝ)^j)‖ :=
          norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_ePhase]; norm_num
  linarith [h1]

lemma ePhase_zero : ePhase 0 = 1 := by simp [ePhase]

/-- Leaf: the `y = 2` site mean is within `4/N` of the period average. -/
lemma smoothSiteMean_two_close (h : ℤ) (j : ℕ) (hj : 1 ≤ j) (N : ℕ) (hN : 0 < N) :
    ‖smoothSiteMean N h j 2 - halfAvg h j‖ ≤ 4 / N := by
  classical
  set F : ℕ → ℂ := fun n => ePhase ((h : ℝ) * omegaLe 2 (n + j) / (4 : ℝ) ^ j) with hF
  have hper : ∀ n, F (n + 2) = F n := by
    intro n
    have h1 : n + 2 + j ≠ 0 := by omega
    have h2 : n + j ≠ 0 := by omega
    have hiff : (2 ∣ n + 2 + j) ↔ (2 ∣ n + j) := by omega
    have heq : omegaLe 2 (n + 2 + j) = omegaLe 2 (n + j) := by
      rw [omegaLe_two_eq _ h1, omegaLe_two_eq _ h2]
      simp only [hiff]
    simp only [hF]
    rw [heq]
  have hb : ∀ n, ‖F n‖ ≤ 1 := fun n => le_of_eq (norm_ePhase _)
  have key := periodic_mean_close F 2 (by norm_num) hper hb N hN
  have hsum : (∑ n ∈ Finset.range 2, F n) / ((2 : ℕ) : ℂ) = halfAvg h j := by
    have hr : (∑ n ∈ Finset.range 2, F n) = F 0 + F 1 := by
      simp [Finset.sum_range_succ]
    rcases Nat.even_or_odd j with he | ho
    · have hj2 : j % 2 = 0 := Nat.even_iff.mp he
      have h0 : omegaLe 2 (0 + j) = 1 := by
        rw [omegaLe_two_eq _ (by omega), if_pos (by omega)]
      have h1 : omegaLe 2 (1 + j) = 0 := by
        rw [omegaLe_two_eq _ (by omega), if_neg (by omega)]
      rw [hr, hF]
      simp only [h0, h1]
      rw [halfAvg]
      norm_num [ePhase_zero]
      ring_nf
    · have hj2 : j % 2 = 1 := Nat.odd_iff.mp ho
      have h0 : omegaLe 2 (0 + j) = 0 := by
        rw [omegaLe_two_eq _ (by omega), if_neg (by omega)]
      have h1 : omegaLe 2 (1 + j) = 1 := by
        rw [omegaLe_two_eq _ (by omega), if_pos (by omega)]
      rw [hr, hF]
      simp only [h0, h1]
      rw [halfAvg]
      norm_num [ePhase_zero]
  have hsite : smoothSiteMean N h j 2 = (∑ n ∈ Finset.Ico N (2 * N), F n) / N := rfl
  rw [hsite, ← hsum]
  calc ‖(∑ n ∈ Finset.Ico N (2 * N), F n) / N - (∑ n ∈ Finset.range 2, F n) / ((2:ℕ):ℂ)‖
      ≤ 2 * ((2 : ℕ) : ℝ) / N := key
    _ = 4 / N := by norm_num

/-- Off the Chowla sector no `h 4^{-j}` is a half-integer. -/
lemma ePhase_ne_neg_one_of_not_chowla {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h)
    {j : ℕ} (hj : 1 ≤ j) : ePhase ((h : ℝ) / (4 : ℝ) ^ j) ≠ -1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro heq
  set x : ℝ := (h : ℝ) / (4 : ℝ) ^ j with hx
  have hsq : ePhase (x + x) = 1 := by
    rw [ePhase_add, heq]; norm_num
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((x + x : ℝ) : ℂ)) = 1 := hsq
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hcast : ((x + x : ℝ) : ℂ) = (n : ℂ) := by
    refine mul_right_cancel₀ hne ?_
    linear_combination hn
  have hreal : x + x = (n : ℝ) := by exact_mod_cast hcast
  -- `n` is odd, else `ePhase x = 1`
  have hnodd : ¬ (2 ∣ n) := by
    rintro ⟨m, hmdef⟩
    have hxm : x = (m : ℝ) := by
      rw [hmdef] at hreal
      push_cast at hreal
      linarith
    have : ePhase x = 1 := by
      rw [hxm, show ((m : ℝ)) = 0 + (m : ℤ) from by push_cast; ring, ePhase_add_int, ePhase_zero]
    rw [heq] at this
    norm_num at this
  -- `2h = n · 4^j`
  have h4 : ((4 : ℝ) ^ j) ≠ 0 := by positivity
  have hmulR : (2 : ℝ) * h = (n : ℝ) * (4 : ℝ) ^ j := by
    rw [hx] at hreal
    field_simp at hreal
    linarith
  have hmulZ : (2 : ℤ) * h = n * 4 ^ j := by exact_mod_cast hmulR
  set k : ℕ := 2 * j - 1 with hk
  have hkodd : Odd k := ⟨j - 1, by omega⟩
  have hpow : (4 : ℤ) ^ j = 2 * 2 ^ k := by
    have : (4 : ℤ) ^ j = 2 ^ (2 * j) := by
      rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_mul]
    rw [this, show 2 * j = k + 1 from by omega, pow_succ]
    ring
  have hh2 : h = n * 2 ^ k := by
    have : (2 : ℤ) * h = 2 * (n * 2 ^ k) := by rw [hmulZ, hpow]; ring
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl; simp at hh2; exact hh hh2
  have hval : padicValInt 2 h = k := by
    rw [hh2, padicValInt.mul hn0 (by positivity)]
    have hz : padicValInt 2 n = 0 := by
      refine padicValInt.eq_zero_of_not_dvd ?_
      simpa using hnodd
    have hp : padicValInt 2 ((2 : ℤ) ^ k) = k := by
      rw [padicValInt, show ((2 : ℤ) ^ k).natAbs = 2 ^ k from by simp,
        padicValNat.prime_pow]
    rw [hz, hp, zero_add]
  exact hc (by rw [ChowlaSector, hval]; exact hkodd)

/-- Weierstrass-type product bound. -/
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f ε : ι → ℝ)
    (hε : ∀ i ∈ s, 0 ≤ ε i) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1)
    (hlb : ∀ i ∈ s, 1 - ε i ≤ f i) :
    1 - ∑ i ∈ s, ε i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have hmem : ∀ i ∈ t, i ∈ insert a t := fun i hi => Finset.mem_insert_of_mem hi
      have hat : a ∈ insert a t := Finset.mem_insert_self a t
      have IH := ih (fun i hi => hε i (hmem i hi)) (fun i hi => h0 i (hmem i hi))
        (fun i hi => h1 i (hmem i hi)) (fun i hi => hlb i (hmem i hi))
      have hpnn : 0 ≤ ∏ i ∈ t, f i :=
        Finset.prod_nonneg (fun i hi => h0 i (hmem i hi))
      have hple : (∏ i ∈ t, f i) ≤ 1 :=
        Finset.prod_le_one (fun i hi => h0 i (hmem i hi)) (fun i hi => h1 i (hmem i hi))
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa : 1 - ε a ≤ f a := hlb a hat
      have hεa : 0 ≤ ε a := hε a hat
      nlinarith [hpnn, hple, IH, hfa, hεa]

/-- Geometric tail. -/
lemma sum_quarter_pow_Ico_le (a b : ℕ) :
    ∑ j ∈ Finset.Ico a b, ((1 : ℝ) / 4) ^ j ≤ (4 / 3) * ((1 : ℝ) / 4) ^ a := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hfac : ∀ k ∈ Finset.range (b - a),
      ((1 : ℝ) / 4) ^ (a + k) = ((1:ℝ)/4) ^ a * ((1:ℝ)/4) ^ k := fun k _ => pow_add _ _ _
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  have hgeom : ∑ k ∈ Finset.range (b - a), ((1 : ℝ) / 4) ^ k ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num : ((1:ℝ)/4) ≠ 1),
      show ∀ x : ℝ, (x - 1) / ((1:ℝ)/4 - 1) = (4/3) * (1 - x) from fun x => by ring]
    have hp : (0 : ℝ) ≤ ((1:ℝ)/4) ^ (b - a) := by positivity
    linarith
  have hanm : (0 : ℝ) ≤ ((1:ℝ)/4) ^ a := by positivity
  nlinarith [hgeom, hanm]

/-- **N1a is a theorem at `y = 2`** off the Chowla sector. -/
theorem smoothNonvanishingAt_two {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h) :
    SmoothNonvanishingAt h 2 := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : (0 : ℝ) < |(h : ℝ)| := by
    have : ((h : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hh
    positivity
  -- choose the cut `j₁`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (16 * Real.pi * |(h : ℝ)|) (by norm_num : (1:ℝ) < 4)
  set j₁ : ℕ := m + 1 with hj₁
  have hj₁1 : 1 ≤ j₁ := by omega
  have hcut : 16 * Real.pi * |(h : ℝ)| < (4 : ℝ) ^ j₁ := by
    refine hm.trans_le ?_
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set A : ℕ → ℝ := fun j => ‖halfAvg h j‖ with hA
  have hA1 : ∀ j, A j ≤ 1 := fun j => norm_halfAvg_le_one h j
  have hA0 : ∀ j, 0 ≤ A j := fun j => norm_nonneg _
  have hApos : ∀ j, 1 ≤ j → 0 < A j := by
    intro j hj
    rw [hA]
    simp only
    rw [norm_pos_iff, halfAvg]
    intro hzero
    have : (1 : ℂ) + ePhase ((h : ℝ) / (4:ℝ)^j) = 0 := by
      field_simp at hzero; linear_combination hzero
    exact ePhase_ne_neg_one_of_not_chowla hh hc hj (by linear_combination this)
  set δ₀ : ℝ := ∏ j ∈ Finset.Ico 1 j₁, A j with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    refine Finset.prod_pos (fun j hj => hApos j ?_)
    exact (Finset.mem_Ico.mp hj).1
  -- tail bound
  have htail : ∀ j, j₁ ≤ j → 1 - (2 * Real.pi * |(h : ℝ)|) * ((1:ℝ)/4) ^ j ≤ A j := by
    intro j hj
    have hd : ‖ePhase ((h : ℝ) / (4:ℝ)^j) - ePhase 0‖ ≤ 4 * Real.pi * |(h : ℝ) / (4:ℝ)^j - 0| :=
      norm_ePhase_sub _ _
    have h4 : (0 : ℝ) < (4:ℝ)^j := by positivity
    have habs2 : |(h : ℝ) / (4:ℝ)^j - 0| = |(h:ℝ)| * ((1:ℝ)/4)^j := by
      rw [sub_zero, abs_div, abs_of_pos h4, div_pow, one_pow]
      field_simp
    rw [ePhase_zero, habs2] at hd
    have hnorm : ‖(1 : ℂ) + ePhase ((h : ℝ) / (4:ℝ)^j)‖
        ≥ 2 - 4 * Real.pi * (|(h:ℝ)| * ((1:ℝ)/4)^j) := by
      have hsplit : (1 : ℂ) + ePhase ((h : ℝ) / (4:ℝ)^j)
          = 2 + (ePhase ((h : ℝ) / (4:ℝ)^j) - 1) := by ring
      rw [hsplit]
      have := norm_sub_norm_le (2 : ℂ) (-(ePhase ((h : ℝ) / (4:ℝ)^j) - 1))
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h3 : ‖-(ePhase ((h : ℝ) / (4:ℝ)^j) - 1)‖ = ‖ePhase ((h : ℝ) / (4:ℝ)^j) - 1‖ := by
        rw [norm_neg]
      have h4' : (2 : ℂ) - (-(ePhase ((h : ℝ) / (4:ℝ)^j) - 1)) = 2 + (ePhase ((h : ℝ) / (4:ℝ)^j) - 1) := by
        ring
      rw [h2, h3, h4'] at this
      linarith [this, hd]
    rw [hA]
    simp only [halfAvg, norm_div, Complex.norm_ofNat]
    linarith [hnorm]
  -- the uniform lower bound on the head·tail product
  have hprodA : ∀ J : ℕ, j₁ ≤ J + 1 → δ₀ / 2 ≤ ∏ j ∈ Finset.Icc 1 J, A j := by
    intro J hJ
    have hIcc : Finset.Icc 1 J = Finset.Ico 1 (J + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hsplit : (∏ j ∈ Finset.Ico 1 j₁, A j) * ∏ j ∈ Finset.Ico j₁ (J+1), A j
        = ∏ j ∈ Finset.Ico 1 (J+1), A j := Finset.prod_Ico_consecutive _ hj₁1 hJ
    set ε : ℕ → ℝ := fun j => (2 * Real.pi * |(h : ℝ)|) * ((1:ℝ)/4) ^ j with hε
    have hsum : ∑ j ∈ Finset.Ico j₁ (J+1), ε j ≤ 1 / 2 := by
      have h1 : ∑ j ∈ Finset.Ico j₁ (J+1), ε j
          = (2 * Real.pi * |(h : ℝ)|) * ∑ j ∈ Finset.Ico j₁ (J+1), ((1:ℝ)/4) ^ j := by
        rw [hε, ← Finset.mul_sum]
      have h2 := sum_quarter_pow_Ico_le j₁ (J+1)
      have hq : ((1:ℝ)/4) ^ j₁ = 1 / (4:ℝ)^j₁ := by
        rw [div_pow, one_pow]
      have h4pos : (0 : ℝ) < (4:ℝ)^j₁ := by positivity
      have hkey : (2 * Real.pi * |(h : ℝ)|) * ((4/3) * ((1:ℝ)/4) ^ j₁) ≤ 1 / 2 := by
        have h5 : (2 * Real.pi * |(h : ℝ)|) * ((4/3) * (1 / (4:ℝ)^j₁))
            = (8/3) * (Real.pi * |(h : ℝ)|) / (4:ℝ)^j₁ := by
          field_simp; ring
        rw [hq, h5, div_le_iff₀ h4pos]
        nlinarith [hcut, hpi, habs]
      have hcoef : (0:ℝ) ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
      calc ∑ j ∈ Finset.Ico j₁ (J+1), ε j
          = (2 * Real.pi * |(h : ℝ)|) * ∑ j ∈ Finset.Ico j₁ (J+1), ((1:ℝ)/4) ^ j := h1
        _ ≤ (2 * Real.pi * |(h : ℝ)|) * ((4/3) * ((1:ℝ)/4) ^ j₁) := by
              exact mul_le_mul_of_nonneg_left h2 hcoef
        _ ≤ 1 / 2 := hkey
    have htailprod : (1:ℝ)/2 ≤ ∏ j ∈ Finset.Ico j₁ (J+1), A j := by
      have := one_sub_sum_le_prod (Finset.Ico j₁ (J+1)) A ε
        (fun i _ => by rw [hε]; positivity) (fun i _ => hA0 i) (fun i _ => hA1 i)
        (fun i hi => htail i (Finset.mem_Ico.mp hi).1)
      linarith [this, hsum]
    rw [hIcc, ← hsplit]
    have hδ₀nn : 0 ≤ δ₀ := hδ₀pos.le
    rw [← hδ₀]
    nlinarith [htailprod, hδ₀pos]
  -- transfer to the site means
  refine ⟨δ₀ / 4, by positivity, ?_⟩
  have hsmall : ∀ᶠ N : ℕ in atTop, 4 * (windowJ N : ℝ) / N ≤ δ₀ / 4 := by
    have hlim : Tendsto (fun N : ℕ => 4 * ((windowJ N : ℝ) / N)) atTop (𝓝 0) := by
      simpa using windowJ_div_tendsto_zero.const_mul (4 : ℝ)
    refine (hlim.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < δ₀ / 4))).mono ?_
    intro N hN
    calc 4 * (windowJ N : ℝ) / N = 4 * ((windowJ N : ℝ) / N) := by ring
      _ ≤ δ₀ / 4 := hN.le
  filter_upwards [hsmall, tendsto_windowJ.eventually_ge_atTop j₁, eventually_gt_atTop 0]
    with N hNsmall hNJ hN0
  set J := windowJ N with hJ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hdiff : ‖(∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j 2) - ∏ j ∈ Finset.Icc 1 J, halfAvg h j‖
      ≤ (Finset.Icc 1 J).card * (4 / N) := by
    refine norm_prod_sub_prod_le _ _ _ _ (by positivity)
      (fun j _ => norm_smoothSiteMean_le_one N h j 2) (fun j _ => norm_halfAvg_le_one h j)
      (fun j hj => smoothSiteMean_two_close h j (Finset.mem_Icc.mp hj).1 N hN0)
  have hcard : ((Finset.Icc 1 J).card : ℝ) ≤ (J : ℝ) := by
    rw [Nat.card_Icc]
    simp
  have hprodnorm : ∏ j ∈ Finset.Icc 1 J, ‖smoothSiteMean N h j 2‖
      = ‖∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j 2‖ := by
    rw [norm_prod]
  have hAprod : ‖∏ j ∈ Finset.Icc 1 J, halfAvg h j‖ = ∏ j ∈ Finset.Icc 1 J, A j := by
    rw [norm_prod]
  have hlow : δ₀ / 2 ≤ ∏ j ∈ Finset.Icc 1 J, A j := hprodA J (by omega)
  have hstep := norm_sub_norm_le (∏ j ∈ Finset.Icc 1 J, halfAvg h j)
    (∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j 2)
  rw [hprodnorm]
  have hdiff' : ‖(∏ j ∈ Finset.Icc 1 J, halfAvg h j) - ∏ j ∈ Finset.Icc 1 J, smoothSiteMean N h j 2‖
      ≤ (J : ℝ) * (4 / N) := by
    rw [norm_sub_rev]
    exact hdiff.trans (by nlinarith [hcard, (by positivity : (0:ℝ) ≤ 4 / N)])
  have hJN : (J : ℝ) * (4 / N) ≤ δ₀ / 4 := by
    have : (J : ℝ) * (4 / N) = 4 * (J : ℝ) / N := by ring
    rw [this]; exact hNsmall
  rw [hAprod] at hstep
  linarith [hstep, hdiff', hlow, hJN]

/-! ### The site half of N1a′ is an exact identity

At `y = 2` the smooth phase at one site takes only the two values `1` (odd argument) and
`ζ_j = e(h 4^{-j})` (even argument), so the site covariance can be computed exactly: it is
`(ζ_j − 1)` times the discrepancy between the rough mean over the whole window and its restriction
to the odd residue.  No analysis enters.  Since `‖ζ_j − 1‖ ≤ 2π|h| 4^{-j}`, the per-site errors are
geometrically small in `j`, which is what makes the `J`-uniformity of `SmoothRoughDecoupling`
cheap.  See `PROBE-2026-09-20-smooth-rough-decoupling.md`. -/

/-- The rough phase at one site. -/
noncomputable def roughPhase (h : ℤ) (j n : ℕ) : ℂ :=
  ePhase ((h : ℝ) * omegaAbove 2 (n + j) / (4 : ℝ) ^ j)

/-- The full phase splits into the two-valued smooth factor and the rough phase. -/
lemma fullPhase_eq (h : ℤ) (j n : ℕ) (hj : 1 ≤ j) :
    ePhase ((h : ℝ) * omegaR (n + j) / (4 : ℝ) ^ j)
      = (if 2 ∣ n + j then ePhase ((h : ℝ) / (4:ℝ)^j) else 1) * roughPhase h j n := by
  have hne : n + j ≠ 0 := by omega
  have hsplit : (h : ℝ) * omegaR (n + j) / (4:ℝ)^j
      = (h : ℝ) * omegaLe 2 (n + j) / (4:ℝ)^j + (h : ℝ) * omegaAbove 2 (n + j) / (4:ℝ)^j := by
    rw [omegaR_eq_omegaLe_add_omegaAbove 2 (n + j)]; ring
  rw [hsplit, ePhase_add, roughPhase]
  congr 1
  rw [omegaLe_two_eq _ hne]
  by_cases hd : 2 ∣ n + j
  · rw [if_pos hd, if_pos hd]; norm_num
  · rw [if_neg hd, if_neg hd]; norm_num [ePhase_zero]

/-- **The covariance of a two-valued factor is exact.**  If `s n = a` on `p` and `b` off `p`,
then `𝔼[s·r] − 𝔼[s]𝔼[r] = (a − b)(c_¬p Σ_p r − c_p Σ_¬p r)/N²`.  No hypothesis on `r`. -/
theorem twoValued_covariance (N : ℕ) (hN : 0 < N) (p : ℕ → Prop) [DecidablePred p]
    (a b : ℂ) (r : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico N (2*N), (if p n then a else b) * r n) / N
      - ((∑ n ∈ Finset.Ico N (2*N), (if p n then a else b)) / N)
        * ((∑ n ∈ Finset.Ico N (2*N), r n) / N)
      = (a - b) * ((((Finset.Ico N (2*N)).filter (fun n => ¬ p n)).card : ℂ)
            * (∑ n ∈ (Finset.Ico N (2*N)).filter p, r n)
          - (((Finset.Ico N (2*N)).filter p).card : ℂ)
            * (∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ p n), r n)) / (N:ℂ)^2 := by
  classical
  set S : Finset ℕ := Finset.Ico N (2*N) with hS
  set Se : ℂ := ∑ n ∈ S.filter p, r n with hSe
  set So : ℂ := ∑ n ∈ S.filter (fun n => ¬ p n), r n with hSo
  set ce : ℂ := ((S.filter p).card : ℂ) with hce
  set co : ℂ := ((S.filter (fun n => ¬ p n)).card : ℂ) with hco
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : ce + co = (N : ℂ) := by
    rw [hce, hco, ← Nat.cast_add, Finset.card_filter_add_card_filter_not, hS, Nat.card_Ico]
    congr 1
    omega
  have h1 : ∑ n ∈ S, (if p n then a else b) * r n = a * Se + b * So := by
    rw [← Finset.sum_filter_add_sum_filter_not S p]
    rw [hSe, hSo, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun n hn => by rw [if_pos (Finset.mem_filter.mp hn).2])
    · exact Finset.sum_congr rfl (fun n hn => by rw [if_neg (Finset.mem_filter.mp hn).2])
  have h2 : ∑ n ∈ S, (if p n then a else b) = a * ce + b * co := by
    rw [← Finset.sum_filter_add_sum_filter_not S p]
    congr 1
    · rw [hce, Finset.sum_congr rfl (fun n hn => by
        rw [if_pos (Finset.mem_filter.mp hn).2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [hco, Finset.sum_congr rfl (fun n hn => by
        rw [if_neg (Finset.mem_filter.mp hn).2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : ∑ n ∈ S, r n = Se + So := by
    rw [← Finset.sum_filter_add_sum_filter_not S p]
  rw [h1, h2, h3, ← hcard]
  have hsum0 : ce + co ≠ 0 := by rw [hcard]; exact hNC
  field_simp
  ring

/-- **Exact site covariance**.  With `ζ = e(h 4^{-j})`, `cₑ`/`c_o` the number of even/odd
arguments and `Sₑ`/`S_o` the corresponding rough sums, the one-site covariance is
`(ζ − 1)(c_o Sₑ − cₑ S_o)/N²`. -/
theorem fullSiteMean_covariance_identity (N : ℕ) (h : ℤ) (j : ℕ) (hj : 1 ≤ j) (hN : 0 < N) :
    fullSiteMean N h j - smoothSiteMean N h j 2 * roughSiteMean N h j 2
      = (ePhase ((h:ℝ)/(4:ℝ)^j) - 1)
        * ((((Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n
            - (((Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n)
        / (N : ℂ)^2 := by
  classical
  set S : Finset ℕ := Finset.Ico N (2*N) with hS
  set ζ : ℂ := ePhase ((h:ℝ)/(4:ℝ)^j) with hζ
  set Se : ℂ := ∑ n ∈ S.filter (fun n => 2 ∣ n + j), roughPhase h j n with hSe
  set So : ℂ := ∑ n ∈ S.filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n with hSo
  set ce : ℂ := ((S.filter (fun n => 2 ∣ n + j)).card : ℂ) with hce
  set co : ℂ := ((S.filter (fun n => ¬ 2 ∣ n + j)).card : ℂ) with hco
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : ce + co = (N : ℂ) := by
    rw [hce, hco, ← Nat.cast_add, Finset.card_filter_add_card_filter_not, hS, Nat.card_Ico]
    congr 1
    omega
  -- the three window sums
  have hfull : ∑ n ∈ S, ePhase ((h : ℝ) * omegaR (n + j) / (4 : ℝ) ^ j) = ζ * Se + So := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => 2 ∣ n + j)]
    rw [hSe, hSo, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [fullPhase_eq h j n hj, if_pos (Finset.mem_filter.mp hn).2]
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [fullPhase_eq h j n hj, if_neg (Finset.mem_filter.mp hn).2, one_mul]
  have hsmooth : ∑ n ∈ S, ePhase ((h : ℝ) * omegaLe 2 (n + j) / (4 : ℝ) ^ j) = ζ * ce + co := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => 2 ∣ n + j)]
    congr 1
    · rw [hce, Finset.sum_congr rfl (fun n hn => ?_), Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hne : n + j ≠ 0 := by omega
      rw [omegaLe_two_eq _ hne, if_pos (Finset.mem_filter.mp hn).2]
      norm_num [hζ]
    · rw [hco, Finset.sum_congr rfl (fun n hn => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
      have hne : n + j ≠ 0 := by omega
      rw [omegaLe_two_eq _ hne, if_neg (Finset.mem_filter.mp hn).2]
      norm_num [ePhase_zero]
  have hrough : ∑ n ∈ S, roughPhase h j n = Se + So := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => 2 ∣ n + j)]
  have hf : fullSiteMean N h j = (ζ * Se + So) / N := by rw [fullSiteMean, ← hS, hfull]
  have hs : smoothSiteMean N h j 2 = (ζ * ce + co) / N := by rw [smoothSiteMean, ← hS, hsmooth]
  have hr : roughSiteMean N h j 2 = (Se + So) / N := by
    rw [roughSiteMean, ← hS, ← hrough]
    rfl
  have hsum0 : ce + co ≠ 0 := by rw [hcard]; exact hNC
  rw [hf, hs, hr, ← hcard]
  field_simp
  ring

/-- The covariance in "mean minus conditional mean" form: `(ζ − 1)·(c_o/N)·(E r − E[r | odd])`,
divided out.  Bound form: the covariance is at most `‖ζ − 1‖` times the odd-residue discrepancy. -/
theorem norm_fullSiteMean_covariance_le (N : ℕ) (h : ℤ) (j : ℕ) (hj : 1 ≤ j) (hN : 0 < N) :
    ‖fullSiteMean N h j - smoothSiteMean N h j 2 * roughSiteMean N h j 2‖
      ≤ 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j
        * (‖(((Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n
            - (((Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n‖
           / (N : ℝ)^2) := by
  classical
  rw [fullSiteMean_covariance_identity N h j hj hN, norm_div, norm_mul]
  have hz : ‖ePhase ((h:ℝ)/(4:ℝ)^j) - 1‖ ≤ 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j := by
    have hd : ‖ePhase ((h : ℝ) / (4:ℝ)^j) - ePhase 0‖ ≤ 4 * Real.pi * |(h : ℝ) / (4:ℝ)^j - 0| :=
      norm_ePhase_sub _ _
    have h4 : (0 : ℝ) < (4:ℝ)^j := by positivity
    have habs2 : |(h : ℝ) / (4:ℝ)^j - 0| = |(h:ℝ)| * ((1:ℝ)/4)^j := by
      rw [sub_zero, abs_div, abs_of_pos h4, div_pow, one_pow]
      field_simp
    rw [ePhase_zero, habs2] at hd
    linarith [hd]
  have hden : ‖((N : ℂ)^2)‖ = (N : ℝ)^2 := by
    rw [norm_pow, Complex.norm_natCast]
  rw [hden]
  have hd2 : (0:ℝ) < (N:ℝ)^2 := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  rw [show 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j
        * (‖(((Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n
            - (((Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n‖
           / (N : ℝ)^2)
      = (4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j)
        * ‖(((Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n
            - (((Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j)).card : ℂ)
              * ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n‖
        / (N : ℝ)^2 from by ring]
  gcongr

/-! ### The window half of N1a′ is the *same* identity

At `y = 2` the smooth *window* phase is two-valued too: `[2 ∣ n+j+1]` alternates with `j`, so
`smoothTail 2 J n` depends on `n` only through its parity.  Both halves of
`SmoothRoughDecoupling` at `y = 2` are therefore instances of `twoValued_covariance`, and the
whole node collapses to a single quantity: the even/odd discrepancy of the rough phase. -/

/-- The value of `smoothTail 2 J` at even arguments. -/
noncomputable def tailEven (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (if 2 ∣ (j + 1) then (1:ℝ) else 0) / (4:ℝ) ^ (j + 1)
/-- The value of `smoothTail 2 J` at odd arguments. -/
noncomputable def tailOdd (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (if ¬ 2 ∣ (j + 1) then (1:ℝ) else 0) / (4:ℝ) ^ (j + 1)

lemma smoothTail_two_eq (J n : ℕ) :
    smoothTail 2 J n = if 2 ∣ n then tailEven J else tailOdd J := by
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, smoothTail, tailEven]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [omegaLe_two_eq _ (by omega)]
    have hiff : (2 ∣ n + j + 1) ↔ (2 ∣ (j + 1)) := by omega
    by_cases hd : 2 ∣ (j + 1)
    · rw [if_pos (hiff.mpr hd), if_pos hd]; norm_num
    · rw [if_neg (fun hx => hd (hiff.mp hx)), if_neg hd]; norm_num
  · rw [if_neg hn, smoothTail, tailOdd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [omegaLe_two_eq _ (by omega)]
    have hiff : (2 ∣ n + j + 1) ↔ ¬ (2 ∣ (j + 1)) := by omega
    by_cases hd : 2 ∣ (j + 1)
    · rw [if_neg (fun hx => (hiff.mp hx) hd), if_neg (not_not_intro hd)]; norm_num
    · rw [if_pos (hiff.mpr hd), if_pos hd]; norm_num

/-- **Exact window covariance** at `y = 2`. -/
theorem fullWindowMean_covariance_identity (N J : ℕ) (h : ℤ) (hN : 0 < N) :
    fullWindowMean N J h - smoothWindowMean N J h 2 * roughWindowMean N J h 2
      = (ePhase ((h:ℝ) * tailEven J) - ePhase ((h:ℝ) * tailOdd J))
        * ((((Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n)).card : ℂ)
            * (∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n),
                ePhase ((h:ℝ) * roughTail 2 J n))
          - (((Finset.Ico N (2*N)).filter (fun n => 2 ∣ n)).card : ℂ)
            * (∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n),
                ePhase ((h:ℝ) * roughTail 2 J n))) / (N:ℂ)^2 := by
  classical
  set a : ℂ := ePhase ((h:ℝ) * tailEven J) with ha
  set b : ℂ := ePhase ((h:ℝ) * tailOdd J) with hb
  set r : ℕ → ℂ := fun n => ePhase ((h:ℝ) * roughTail 2 J n) with hr
  have hsmoothphase : ∀ n, ePhase ((h:ℝ) * smoothTail 2 J n) = if 2 ∣ n then a else b := by
    intro n
    rw [smoothTail_two_eq]
    by_cases hn : 2 ∣ n
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg hn]
  have hfull : fullWindowMean N J h
      = (∑ n ∈ Finset.Ico N (2*N), (if 2 ∣ n then a else b) * r n) / N := by
    rw [fullWindowMean]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ePhase_truncTail_factor 2 J n h, hsmoothphase n]
  have hsm : smoothWindowMean N J h 2
      = (∑ n ∈ Finset.Ico N (2*N), (if 2 ∣ n then a else b)) / N := by
    rw [smoothWindowMean]
    congr 1
    exact Finset.sum_congr rfl (fun n _ => hsmoothphase n)
  have hro : roughWindowMean N J h 2 = (∑ n ∈ Finset.Ico N (2*N), r n) / N := rfl
  rw [hfull, hsm, hro]
  exact twoValued_covariance N hN (fun n => 2 ∣ n) a b r

/-- **Wiring, N1a discharged**: on the non-Chowla sector the only open inputs are
`RoughIndependenceAt h 2` and `SmoothRoughDecoupling h`. -/
theorem crtConstantSched_of_roughAt_notChowla {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h)
    (hR : RoughIndependenceAt h 2) (hD : SmoothRoughDecoupling h) : CRTConstantSched h :=
  crtConstantSched_of_roughAt hR hD (smoothNonvanishingAt_two hh hc)

/-- **Headline wiring with N1a discharged**: `SmoothNonvanishing` is gone from the hypotheses. -/
theorem isNormal_G4_of_roughAt
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h →
      RoughIndependenceAt h 2 ∧ SmoothRoughDecoupling h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) := by
  refine isNormal_G4_of_windowDecay (fun h hh => ?_)
  by_cases hc : ChowlaSector h
  · exact hCh h hh hc
  · obtain ⟨hR, hD⟩ := hSD h hh hc
    exact fullWindowMean_tendsto_zero_of_sched
      (crtConstantSched_of_roughAt_notChowla hh hc hR hD) hSite hh

end NormalNumbers.G4
