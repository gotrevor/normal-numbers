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

theorem smoothWindowCRT (h : ℤ) (y : ℕ) (hy : 2 ≤ y) (hS : SmoothNonvanishing h) :
    ∃ (c' : ℕ → ℂ) (B : ℝ), (∀ J, ‖c' J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
      ‖smoothWindowMean N (windowJ N) h y
          - c' (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y‖
        ≤ B * (windowJ N : ℝ) * primorial y / N := by
  classical
  obtain ⟨δ, hδ, hδN⟩ := hS y hy
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
    (hD : SmoothRoughDecoupling h) (hS : SmoothNonvanishing h) : CRTConstantSched h := by
  classical
  obtain ⟨cR, BR, CR, hcRB, hRev⟩ := hR
  obtain ⟨CD, hDev⟩ := hD
  obtain ⟨δ, hδ, hδev⟩ := hS 2 le_rfl
  obtain ⟨c', B', hc'B, h4ev⟩ := smoothWindowCRT h 2 le_rfl hS
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
  crtConstantSched_of_roughAt (roughIndependenceAt_of_rough hR le_rfl) hD hS

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
