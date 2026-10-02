/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeQuantSchedule
import NormalNumbers.WeylCriterion
import NormalNumbers.CPrimeQuantET
import NormalNumbers.CPrimeQuantAP
import NormalNumbers.LiteratureBMStrong
import NormalNumbers.Wall
import NormalNumbers.G4WiringSparse
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Quantitative C′: the proofs (campaign launched 2026-10-02)

Targets: the frozen `CPrimeQuant` and `CPrimeResidueRich` (`CPrimeQuantStatement.lean`).
Route, build gaps and stop rules: `KICKOFF-2026-09-30-cprime-quantitative.md`; paper derivation
(refereed once, no false step): `docs/CPRIME-QUANTITATIVE-2026-09-30.md`.

## Decomposition of `cPrimeQuant_holds` (lap 1, 2026-10-02)

* `orbitWeylQuant` — **the crux**: limsup Weyl sums `≤ C₁ρ(log(1/ρ) + log(|h|+1))²`.  This is
  the fixed-`u` rerun of `PrimeModelFamilyGraded` (build gaps 1–4 of the doc) with
  `u = max(u₀, ⌈log(1/ρ)⌉)`, so that `4e^{−u} ≤ 4ρ` and `log u ≤ log(1/ρ)` fold into the square.
* `orbitDefectLe_of_weyl` — trapezoid Erdős–Turán (build gap 5): with ramp `δ` and cutoff `H`,
  discrepancy `≤ 4δ + 1/(δH) + Σ_{h≤H} 2B(h)/h`.  Standard; route: `trapUp`/`trapLo` from
  `WeylCriterion`, Fourier coefficients by integration by parts
  (`fourierCoeffOn_of_hasDeriv_right`), `|ĝ(h)| ≤ min(1/(π|h|), 1/(π²δh²))`.
* `cPrimeQuant_of_parts` — the glue at `δ = ρ`, `H = ⌈1/ρ²⌉`, proved below.

Split either proof into named sub-lemmas freely.  A step found false goes into `Maze.lean` with
its refuting theorem, and the campaign stops.
-/

namespace NormalNumbers.PrimeModel.Quant

open Filter

/-- Limsup Weyl-sum bound for the base-4 orbit of `x`: at every frequency `h ≠ 0`, the Fourier
mean is eventually within `ε` of `B h`. -/
def OrbitWeylLe (x : ℝ) (B : ℤ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ‖fourierMean (orbit 4 x) h n‖ ≤ B h + ε

/-! ### Gap 4: quantitative wiring (orbit Weyl sums vs the truncated window mean) -/

section Wiring

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse Topology

variable (S : ℕ → Prop) [DecidablePred S]

/-- Under `TailOK`, the orbit prefix Fourier mean and the truncated window mean are asymptotic
(the `hgoal` step of `G4Sparse.prefix_fourier_tendsto_zero`, isolated). -/
theorem prefix_sub_window_tendsto (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched) (h : ℤ) :
    Tendsto (fun N => fourierMean (orbit 4 (subsetLambert S 4)) h N
      - windowMeanS S (Jsched N) h N) atTop (𝓝 0) := by
  set F : ℕ → ℂ := fun n => ePhase (h * orbit 4 (subsetLambert S 4) n) with hF
  have hFtail : ∀ n : ℕ, F n = ePhase (h * (TWeight.subset S).tailB 4 n) := by
    intro n
    have hshift : (h : ℝ) * Int.fract ((TWeight.subset S).tailB 4 n)
        = (h : ℝ) * (TWeight.subset S).tailB 4 n
          + ((-(h * ⌊(TWeight.subset S).tailB 4 n⌋) : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [hF]
    simp only
    rw [orbit_eq_fract_tailB_subset, hshift, ePhase_add_int]
  have hgoal : Tendsto (fun N => prefixMean F N - windowMeanS S (Jsched N) h N) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (g := fun N : ℕ => 4 * Real.pi * |(h : ℝ)| *
        ((∑ n ∈ Finset.range N,
            |(TWeight.subset S).tailB 4 n - truncTailS S (Jsched N) n|) / N)) ?_
      (by simpa using hTail.const_mul (4 * Real.pi * |(h : ℝ)|))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set J := Jsched N with hJ
    have hsub : prefixMean F N - windowMeanS S J h N
        = (∑ n ∈ Finset.range N,
            (ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n))) / N := by
      rw [prefixMean, windowMeanS, prefixMean, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun n _ => by rw [hFtail n])
    rw [hsub, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hNR)]
    calc ‖∑ n ∈ Finset.range N,
            (ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n))‖
        ≤ ∑ n ∈ Finset.range N,
            ‖ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, 4 * Real.pi * |(h : ℝ)| *
            |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          calc ‖ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n)‖
              ≤ 4 * Real.pi *
                  |(h : ℝ) * (TWeight.subset S).tailB 4 n - (h : ℝ) * truncTailS S J n| :=
                norm_ePhase_sub _ _
            _ = 4 * Real.pi * |(h : ℝ)| *
                  |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
                rw [← mul_sub, abs_mul]; ring
      _ = 4 * Real.pi * |(h : ℝ)| *
            ∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
          rw [Finset.mul_sum]
  refine hgoal.congr (fun N => ?_)
  congr 1
  rw [fourierMean, prefixMean]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hF]; simp only; rw [ePhase]
  congr 1
  push_cast
  ring

/-- **Quantitative wiring.**  A negligible tail and limsup window-mean bounds `B` give the
orbit Weyl bound `OrbitWeylLe` with the same `B`. -/
theorem orbitWeylLe_of_window (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched) (B : ℤ → ℝ)
    (hB : ∀ h : ℤ, h ≠ 0 → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖windowMeanS S (Jsched N) h N‖ ≤ B h + ε) :
    OrbitWeylLe (subsetLambert S 4) B := by
  intro h hh ε hε
  have hd := (prefix_sub_window_tendsto S Jsched hTail h).norm
  rw [norm_zero] at hd
  filter_upwards [hB h hh (ε / 2) (by linarith), hd.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 2))]
    with N h1 h2
  have := norm_sub_norm_le (fourierMean (orbit 4 (subsetLambert S 4)) h N)
    (windowMeanS S (Jsched N) h N)
  linarith

/-- Bounded square-root fresh mass below `1` controls the dyadic fresh mass `S_P(N, 2N)`. -/
theorem freshMassTwo_of_sqrtFreshMassLe {ρ : ℝ} (hρ : ρ < 1) (hS : SqrtFreshMassLe S ρ) :
    ∀ᶠ N : ℕ in atTop, recipSumIoc S N (2 * N) ≤ 1 := by
  have hev := hS ((1 - ρ) / 2) (by linarith)
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  filter_upwards [h2.eventually hev] with N hN
  have hsq : Nat.sqrt (2 * N) ≤ N := by
    by_contra hc
    have h1 : N + 1 ≤ Nat.sqrt (2 * N) := by omega
    have h2 : (N + 1) ^ 2 ≤ Nat.sqrt (2 * N) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 := Nat.sqrt_le' (2 * N)
    nlinarith
  have hmono : recipSumIoc S N (2 * N) ≤ recipSumIoc S (Nat.sqrt (2 * N)) (2 * N) := by
    unfold recipSumIoc
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left hsq)) ?_
    exact fun p _ _ => by positivity
  linarith

/-- **Tail under bounded fresh mass.**  The graded schedule `JG` keeps a negligible tail as soon
as `ρ < 1` (the doc's "infinite phase tail" row). -/
theorem tailOK_of_sqrtFreshMassLe {ρ : ℝ} (hρ : ρ < 1) (hS : SqrtFreshMassLe S ρ)
    (hP : DivergentRecip S) : TailOK S (FamilyGraded.JG S) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_
    (FamilyGraded.tail_graded S (freshMassTwo_of_sqrtFreshMassLe S hρ hS) hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 S (FamilyGraded.JG S N) N hN

end Wiring

/-- `log₄ n ≤ log(n + 1)`. -/
lemma natLog4_le_log (n : ℕ) : ((Nat.log 4 n : ℕ) : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpow : ((4 : ℝ) ^ (Nat.log 4 n)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hn.ne'
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hl
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hn1 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hn) (by linarith)
  have : (0 : ℝ) ≤ (Nat.log 4 n : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The crux (window-mean form).**  On the graded site count `J = JG P N`, bounded square-root
fresh mass gives truncated window means of size `O(ρ (log(1/ρ) + log|h|)²)`.  Paper: doc
§"Transfer", `|W_h| = O(ρ(log²|h| + log u log|h| + log u)) + 4e^{−u}` at fixed `u` (cutoffs
`y_j = N^{u⁻²2⁻ʲ}`, a schedule independent of `J`), then `u = max(u₀, ⌈log 1/ρ⌉)`.  70% (paper
refereed; Lean path = build gaps 1–3: the fixed-`u` rerun of `windowMean_le_terms` and limsup
versions of `termE1/E4a/E4b/E4c/E5`). -/
theorem windowWeylQuant : ∃ C₁ ρ₁ : ℝ, 0 < C₁ ∧ 0 < ρ₁ ∧ ρ₁ < 1 ∧
    ∀ (P : ℕ → Prop) [DecidablePred P], G4Sparse.DivergentRecip P →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → SqrtFreshMassLe P ρ →
        ∀ h : ℤ, h ≠ 0 → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
          ‖G4Sparse.windowMeanS P (FamilyGraded.JG P N) h N‖
            ≤ C₁ * ρ * (Real.log (1 / ρ) + Real.log (|(h : ℝ)| + 1)) ^ 2 + ε := by
  refine ⟨10 ^ 6, 1 / 3, by norm_num, by norm_num, by norm_num, ?_⟩
  intro P _ hP ρ hρ hρ3 hS h hh ε hε
  set L := Real.log (1 / ρ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    calc Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
  set u : ℕ := max 3000 ⌈L⌉₊ with hu
  have hu3000 : 3000 ≤ u := le_max_left _ _
  have huL : L ≤ (u : ℝ) := (Nat.le_ceil L).trans (by exact_mod_cast le_max_right _ _)
  have huL' : (u : ℝ) ≤ 3001 + L := by
    have h1 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
    rcases le_total 3000 ⌈L⌉₊ with hc | hc
    · rw [hu, max_eq_right hc]; linarith
    · rw [hu, max_eq_left hc]; push_cast; linarith
  have hE0 : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hE : ∀ᶠ N : ℕ in atTop, FamilyGraded.epsG P N ≤ 2 * ρ := by
    filter_upwards [QuantSchedule.epsG_eventually_le P hS hρ] with N hN; linarith
  -- the pointwise and limiting pieces
  have hwin := QuantSchedule.windowMean_le_terms P u (by omega) hP h
  have hE1 := QuantSchedule.termE1_le P u (by omega) h hE0 hE
  have hE4a := QuantSchedule.termE4a_le P u (by omega)
  have hE4c := QuantSchedule.termE4c_tendsto P u hu3000 hP
  have hE5 := QuantSchedule.termE5_tendsto P u hu3000 hP h hE0 hE
  have hJN := (QuantSchedule.JG_div_tendsto P u hP).const_mul (4 * Real.pi * |(h : ℝ)| / 3)
  rw [mul_zero] at hJN
  have hsmall := (hE4c.add hE5).add hJN
  rw [add_zero, add_zero] at hsmall
  -- the constant
  set M := L + Real.log (|(h : ℝ)| + 1) with hM
  have hlogh : 0 ≤ Real.log (|(h : ℝ)| + 1) := Real.log_nonneg (by linarith [abs_nonneg (h : ℝ)])
  have hM1 : 1 ≤ M := by linarith
  set k : ℝ := ((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkM : k ≤ 2 * M := by
    have h1 := natLog4_le_log h.natAbs
    have h2 : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2] at h1
    rw [hk]; push_cast; linarith
  set c : ℝ := 2 + 3 * (u : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcM : c ≤ 9100 * M := by rw [hc]; nlinarith
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
  have hA : 2 * (2 * k * (k + c) + 4 * Real.pi * (k + c)) ≤ 400000 * M ^ 2 := by
    have hkc : k + c ≤ 9102 * M := by linarith
    have hkc0 : 0 ≤ k + c := by linarith
    have h1 : 2 * k * (k + c) ≤ 2 * (2 * M) * (9102 * M) := by
      apply mul_le_mul (by linarith) hkc hkc0 (by linarith)
    have h2 : 4 * Real.pi * (k + c) ≤ 16 * (9102 * M) := by
      have := mul_le_mul hpi hkc hkc0 (by norm_num)
      nlinarith [Real.pi_pos]
    nlinarith
  -- the exponentially small terms are at most `ρ` each
  have hexpu : Real.exp (-(u : ℝ)) ≤ ρ := by
    calc Real.exp (-(u : ℝ)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = ρ := by rw [hL, Real.log_div (by norm_num) hρ.ne', Real.log_one, zero_sub, neg_neg,
          Real.exp_log hρ]
  have hu0 : (3000 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3000
  have hexp4a : 4 * Real.exp 20 * Real.exp (-((u : ℝ) ^ 2 / 32)) ≤ 4 * ρ := by
    have : Real.exp 20 * Real.exp (-((u : ℝ) ^ 2 / 32)) ≤ Real.exp (-(u : ℝ)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    linarith
  -- assemble
  filter_upwards [hwin, hE1, hE4a, hsmall.eventually (gt_mem_nhds hε),
    (FamilyGraded.JG_tendsto P hP).eventually_ge_atTop (h.natAbs + 1), eventually_gt_atTop 0]
    with N hw h1 h4a hsm hJ hN
  have hb := hw ⟨h.natAbs + 1, by omega, hJ, G4Sparse.nontrivial_site hh⟩ hN
  have h4b := QuantSchedule.termE4b_le P u N
  have hρ0 : 0 ≤ ρ := hρ.le
  have hfin : 2 * (2 * ρ) * (2 * k * (k + c) + 4 * Real.pi * (k + c)) ≤ 2 * ρ * (400000 * M ^ 2) := by
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 2 * ρ)
    nlinarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have hk' : ((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) = k := rfl
  have hc' : (2 + 3 * (u : ℝ)) = c := rfl
  have : 5 * ρ ≤ 5 * ρ * M ^ 2 := le_mul_of_one_le_right (by positivity) hM2
  nlinarith

/-- **The crux (orbit form).**  Bounded square-root fresh mass gives orbit Weyl sums of size
`O(ρ (log(1/ρ) + log|h|)²)`: `windowWeylQuant` through the quantitative wiring. -/
theorem orbitWeylQuant : ∃ C₁ ρ₁ : ℝ, 0 < C₁ ∧ 0 < ρ₁ ∧ ρ₁ < 1 ∧
    ∀ (P : ℕ → Prop) [DecidablePred P], G4Sparse.DivergentRecip P →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → SqrtFreshMassLe P ρ →
        OrbitWeylLe (PrimeLambert.subsetLambert P 4)
          (fun h => C₁ * ρ * (Real.log (1 / ρ) + Real.log (|(h : ℝ)| + 1)) ^ 2) := by
  obtain ⟨C₁, ρ₁, hC₁, hρ₁, hρ₁1, hW⟩ := windowWeylQuant
  refine ⟨C₁, ρ₁, hC₁, hρ₁, hρ₁1, fun P _ hP ρ hρ hρ1 hS => ?_⟩
  exact orbitWeylLe_of_window P _ (tailOK_of_sqrtFreshMassLe P (lt_of_le_of_lt hρ1 hρ₁1) hS hP)
    _ (hW P hP ρ hρ hρ1 hS)

/-- **Erdős–Turán (Fejér sandwich).**  Weyl bounds up to frequency `H` give interval discrepancy
`2δ + 1/(4δ²(H+1)) + Σ_{h=1}^{H} 2B(h)/h`, via `visit_err` (CPrimeQuantET). -/
theorem orbitDefectLe_of_weyl (x : ℝ) (B : ℤ → ℝ) (hW : OrbitWeylLe x B) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (H : ℕ) (hH : 1 ≤ H) :
    OrbitDefectLe x (2 * δ + 1 / (4 * δ ^ 2 * (H + 1))
      + ∑ h ∈ Finset.Icc 1 H, 2 * B h / h) := by
  intro a c ha hac hc ε hε
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  set ε' := ε / (2 * H) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hB0 : ∀ k : ℕ, 1 ≤ k → 0 ≤ B k := by
    intro k hk
    refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨n, hn⟩ := (hW k (by exact_mod_cast (show k ≠ 0 by omega)) e he).exists
    linarith [norm_nonneg (fourierMean (orbit 4 x) (k : ℤ) n)]
  have hall : ∀ᶠ n : ℕ in atTop, ∀ k ∈ Finset.Icc 1 H,
      ‖fourierMean (orbit 4 x) (k : ℤ) n‖ ≤ B k + ε' := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact hW k (by have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)) ε' hε'0
  filter_upwards [hall, eventually_gt_atTop 0] with n hn hn0
  have hu : ∀ k, 0 ≤ orbit 4 x k ∧ orbit 4 x k < 1 :=
    fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  refine (visit_err H (orbit 4 x) hu hδ hδ2 ha hac hc n hn0).trans ?_
  have hterm : ∀ k ∈ Finset.Icc 1 H, 2 * (‖fourierMean (orbit 4 x) (k : ℤ) n‖ / (Real.pi * k))
      ≤ 2 * B k / k + 2 * ε' := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hW' := hn k hk
    have hBk := hB0 k hk1
    have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have e1 : ‖fourierMean (orbit 4 x) (k : ℤ) n‖ / (Real.pi * k)
        ≤ ‖fourierMean (orbit 4 x) (k : ℤ) n‖ / k :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by nlinarith)
    have e2 : ‖fourierMean (orbit 4 x) (k : ℤ) n‖ / k ≤ B k / k + ε' := by
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      nlinarith
    have : 2 * B k / k = 2 * (B k / k) := by ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul] at hsum
  have : ((H + 1 - 1 : ℕ) : ℝ) * (2 * ε') = ε := by
    rw [Nat.add_sub_cancel, hε']; field_simp
  linarith

lemma orbitDefectLe_mono {x D D' : ℝ} (h : OrbitDefectLe x D) (hD : D ≤ D') :
    OrbitDefectLe x D' := by
  intro a c ha hac hc ε hε
  filter_upwards [h a c ha hac hc ε hε] with n hn
  linarith

/-- Arithmetic for the glue: with `L = log(1/ρ) ≥ log 3` and `H = ⌈1/ρ³⌉`, `log(H+1) ≤ 4L`. -/
lemma log_H_succ_le {ρ : ℝ} (hρ : 0 < ρ) (hρ3 : ρ ≤ 1 / 3) :
    Real.log ((⌈1 / ρ ^ 3⌉₊ : ℝ) + 1) ≤ 4 * Real.log (1 / ρ) := by
  have hceil : (⌈1 / ρ ^ 3⌉₊ : ℝ) < 1 / ρ ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  set y := 1 / ρ with hy
  have hy3 : 3 ≤ y := by rw [hy, le_div_iff₀ hρ]; linarith
  have hρy : 1 / ρ ^ 3 = y ^ 3 := by rw [hy, div_pow, one_pow]
  have hle : (⌈1 / ρ ^ 3⌉₊ : ℝ) + 1 ≤ y ^ 4 := by
    have h27 : 27 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
    have : y ^ 3 + 2 ≤ y ^ 4 := by
      have : y ^ 4 = y * y ^ 3 := by ring
      nlinarith
    linarith
  calc Real.log ((⌈1 / ρ ^ 3⌉₊ : ℝ) + 1) ≤ Real.log (y ^ 4) :=
        Real.log_le_log (by positivity) hle
    _ = 4 * Real.log y := by rw [Real.log_pow]; norm_num

/-- **Glue.**  The crux plus Fejér Erdős–Turán (`δ = ρ`, `H = ⌈1/ρ³⌉`) give `CPrimeQuant` with
`C = 3 + 250C₁` and `ρ₀ = min(ρ₁, 1/3)`. -/
theorem cPrimeQuant_of_parts : CPrimeQuant := by
  obtain ⟨C₁, ρ₁, hC₁, hρ₁, hρ₁1, hW⟩ := orbitWeylQuant
  refine ⟨3 + 250 * C₁, min ρ₁ (1 / 3), by positivity, by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro P _ hP ρ hρ hρ0 hS
  have hρ3 : ρ ≤ 1 / 3 := hρ0.trans (min_le_right _ _)
  set L := Real.log (1 / ρ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    calc Real.exp 1 ≤ 3 := this
      _ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
  set H := ⌈1 / ρ ^ 3⌉₊ with hHdef
  have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (by
    rw [hHdef]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hHge : 1 / ρ ^ 3 ≤ (H : ℝ) := Nat.le_ceil _
  have hD := orbitDefectLe_of_weyl _ _ (hW P hP ρ hρ (hρ0.trans (min_le_left _ _)) hS) ρ hρ
    (by linarith) H hH1
  refine orbitDefectLe_mono hD ?_
  have htail : 1 / (4 * ρ ^ 2 * (H + 1)) ≤ ρ := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : 1 / ρ ^ 3 * ρ ^ 3 = 1 := by field_simp
    have : ρ ^ 3 * (H : ℝ) ≥ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hHge (le_of_lt (by positivity : (0:ℝ) < ρ ^ 3))]
    nlinarith [pow_pos hρ 3]
  have hlogH := log_H_succ_le hρ hρ3
  have hterm : ∀ h ∈ Finset.Icc 1 H,
      2 * (C₁ * ρ * (L + Real.log (|((h : ℤ) : ℝ)| + 1)) ^ 2) / (h : ℝ)
        ≤ 50 * C₁ * ρ * L ^ 2 * (1 / (h : ℝ)) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast hh.1
    have habs : |((h : ℤ) : ℝ)| = (h : ℝ) := by
      push_cast; exact abs_of_pos hhpos
    rw [habs]
    have hlog0 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogh : Real.log ((h : ℝ) + 1) ≤ 4 * L := by
      refine le_trans (Real.log_le_log (by linarith) ?_) hlogH
      have : (h : ℝ) ≤ H := by exact_mod_cast hh.2
      linarith
    have hsq : (L + Real.log ((h : ℝ) + 1)) ^ 2 ≤ 25 * L ^ 2 := by nlinarith
    rw [mul_one_div, div_le_div_iff_of_pos_right hhpos]
    have : 0 ≤ C₁ * ρ := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hharm : ∑ h ∈ Finset.Icc 1 H, 1 / (h : ℝ) ≤ 1 + 4 * L := by
    have hh := harmonic_le_one_add_log H
    have heq : ∑ h ∈ Finset.Icc 1 H, 1 / (h : ℝ) = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    rw [heq]
    refine hh.trans ?_
    have : Real.log H ≤ Real.log ((H : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hH1) (by linarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hfin : 50 * C₁ * ρ * L ^ 2 * (1 + 4 * L) ≤ 250 * C₁ * ρ * L ^ 3 := by
    have : 0 ≤ C₁ * ρ * L ^ 2 := by positivity
    nlinarith
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hharm (by positivity))
  have hρL : ρ ≤ ρ * L ^ 3 := le_mul_of_one_le_right hρ.le (one_le_pow₀ hL1)
  have : 2 * ρ + 1 / (4 * ρ ^ 2 * (H + 1)) + ∑ h ∈ Finset.Icc 1 H,
      2 * (C₁ * ρ * (L + Real.log (|((h : ℤ) : ℝ)| + 1)) ^ 2) / (h : ℝ)
        ≤ (3 + 250 * C₁) * ρ * L ^ 3 := by nlinarith
  exact this

/-- **Quantitative C′.**  Bounded square-root fresh mass `ρ ≤ ρ₀` plus a divergent reciprocal sum
give orbit discrepancy `≤ C·ρ·log³(1/ρ)` for `∑_{p∈P} 1/(4ᵖ−1)`.  Reduced to `orbitWeylQuant`
(the crux) and `orbitDefectLe_of_weyl` (trapezoid Erdős–Turán) by `cPrimeQuant_of_parts`. -/
theorem cPrimeQuant_holds : CPrimeQuant := cPrimeQuant_of_parts

/-- **Orbit discrepancy to word frequency.**  A discrepancy `D < 4^{-L}` gives every nonempty
base-4 word of length `L` positive lower frequency (`Literature.visitCount_eq_card_matchesAt`
and the `w.length` boundary windows of `card_filter_matchesAt_le`). -/
theorem wordFreq_of_defect {x D : ℝ} (hD : OrbitDefectLe x D) {w : List ℕ} (hw : w ≠ [])
    (hwd : ∀ d ∈ w, d < 4) (hDl : D < 1 / (4 : ℝ) ^ w.length) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c ≤ (countOccurrences w ((List.range n).map (digitOf 4 (Int.fract x))) : ℝ) / n := by
  set v := blockNatVal 4 w with hv
  set P : ℝ := (4 : ℝ) ^ w.length with hP
  have hP0 : 0 < P := by positivity
  have hvlt : v < 4 ^ w.length := blockNatVal_lt 4 w hwd
  have hv1 : (v : ℝ) + 1 ≤ P := by rw [hP]; exact_mod_cast hvlt
  set g := 1 / P - D with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨g / 2, by positivity, ?_⟩
  have hlen : (v + 1 : ℝ) / P - v / P = 1 / P := by ring
  have hE := hD (v / P) ((v + 1) / P) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hP0.le) (by rw [div_le_one hP0]; exact hv1)
    (g / 4) (by positivity)
  filter_upwards [hE, eventually_ge_atTop ⌈4 * w.length / g⌉₊, eventually_gt_atTop 0] with n hn hnL hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have horb : orbit 4 x = orbit 4 (Int.fract x) := (funext (orbit_fract 4 x)).symm
  have hvc := Literature.visitCount_eq_card_matchesAt 4 (by norm_num) x w hwd n
  rw [Nat.cast_ofNat, ← hv, ← hP] at hvc
  rw [horb, hvc, hlen] at hn
  have hcnt := (card_filter_matchesAt_le (digitOf 4 (Int.fract x)) w hw n).2
  have hcntR : (((Finset.range n).filter (MatchesAt (digitOf 4 (Int.fract x)) w)).card : ℝ)
      ≤ (countOccurrences w ((List.range n).map (digitOf 4 (Int.fract x))) : ℝ) + w.length := by
    exact_mod_cast hcnt
  have hLn : (w.length : ℝ) / n ≤ g / 4 := by
    rw [div_le_iff₀ hnR]
    have := (Nat.le_ceil (4 * (w.length : ℝ) / g)).trans
      (by exact_mod_cast hnL : (⌈4 * (w.length : ℝ) / g⌉₊ : ℝ) ≤ n)
    rw [div_le_iff₀ hg0] at this
    linarith
  have hlow := (abs_le.mp hn).1
  have : (((Finset.range n).filter (MatchesAt (digitOf 4 (Int.fract x)) w)).card : ℝ) / n
      ≤ (countOccurrences w ((List.range n).map (digitOf 4 (Int.fract x))) : ℝ) / n + w.length / n := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hcntR hnR.le
  linarith

/-- Arithmetic: `ρ log³(1/ρ) ≤ 216 √ρ` for `0 < ρ ≤ 1`. -/
lemma rho_log_cube_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ * Real.log (1 / ρ) ^ 3 ≤ 216 * Real.sqrt ρ := by
  have hl0 : 0 ≤ Real.log (1 / ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hl := Real.log_le_rpow_div (x := 1 / ρ) (by positivity) (by norm_num : (0 : ℝ) < 1 / 6)
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  -- (1/ρ)^(1/6) cubed is 1/√ρ
  have hcube : ((1 / ρ) ^ (1 / 6 : ℝ)) ^ 3 = 1 / Real.sqrt ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow,
      Real.div_rpow zero_le_one hρ.le, Real.one_rpow]
    norm_num
  have h1 : Real.log (1 / ρ) ^ 3 ≤ (6 * (1 / ρ) ^ (1 / 6 : ℝ)) ^ 3 := by
    have : Real.log (1 / ρ) ≤ 6 * (1 / ρ) ^ (1 / 6 : ℝ) := by
      have e : (1 / ρ) ^ (1 / 6 : ℝ) / (1 / 6) = 6 * (1 / ρ) ^ (1 / 6 : ℝ) := by ring
      linarith
    exact pow_le_pow_left₀ hl0 this 3
  rw [mul_pow, hcube] at h1
  have hsq : ρ = Real.sqrt ρ * Real.sqrt ρ := (Real.mul_self_sqrt hρ.le).symm
  calc ρ * Real.log (1 / ρ) ^ 3 ≤ ρ * (6 ^ 3 * (1 / Real.sqrt ρ)) :=
        mul_le_mul_of_nonneg_left h1 hρ.le
    _ = 216 * Real.sqrt ρ := by
        conv_lhs => rw [hsq]
        field_simp; norm_num

/-- **Residue-class richness.**  Every fixed-length base-4 word has positive lower frequency in
`∑_{p≡a (q)} 1/(4ᵖ−1)` once `q` is large: `cPrimeQuant_holds` at a fixed `ρ*` small for `L`,
`sqrtFreshMassLe_residue` (`ρ ≤ 9/φ(q) ≤ ρ*` for `q > ((K+1)!)^K`), `divergentRecip_residue`
and `wordFreq_of_defect`. -/
theorem cPrimeResidueRich_holds : CPrimeResidueRich := by
  obtain ⟨C, ρ₀, hC, hρ₀, hρ₀1, hQ⟩ := cPrimeQuant_holds
  intro L
  set θ : ℝ := 1 / (4 : ℝ) ^ L with hθ
  have hθ0 : 0 < θ := by positivity
  set r : ℝ := θ / (432 * C) with hr
  have hr0 : 0 < r := by positivity
  set ρs : ℝ := min ρ₀ (r ^ 2) with hρs
  have hρs0 : 0 < ρs := lt_min hρ₀ (by positivity)
  have hρs1 : ρs ≤ 1 := (min_le_left _ _).trans hρ₀1.le
  -- the discrepancy at ρs is below θ
  have hdisc : C * ρs * Real.log (1 / ρs) ^ 3 < θ := by
    have h1 := rho_log_cube_le hρs0 hρs1
    have h2 : Real.sqrt ρs ≤ r := by
      rw [Real.sqrt_le_left hr0.le]; exact min_le_right _ _
    have : C * ρs * Real.log (1 / ρs) ^ 3 ≤ C * (216 * r) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hC.le
    have e : C * (216 * r) = θ / 2 := by rw [hr]; field_simp; ring
    linarith
  -- K with 9/K ≤ ρs
  set K : ℕ := ⌈9 / ρs⌉₊ + 1 with hK
  refine ⟨((K + 1).factorial) ^ K + 1, fun q a hq ha w hwL hwd => ?_⟩
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hφK : K ≤ q.totient := le_totient_of_large K (by omega)
  have hφ : 9 / (q.totient : ℝ) ≤ ρs := by
    have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
    have : 9 / ρs ≤ (K : ℝ) := by
      rw [hK]; push_cast; linarith [Nat.le_ceil (9 / ρs)]
    rw [div_le_iff₀ (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) hφK))]
    rw [div_le_iff₀ hρs0] at this
    have : (K : ℝ) ≤ q.totient := by exact_mod_cast hφK
    nlinarith
  have hS : SqrtFreshMassLe (fun p => p % q = a % q) ρs := by
    intro ε hε
    filter_upwards [sqrtFreshMassLe_residue hq1 ha ε hε] with N hN
    linarith
  have hD := hQ (fun p => p % q = a % q) (divergentRecip_residue hq1 ha) ρs hρs0
    (min_le_left _ _) hS
  by_cases hw : w = []
  · subst hw
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnil : ∀ l : List ℕ, countOccurrences [] l = l.length + 1 := by
      intro l; rw [countOccurrences_eq_card]; simp
    rw [hnil, List.length_map, List.length_range]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hnR]; push_cast; linarith
  · exact wordFreq_of_defect hD hw hwd (by rw [hwL]; exact hdisc)

end NormalNumbers.PrimeModel.Quant
