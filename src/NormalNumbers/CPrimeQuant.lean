/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeQuantStatement
import NormalNumbers.WeylCriterion
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
  sorry

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

/-- **Trapezoid Erdős–Turán.**  Weyl bounds up to frequency `H` give interval discrepancy
`4δ + 1/(δH) + Σ_{h=1}^{H} 2B(h)/h`.  95% (standard; the `1/h` weight is `|ĝ(h)| ≤ 1/(π|h|)` for
a trapezoid, the tail is `Σ_{|h|>H} 1/(π²δh²)` against the trivial bound `|W_h| ≤ 1`). -/
theorem orbitDefectLe_of_weyl (x : ℝ) (B : ℤ → ℝ) (hW : OrbitWeylLe x B) (δ : ℝ) (hδ : 0 < δ)
    (H : ℕ) (hH : 1 ≤ H) :
    OrbitDefectLe x (4 * δ + 1 / (δ * H) + ∑ h ∈ Finset.Icc 1 H, 2 * B h / h) := by
  sorry

lemma orbitDefectLe_mono {x D D' : ℝ} (h : OrbitDefectLe x D) (hD : D ≤ D') :
    OrbitDefectLe x D' := by
  intro a c ha hac hc ε hε
  filter_upwards [h a c ha hac hc ε hε] with n hn
  linarith

/-- Arithmetic for the glue: with `L = log(1/ρ) ≥ log 3` and `H = ⌈1/ρ²⌉`, `log(H+1) ≤ 3L`. -/
lemma log_H_succ_le {ρ : ℝ} (hρ : 0 < ρ) (hρ3 : ρ ≤ 1 / 3) :
    Real.log ((⌈1 / ρ ^ 2⌉₊ : ℝ) + 1) ≤ 3 * Real.log (1 / ρ) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hceil : (⌈1 / ρ ^ 2⌉₊ : ℝ) < 1 / ρ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : (1 : ℝ) ≤ 1 / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]; nlinarith
  have hle : (⌈1 / ρ ^ 2⌉₊ : ℝ) + 1 ≤ (1 / ρ) ^ 3 := by
    have : 3 / ρ ^ 2 ≤ (1 / ρ) ^ 3 := by
      rw [div_pow, one_pow, div_le_div_iff₀ hρ2 (by positivity)]; nlinarith
    have : 1 / ρ ^ 2 + 2 ≤ 3 / ρ ^ 2 := by
      have : 3 / ρ ^ 2 = 1 / ρ ^ 2 + 2 * (1 / ρ ^ 2) := by ring
      linarith
    linarith
  calc Real.log ((⌈1 / ρ ^ 2⌉₊ : ℝ) + 1) ≤ Real.log ((1 / ρ) ^ 3) :=
        Real.log_le_log (by positivity) hle
    _ = 3 * Real.log (1 / ρ) := by rw [Real.log_pow]; norm_num

/-- **Glue.**  The crux plus trapezoid Erdős–Turán give `CPrimeQuant` with
`C = 5 + 128C₁` and `ρ₀ = min(ρ₁, 1/3)`. -/
theorem cPrimeQuant_of_parts : CPrimeQuant := by
  obtain ⟨C₁, ρ₁, hC₁, hρ₁, hρ₁1, hW⟩ := orbitWeylQuant
  refine ⟨5 + 128 * C₁, min ρ₁ (1 / 3), by positivity, by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro P _ hP ρ hρ hρ0 hS
  have hρ3 : ρ ≤ 1 / 3 := hρ0.trans (min_le_right _ _)
  set L := Real.log (1 / ρ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    calc Real.exp 1 ≤ 3 := this
      _ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
  set H := ⌈1 / ρ ^ 2⌉₊ with hHdef
  have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (by
    rw [hHdef]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hHge : 1 / ρ ^ 2 ≤ (H : ℝ) := Nat.le_ceil _
  have hD := orbitDefectLe_of_weyl _ _ (hW P hP ρ hρ (hρ0.trans (min_le_left _ _)) hS) ρ hρ H hH1
  refine orbitDefectLe_mono hD ?_
  -- the three pieces
  have htail : 1 / (ρ * H) ≤ ρ := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / ρ ^ 2 * ρ ^ 2 = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hHge (le_of_lt (by positivity : (0:ℝ) < ρ ^ 2))]
  have hlogH := log_H_succ_le hρ hρ3
  have hterm : ∀ h ∈ Finset.Icc 1 H,
      2 * (C₁ * ρ * (L + Real.log (|((h : ℤ) : ℝ)| + 1)) ^ 2) / (h : ℝ)
        ≤ 32 * C₁ * ρ * L ^ 2 * (1 / (h : ℝ)) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast hh.1
    have habs : |((h : ℤ) : ℝ)| = (h : ℝ) := by
      push_cast; exact abs_of_pos hhpos
    rw [habs]
    have hlog0 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogh : Real.log ((h : ℝ) + 1) ≤ 3 * L := by
      refine le_trans (Real.log_le_log (by linarith) ?_) hlogH
      have : (h : ℝ) ≤ H := by exact_mod_cast hh.2
      linarith
    have hsq : (L + Real.log ((h : ℝ) + 1)) ^ 2 ≤ 16 * L ^ 2 := by nlinarith
    rw [mul_one_div, div_le_div_iff_of_pos_right hhpos]
    have : 0 ≤ C₁ * ρ := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hharm : ∑ h ∈ Finset.Icc 1 H, 1 / (h : ℝ) ≤ 1 + 3 * L := by
    have hh := harmonic_le_one_add_log H
    have heq : ∑ h ∈ Finset.Icc 1 H, 1 / (h : ℝ) = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    rw [heq]
    refine hh.trans ?_
    have : Real.log H ≤ Real.log ((H : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hH1) (by linarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hfin : 32 * C₁ * ρ * L ^ 2 * (1 + 3 * L) ≤ 128 * C₁ * ρ * L ^ 3 := by
    have : 0 ≤ C₁ * ρ * L ^ 2 := by positivity
    nlinarith
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hharm (by positivity))
  have hρL : ρ ≤ ρ * L ^ 3 := le_mul_of_one_le_right hρ.le (one_le_pow₀ hL1)
  have : 4 * ρ + 1 / (ρ * H) + ∑ h ∈ Finset.Icc 1 H,
      2 * (C₁ * ρ * (L + Real.log (|((h : ℤ) : ℝ)| + 1)) ^ 2) / (h : ℝ)
        ≤ (5 + 128 * C₁) * ρ * L ^ 3 := by nlinarith
  exact this

/-- **Quantitative C′.**  Bounded square-root fresh mass `ρ ≤ ρ₀` plus a divergent reciprocal sum
give orbit discrepancy `≤ C·ρ·log³(1/ρ)` for `∑_{p∈P} 1/(4ᵖ−1)`.  Reduced to `orbitWeylQuant`
(the crux) and `orbitDefectLe_of_weyl` (trapezoid Erdős–Turán) by `cPrimeQuant_of_parts`. -/
theorem cPrimeQuant_holds : CPrimeQuant := cPrimeQuant_of_parts

/-- **Residue-class richness.**  Every fixed-length base-4 word has positive lower frequency in
`∑_{p≡a (q)} 1/(4ᵖ−1)` once `q` is large.  From `cPrimeQuant_holds` with `ρ = log 2/φ(q)`, Mertens
in progressions, `DivergentRecip` (mathlib's `not_summable_residueClass_prime_div`) and the
orbit-to-digit window translation.  85% given `cPrimeQuant_holds`. -/
theorem cPrimeResidueRich_holds : CPrimeResidueRich := by
  sorry

end NormalNumbers.PrimeModel.Quant
