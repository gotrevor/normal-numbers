/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassRandomLambertMoment

/-!
# Random Erdős–Borwein subseries: the positive side (below exponent `ln 2`)

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 7eb1c8f3
(namespace relocated).  Paper-accepted by codex2 at 95% (mail 20261012T052349Z).  Paper argument:
`nn-erdos-borwein-random-2026-10-12.md`, section "Below ln 2".  LOCAL-ONLY branch.

The frozen headline `ebRandom_ae_normal_below_ln2` has no Hardy–Ramanujan hypothesis.  Per the
literature-as-hypothesis policy, this module proves the CONDITIONAL companion
`ebRandom_ae_normal_below_ln2_of_HR`, which takes the named input `HardyRamanujanLowerTail`.  The
unconditional headline stays in the packet until Hardy–Ramanujan itself is formalized.

Reusable, already proved in `NormalNumbers.CoefmassRandomLambertMoment` (general modulus `p`, no
primality): `anchor_phase_formula`, `anchor_tail_cos_le`, `cos_two_pi_le_of_near_rational`,
`bernMod_*`, `ePh_*`, `weylMean_even_expansion`.  The Bernoulli integral lemmas there are
`Prime`-indexed; port them to `ℕ` indices (`integral_ePh_finset_sum`,
`norm_integral_ePh_finset_sum`, `norm_integral_ePh_add_randomLambert_le`).
-/

namespace NormalNumbers.ErdosBorweinPositive

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Independent Bernoulli selections of positive integers (index `0` unused). -/
def BernoulliLawNat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ m, 0 ≤ delta m ∧ delta m ≤ 1) ∧
  (∀ m, Measurable (X m)) ∧ iIndepFun X μ ∧
    ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)

/-- The random Erdős–Borwein subseries `Σ_{m ≥ 1, X_m} 1/(b^m - 1)`. -/
noncomputable def ebLambert {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool) (w : Ω) : ℝ :=
  ∑' m : ℕ, (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)

/-- Literature input: the lower-tail consequence of the classical Hardy–Ramanujan inequality, via
the Poisson–Chernoff bound.  The source inequality is displayed as (1) in Fan, arXiv:2508.06005v3.
This is a named hypothesis, not an axiom (codex2). -/
def HardyRamanujanLowerTail : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ q : ℝ,
    0 < q → q < 1 - α + α * Real.log α →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (((Finset.Icc 1 N).filter (fun n =>
        (n.primeFactors.card : ℝ) ≤ α * Real.log (Real.log N))).card : ℝ) ≤
          C * N * Real.rpow (Real.log N) (-q)

/-! ### Shifted common-divisor reduction

The four lemmas below isolate the analytic content of `shifted_gcd_divisor_moment`: once the
Dirichlet series `∑ τ(d)^r / d²` is known to converge, the shifted moment follows by an exact
finite rearrangement and the elementary count of multiples in a shifted interval. -/

/-- A shifted interval contains at most `⌊(N+u)/d⌋` multiples of `d`. -/
theorem card_shifted_multiples_le (u d N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card ≤ (N + u) / d := by
  calc
    ((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card =
        (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).image (fun n => n + u)).card :=
      (Finset.card_image_of_injective _ (fun _ _ h => by omega)).symm
    _ ≤ ((Finset.range (N + u + 1)).filter (fun k => k ≠ 0 ∧ d ∣ k)).card := by
      apply Finset.card_le_card
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
      rcases Finset.mem_filter.mp hn with ⟨hn, hd⟩
      rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
        exact ⟨by omega, hd⟩⟩
    _ = (N + u) / d := by
      simpa [Nat.succ_eq_add_one] using Nat.card_multiples' (N + u) d

/-- Real-valued form of `card_shifted_multiples_le`, with a bound uniform in `N ≥ 1`. -/
theorem card_shifted_multiples_real_le (u d N : ℕ) (hN : 1 ≤ N) :
    (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card : ℝ) ≤
      ((u + 1 : ℕ) : ℝ) * N / d := by
  calc
    (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card : ℝ) ≤
        (((N + u) / d : ℕ) : ℝ) := by exact_mod_cast card_shifted_multiples_le u d N
    _ ≤ ((N + u : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    _ ≤ ((u + 1 : ℕ) : ℝ) * N / d := by
      gcongr
      exact_mod_cast (show N + u ≤ (u + 1) * N by
        calc
          N + u ≤ N + u * N := Nat.add_le_add_left (Nat.le_mul_of_pos_right u hN) N
          _ = (u + 1) * N := by ring)

/-- Rearrange a finite weighted sum over common divisors into a product of shifted counts. -/
theorem shifted_common_divisor_sum_eq (u v N B : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 B,
      if d ∣ n + u ∧ d ∣ m + v then f d else 0) =
      ∑ d ∈ Finset.Icc 1 B, f d *
        (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card : ℝ) *
        (((Finset.Icc 1 N).filter (fun m => d ∣ m + v)).card : ℝ) := by
  classical
  conv_lhs =>
    enter [2, n]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hinner (n : ℕ) :
      (∑ m ∈ Finset.Icc 1 N, if d ∣ n + u ∧ d ∣ m + v then f d else 0) =
        if d ∣ n + u then
          f d * (((Finset.Icc 1 N).filter (fun m => d ∣ m + v)).card : ℝ) else 0 := by
    by_cases hn : d ∣ n + u
    · simp only [hn, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]
    · simp [hn]
  rw [Finset.sum_congr rfl (fun n _ => hinner n)]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp [nsmul_eq_mul, mul_assoc]
  ring

/-- Common divisors in the required finite range are exactly the divisors of the gcd. -/
theorem gcd_divisors_eq_filter (u v N n m : ℕ) (hn : n ∈ Finset.Icc 1 N)
    (hm : m ∈ Finset.Icc 1 N) :
    (Nat.gcd (n + u) (m + v)).divisors =
      (Finset.Icc 1 (N + u + v)).filter
        (fun d => d ∣ n + u ∧ d ∣ m + v) := by
  ext d
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
  rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
  have hnu0 : n + u ≠ 0 := by omega
  have hg0 : Nat.gcd (n + u) (m + v) ≠ 0 := Nat.gcd_ne_zero_left hnu0
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    have hd' := (Nat.dvd_gcd_iff.mp hd)
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun hd0 =>
        hg0 (zero_dvd_iff.mp (hd0 ▸ hd))),
      le_trans (Nat.le_of_dvd (by omega) hd'.1) (by omega)⟩, hd'⟩
  · rintro ⟨hdB, hd1, hd2⟩
    exact ⟨Nat.dvd_gcd hd1 hd2, hg0⟩

/-- The shifted gcd-divisor moment follows from the one-variable divisor Dirichlet series. -/
theorem shifted_gcd_divisor_moment_of_summable (u v r : ℕ)
    (hsum : Summable (fun d : ℕ =>
      ((d.divisors.card : ℝ) ^ r) / (d : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r)) ≤ C * (N : ℝ)^2 := by
  let A : ℝ := ((u + 1 : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ)
  let T : ℝ := ∑' d : ℕ, ((d.divisors.card : ℝ) ^ r) / (d : ℝ) ^ 2
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 + A * T, by positivity, ?_⟩
  intro N hN
  let D := Finset.Icc 1 (N + u + v)
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (m : ℕ)
      (hm : m ∈ Finset.Icc 1 N) :
      (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r) ≤
        ∑ d ∈ D, if d ∣ n + u ∧ d ∣ m + v then
          ((d.divisors.card : ℝ) ^ r) else 0 := by
    let g := Nat.gcd (n + u) (m + v)
    have hnu0 : n + u ≠ 0 := by
      rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
      omega
    have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hnu0
    have hmem : g ∈ g.divisors := Nat.mem_divisors_self g hg0
    calc
      ((g.divisors.card : ℝ) ^ r) ≤
          ∑ d ∈ g.divisors, ((d.divisors.card : ℝ) ^ r) :=
        Finset.single_le_sum (s := g.divisors)
          (f := fun d => ((d.divisors.card : ℝ) ^ r))
          (fun d hd => by positivity) hmem
      _ = ∑ d ∈ D, if d ∣ n + u ∧ d ∣ m + v then
          ((d.divisors.card : ℝ) ^ r) else 0 := by
        rw [gcd_divisors_eq_filter u v N n m hn hm]
        simp only [D, Finset.sum_filter]
  calc
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r)) ≤
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ∑ d ∈ D, if d ∣ n + u ∧ d ∣ m + v then
            ((d.divisors.card : ℝ) ^ r) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact hpoint n hn m hm
    _ = ∑ d ∈ D, ((d.divisors.card : ℝ) ^ r) *
          (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card : ℝ) *
          (((Finset.Icc 1 N).filter (fun m => d ∣ m + v)).card : ℝ) :=
      shifted_common_divisor_sum_eq u v N (N + u + v) _
    _ ≤ ∑ d ∈ D, A * (N : ℝ) ^ 2 *
          (((d.divisors.card : ℝ) ^ r) / (d : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hcu := card_shifted_multiples_real_le u d N hN
      have hcv := card_shifted_multiples_real_le v d N hN
      calc
        ((d.divisors.card : ℝ) ^ r) *
            (((Finset.Icc 1 N).filter (fun n => d ∣ n + u)).card : ℝ) *
            (((Finset.Icc 1 N).filter (fun m => d ∣ m + v)).card : ℝ) ≤
            ((d.divisors.card : ℝ) ^ r) *
              (((u + 1 : ℕ) : ℝ) * N / d) *
              (((v + 1 : ℕ) : ℝ) * N / d) := by gcongr
        _ = A * (N : ℝ) ^ 2 *
            (((d.divisors.card : ℝ) ^ r) / (d : ℝ) ^ 2) := by
          dsimp [A]
          ring
    _ = A * (N : ℝ) ^ 2 *
          (∑ d ∈ D, ((d.divisors.card : ℝ) ^ r) / (d : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ A * (N : ℝ) ^ 2 * T := by
      gcongr
      exact hsum.sum_le_tsum D (fun d hd => by positivity)
    _ ≤ (1 + A * T) * (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (N : ℝ)]

/-- All fixed positive integer moments of the shifted gcd divisor count are bounded (codex2,
95%).  Dominate `τ(gcd)^r` by `Σ_{d ∣ gcd} τ(d)^r`, count simultaneous divisibility
(`≤ 9/d²`), and sum `Σ τ(d)^r/d² < ∞`. -/
theorem shifted_gcd_divisor_moment (u v r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r)) ≤ C * (N : ℝ)^2 := by
  sorry

noncomputable def weylMean (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^n * (x : ℂ))) / N

/-! ### Natural-index Bernoulli characteristic functions

The corresponding lemmas in `RandomLambertMoment` are indexed by primes.  The Erdős--Borwein
series uses every positive integer, represented here by the injective index map `m ↦ m + 1`.
The proofs below deliberately keep that shift visible, so later good-modulus products can be
stated directly in terms of the frozen `BernoulliLawNat` and `ebLambert` definitions. -/

open NormalNumbers.RandomLambertMoment

/-- The positive-integer Lambert denominators form a summable family. -/
theorem summable_ebLambert_denom (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun m : ℕ => (1 : ℝ) / ((b : ℝ) ^ (m + 1) - 1)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hgeom : Summable (fun m : ℕ => 2 * (1 / (b : ℝ)) ^ (m + 1)) := by
    exact ((summable_geometric_of_lt_one (by positivity)
      (by simpa using one_div_lt_one_div_of_lt zero_lt_one hb1)).mul_left 2).comp_injective
        Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun m => by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (one_le_pow₀ hb1.le))) (fun m => ?_) hgeom
  have hpow : (2 : ℝ) ≤ (b : ℝ) ^ (m + 1) := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ (m + 1) := pow_le_pow_right₀ hb1.le (by omega)
  have hden : 0 < (b : ℝ) ^ (m + 1) - 1 := by linarith
  have hbpowpos : (0 : ℝ) < (b : ℝ) ^ (m + 1) := by positivity
  calc
    1 / ((b : ℝ) ^ (m + 1) - 1) ≤ 2 / (b : ℝ) ^ (m + 1) := by
      rw [div_le_div_iff₀ hden hbpowpos]
      nlinarith
    _ = 2 * (1 / (b : ℝ)) ^ (m + 1) := by
      rw [div_pow]
      simp only [one_pow]
      ring

/-- Every selected Erdős--Borwein subseries is absolutely summable. -/
theorem summable_ebLambert_terms (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} (X : ℕ → Ω → Bool) (w : Ω) :
    Summable (fun m : ℕ =>
      (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) := by
  apply (summable_ebLambert_denom b hb).of_norm_bounded
  intro m
  have hbR : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden : 0 < (b : ℝ) ^ (m + 1) - 1 :=
    sub_pos.mpr (one_lt_pow₀ hbR (by omega))
  split_ifs <;> simp only [norm_div, Real.norm_eq_abs, abs_one, abs_zero, zero_div]
  · rw [abs_of_pos hden]
  · exact div_nonneg (by norm_num) hden.le

/-- The natural-index Erdős--Borwein random series is measurable. -/
theorem measurable_ebLambert (b : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) :
    Measurable (ebLambert b X) := by
  unfold ebLambert
  exact Measurable.tsum fun m => by
    have hm : Measurable (fun w => if X (m + 1) w then (1 : ℝ) else 0) :=
      (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX (m + 1))
    exact hm.div_const _

/-- The characteristic function of one natural-index Bernoulli coordinate. -/
theorem integral_ePh_bernoulli_nat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (delta : ℕ → ℝ)
    (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X) (m : ℕ) (θ : ℝ) :
    (∫ w, ePh (if X m w then θ else 0) ∂μ) =
      ((1 - delta m : ℝ) : ℂ) + (delta m : ℂ) * ePh θ := by
  let A : Set Ω := {w | X m w = true}
  have hA : MeasurableSet A := (hX.2.1 m) (measurableSet_singleton true)
  have hdelta0 : 0 ≤ delta m := (hX.1 m).1
  have hreal : μ.real A = delta m := by
    rw [measureReal_def, hX.2.2.2 m, ENNReal.toReal_ofReal hdelta0]
  have hfun : (fun w => ePh (if X m w then θ else 0)) =
      fun w => A.indicator (fun _ => ePh θ - 1) w + 1 := by
    funext w
    by_cases hw : X m w = true
    · simp [A, hw]
    · have hw' : X m w = false := Bool.eq_false_of_not_eq_true hw
      simp [A, hw, hw', ePh]
  rw [hfun, integral_add]
  · rw [integral_indicator_const _ hA, integral_const, hreal]
    have huniv : μ.real Set.univ = 1 := by simp [measureReal_def]
    rw [huniv]
    simp only [one_smul]
    push_cast
    rw [Complex.real_smul]
    ring
  · exact (integrable_const _).indicator hA
  · exact integrable_const _

/-- Independence factorizes a finite set of positive-integer coordinates. -/
theorem integral_ePh_finset_eb {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (G : Finset ℕ) (a : ℝ) :
    (∫ w, ePh (a * ∑ m ∈ G,
        (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) ∂μ) =
      ∏ m ∈ G, (((1 - delta (m + 1) : ℝ) : ℂ) +
        (delta (m + 1) : ℂ) * ePh (a / ((b : ℝ) ^ (m + 1) - 1))) := by
  classical
  let Y : G → Ω → ℂ := fun m w =>
    ePh (if X (m.1 + 1) w then a / ((b : ℝ) ^ (m.1 + 1) - 1) else 0)
  have hI : iIndepFun (fun m : G => X (m.1 + 1)) μ :=
    iIndepFun.precomp (Nat.succ_injective.comp Subtype.val_injective) hX.2.2.1
  have hprod := hI.integral_fun_prod_comp
    (fun m => (hX.2.1 (m.1 + 1)).aemeasurable)
    (fun m => (measurable_of_finite (f := fun z : Bool =>
      ePh (if z then a / ((b : ℝ) ^ (m.1 + 1) - 1) else 0))).aestronglyMeasurable)
  have hpoint (w : Ω) :
      ePh (a * ∑ m ∈ G,
          (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) =
        ∏ m : G, Y m w := by
    rw [Finset.mul_sum]
    rw [show (∑ m ∈ G, a * ((if X (m + 1) w then (1 : ℝ) else 0) /
        ((b : ℝ) ^ (m + 1) - 1))) =
        ∑ m : G, (if X (m.1 + 1) w then a / ((b : ℝ) ^ (m.1 + 1) - 1) else 0) by
      calc
        _ = ∑ m : G, a * ((if X (m.1 + 1) w then (1 : ℝ) else 0) /
            ((b : ℝ) ^ (m.1 + 1) - 1)) :=
          Finset.sum_subtype G (p := fun m : ℕ => m ∈ G) (by simp) _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro m hm
          split_ifs <;> ring]
    unfold ePh Y
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    rfl
  rw [show (∫ w, ePh (a * ∑ m ∈ G,
      (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) ∂μ) =
      ∫ w, ∏ m : G, Y m w ∂μ by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint]
  rw [hprod]
  calc
    (∏ m : G, ∫ w, Y m w ∂μ) =
        ∏ m ∈ G, ∫ w, ePh (if X (m + 1) w then
          a / ((b : ℝ) ^ (m + 1) - 1) else 0) ∂μ := by
      rw [Finset.prod_subtype G (p := fun m : ℕ => m ∈ G) (by simp)]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro m hm
      exact integral_ePh_bernoulli_nat μ delta X hX (m + 1) _

/-- Moduli of the finite natural-index characteristic factors are `bernMod` products. -/
theorem norm_integral_ePh_finset_eb {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (G : Finset ℕ) (a : ℝ) :
    ‖∫ w, ePh (a * ∑ m ∈ G,
        (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) ∂μ‖ =
      ∏ m ∈ G, bernMod (delta (m + 1)) (a / ((b : ℝ) ^ (m + 1) - 1)) := by
  rw [integral_ePh_finset_eb μ b delta X hX G a, norm_prod]
  simp only [bernMod]

/-- Initial positive-integer truncations converge to the full Erdős--Borwein subseries. -/
theorem tendsto_sum_range_ebLambert (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} (X : ℕ → Ω → Bool) (w : Ω) :
    Tendsto (fun M => ∑ m ∈ Finset.range M,
      (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) atTop
      (𝓝 (ebLambert b X w)) := by
  exact (summable_ebLambert_terms b hb X w).hasSum.tendsto_sum_nat

theorem measurable_ebLambert_finset_sum (b : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (G : Finset ℕ) :
    Measurable (fun w => ∑ m ∈ G,
      (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) := by
  apply Finset.measurable_sum
  intro m hm
  have hmeas : Measurable (fun w => if X (m + 1) w then (1 : ℝ) else 0) :=
    (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX (m + 1))
  exact hmeas.div_const _

/-- The full natural-index characteristic function is bounded by the product over any finite
set of selected positive-integer coordinates. -/
theorem norm_integral_ePh_ebLambert_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (F : Finset ℕ) (a : ℝ) :
    ‖∫ w, ePh (a * ebLambert b X w) ∂μ‖ ≤
      ∏ m ∈ F, bernMod (delta (m + 1)) (a / ((b : ℝ) ^ (m + 1) - 1)) := by
  let Z : ℕ → Ω → ℂ := fun M w => ePh (a * ∑ m ∈ Finset.range M,
    (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1))
  have hZm : ∀ M, AEStronglyMeasurable (Z M) μ := by
    intro M
    exact (continuous_ePh.measurable.comp
      (measurable_const.mul (measurable_ebLambert_finset_sum b X hX.2.1 _))).aestronglyMeasurable
  have hbound : ∀ M, ∀ᵐ w ∂μ, ‖Z M w‖ ≤ (1 : ℝ) := by
    intro M
    exact Filter.Eventually.of_forall fun w => (norm_ePh _).le
  have hlim : ∀ᵐ w ∂μ, Tendsto (fun M => Z M w) atTop
      (𝓝 (ePh (a * ebLambert b X w))) := by
    apply Filter.Eventually.of_forall
    intro w
    exact continuous_ePh.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (tendsto_sum_range_ebLambert b hb X w))
  have hint := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    hZm (integrable_const 1) hbound hlim
  have hnorm : Tendsto (fun M => ‖∫ w, Z M w ∂μ‖) atTop
      (𝓝 ‖∫ w, ePh (a * ebLambert b X w) ∂μ‖) :=
    (continuous_norm.tendsto _).comp hint
  apply le_of_tendsto hnorm
  have hcof : ∀ᶠ M in atTop, F ⊆ Finset.range M := by
    filter_upwards [eventually_ge_atTop ((F.sup id) + 1)] with M hM
    intro m hm
    rw [Finset.mem_range]
    have hle : m ≤ F.sup id := Finset.le_sup (f := id) hm
    omega
  filter_upwards [hcof] with M hFM
  rw [norm_integral_ePh_finset_eb μ b delta X hX (Finset.range M) a]
  apply Finset.prod_le_prod_of_subset_of_le_one hFM
  · intro m hm
    exact bernMod_nonneg _ _
  · intro m hm hmF
    exact bernMod_le_one (hX.1 (m + 1)).1 (hX.1 (m + 1)).2 _

/-- A deterministic translate contributes only a unit factor to the full characteristic norm. -/
theorem norm_integral_ePh_add_ebLambert_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (F : Finset ℕ) (u a : ℝ) :
    ‖∫ w, ePh (u + a * ebLambert b X w) ∂μ‖ ≤
      ∏ m ∈ F, bernMod (delta (m + 1)) (a / ((b : ℝ) ^ (m + 1) - 1)) := by
  have hpoint (w : Ω) :
      ePh (u + a * ebLambert b X w) = ePh u * ePh (a * ebLambert b X w) := ePh_add _ _
  rw [show (∫ w, ePh (u + a * ebLambert b X w) ∂μ) =
      ∫ w, ePh u * ePh (a * ebLambert b X w) ∂μ by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint]
  rw [integral_const_mul, norm_mul, norm_ePh, one_mul]
  exact norm_integral_ePh_ebLambert_le μ b hb delta X hX F a

/-- Finite even moments reduce to an average of Bernoulli characteristic moduli.  This is the
natural-index analogue of `RandomLambertMoment.moment_le_tupleAvg`; no complementary infinite
random sum remains after this lemma. -/
theorem ebMoment_le_tupleAvg (b : ℕ) (hb : 2 ≤ b) (h : ℤ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (F : Finset ℕ) (k N : ℕ) (hN : 1 ≤ N) (c : ℝ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
      (∑ n : Fin (2 * k) → Fin N,
          ∏ m ∈ F, bernMod (delta (m + 1))
            (tuplePhase b h k (m + 1) (fun i => (n i).val))) /
        (N : ℝ) ^ (2 * k) := by
  classical
  let A : (Fin (2 * k) → Fin N) → Ω → ℂ := fun n w =>
    ePh ((h : ℝ) * tuplePowerSum b k (fun i => (n i).val) *
      (c + (s : ℝ) * ebLambert b X w))
  have hY : Measurable (ebLambert b X) := measurable_ebLambert b X hX.2.1
  have hAmeas (n : Fin (2 * k) → Fin N) : Measurable (A n) := by
    dsimp [A]
    exact continuous_ePh.measurable.comp
      (measurable_const.mul (measurable_const.add (measurable_const.mul hY)))
  have hAint (n : Fin (2 * k) → Fin N) : Integrable (A n) μ := by
    apply Integrable.of_bound (hAmeas n).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun w => (norm_ePh _).le
  have hpoint (w : Ω) :
      ((‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^ (2 * k) : ℝ) : ℂ) =
        (∑ n : Fin (2 * k) → Fin N, A n w) / (N : ℂ) ^ (2 * k) := by
    exact weylMean_even_expansion b h k N hN _
  have hint :
      (((∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^
          (2 * k) ∂μ) : ℝ) : ℂ) =
        (∑ n : Fin (2 * k) → Fin N, ∫ w, A n w ∂μ) / (N : ℂ) ^ (2 * k) := by
    calc
      (((∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^
          (2 * k) ∂μ) : ℝ) : ℂ) =
          ∫ w, ((‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^
            (2 * k) : ℝ) : ℂ) ∂μ :=
        (integral_complex_ofReal (μ := μ)).symm
      _ = ∫ w, (∑ n : Fin (2 * k) → Fin N, A n w) /
          (N : ℂ) ^ (2 * k) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (∑ n : Fin (2 * k) → Fin N, ∫ w, A n w ∂μ) /
          (N : ℂ) ^ (2 * k) := by
        rw [integral_div, integral_finsetSum Finset.univ (fun n _ => hAint n)]
  have hchar (n : Fin (2 * k) → Fin N) :
      ‖∫ w, A n w ∂μ‖ ≤
        ∏ m ∈ F, bernMod (delta (m + 1))
          (tuplePhase b h k (m + 1) (fun i => (n i).val)) := by
    let q : ℝ := tuplePowerSum b k (fun i => (n i).val)
    have hrewrite (w : Ω) :
        A n w = ePh ((h : ℝ) * q * c +
          ((s : ℝ) * (h : ℝ) * q) * ebLambert b X w) := by
      dsimp [A, q]
      congr 1
      ring
    calc
      ‖∫ w, A n w ∂μ‖ =
          ‖∫ w, ePh ((h : ℝ) * q * c +
            ((s : ℝ) * (h : ℝ) * q) * ebLambert b X w) ∂μ‖ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hrewrite
      _ ≤ ∏ m ∈ F, bernMod (delta (m + 1))
          (((s : ℝ) * (h : ℝ) * q) / ((b : ℝ) ^ (m + 1) - 1)) :=
        norm_integral_ePh_add_ebLambert_le μ b hb delta X hX F
          ((h : ℝ) * q * c) ((s : ℝ) * (h : ℝ) * q)
      _ = ∏ m ∈ F, bernMod (delta (m + 1))
          (tuplePhase b h k (m + 1) (fun i => (n i).val)) := by
        apply Finset.prod_congr rfl
        intro m hm
        exact bernMod_signed_tuplePowerSum b h k (m + 1) (fun i => (n i).val)
          (delta (m + 1)) s hs
  have hnonneg : 0 ≤
      ∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^ (2 * k) ∂μ :=
    integral_nonneg fun w => by positivity
  have hden : 0 ≤ (N : ℝ) ^ (2 * k) := by positivity
  calc
    (∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^
        (2 * k) ∂μ) =
        ‖(((∫ w, ‖weylMean b h (c + (s : ℝ) * ebLambert b X w) N‖ ^
          (2 * k) ∂μ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖(∑ n : Fin (2 * k) → Fin N, ∫ w, A n w ∂μ) /
          (N : ℂ) ^ (2 * k)‖ := by rw [hint]
    _ = ‖∑ n : Fin (2 * k) → Fin N, ∫ w, A n w ∂μ‖ /
          (N : ℝ) ^ (2 * k) := by
      rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ (∑ n : Fin (2 * k) → Fin N, ‖∫ w, A n w ∂μ‖) /
          (N : ℝ) ^ (2 * k) :=
      div_le_div_of_nonneg_right (norm_sum_le Finset.univ _) hden
    _ ≤ (∑ n : Fin (2 * k) → Fin N,
          ∏ m ∈ F, bernMod (delta (m + 1))
            (tuplePhase b h k (m + 1) (fun i => (n i).val))) /
          (N : ℝ) ^ (2 * k) := by
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun n _ => hchar n) hden

/-- The summable moment bound behind `ebRandom_ae_normal_below_ln2` (codex2, 95%).
1. With `α ln 2 > a`, fix `k` and `q < Q(α)` with `kq > 1`.
2. The event that all coordinates have poor mass has probability `p_N^{2k} = O((log N)^{-2kq})`.
3. Shared-divisor loss decays at every log-power, by `shifted_gcd_divisor_moment` and Markov at
   `R > 2kq/η`.
4. The remaining tuples contract by `exp(-c_b (log N)^η)`. -/
@[blueprint (title := "Divisor moments yield summable Weyl bounds below log 2")]
theorem eb_weyl_moment_decay (hHR : HardyRamanujanLowerTail)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a c : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m))
    (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ q C : ℝ, 2 < q ∧ 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∫ w, ‖weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        C * Real.rpow (Real.log N) (-q) := by
  sorry

/-- **Conditional headline** (new companion, 2026-10-12; the frozen unconditional
`ebRandom_ae_normal_below_ln2` is NOT weakened).  Identical conclusion, plus the named literature
input `HardyRamanujanLowerTail`.  Proof:
1. `eb_weyl_moment_decay` gives, for each `b, h ≠ 0`, a fixed `k` and `q > 2` with
   `E|A_N|^{2k} ≤ C (log N)^{-q}`.
2. Markov at each rational `ε > 0`, then Borel–Cantelli along `N_j = ⌊exp √j⌋`
   (`Σ j^{-q/2} < ∞`).
3. Interpolate: `|A_N - A_{N_j}| ≤ 2(N - N_j)/N` and `N_{j+1}/N_j → 1`.
4. Take a countable intersection over `b, h, ε`, then Weyl → normality
   (`NormalNumbers.isNormal_of_weylAvg`, QSpanCriterion). -/
theorem ebRandom_ae_normal_below_ln2_of_HR (hHR : HardyRamanujanLowerTail)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a c : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinPositive
