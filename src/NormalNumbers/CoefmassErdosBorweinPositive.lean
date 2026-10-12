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
open ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction.zeta

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

/-! ### The shifted Hardy--Ramanujan input -/

/-- The Hardy--Ramanujan lower-tail exponent is positive strictly below its mean. -/
theorem hardyRamanujanExponent_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < 1 - α + α * Real.log α := by
  nlinarith [Real.self_sub_one_lt_mul_log hα0.le hα1.ne]

/-- Choose the two strict margins used by the moment argument: a Hardy--Ramanujan exponent `q`
and a divisor-mass exponent `α log 2 - a`. -/
theorem exists_hardyRamanujan_parameters (a : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) :
    ∃ α q : ℝ, 0 < α ∧ α < 1 ∧ 0 < q ∧
      q < 1 - α + α * Real.log α ∧ 0 < α * Real.log 2 - a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let α := (a / Real.log 2 + 1) / 2
  have hdiv0 : 0 ≤ a / Real.log 2 := div_nonneg ha0 hlog2.le
  have hdiv1 : a / Real.log 2 < 1 := (div_lt_one hlog2).2 ha
  have hα0 : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hgap : 0 < α * Real.log 2 - a := by
    dsimp [α]
    field_simp
    linarith
  let Q := 1 - α + α * Real.log α
  have hQ : 0 < Q := hardyRamanujanExponent_pos hα0 hα1
  refine ⟨α, Q / 2, hα0, hα1, by positivity, ?_, hgap⟩
  dsimp [Q]
  linarith

/-- Hardy--Ramanujan remains valid for the zero-based shifted coordinates used by the Weyl
tuple expansion.  Enlarging the endpoint from `N` to `N + u` costs only the fixed factor
`u + 1`; the negative logarithmic power improves when the endpoint is enlarged. -/
theorem shifted_hardyRamanujanLowerTail (hHR : HardyRamanujanLowerTail)
    (u : ℕ) (hu : 1 ≤ u) (α q : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hq0 : 0 < q) (hq : q < 1 - α + α * Real.log α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (((Finset.univ : Finset (Fin N)).filter (fun n =>
        ((n.val + u).primeFactors.card : ℝ) ≤
          α * Real.log (Real.log ((N + u : ℕ) : ℝ)))).card : ℝ) ≤
        C * N * Real.rpow (Real.log N) (-q) := by
  obtain ⟨C, hC, hbound⟩ := hHR α hα0 hα1 q hq0 hq
  refine ⟨C * (u + 1), mul_pos hC (by positivity), ?_⟩
  intro N hN
  let A := (Finset.univ : Finset (Fin N)).filter (fun n =>
    ((n.val + u).primeFactors.card : ℝ) ≤
      α * Real.log (Real.log ((N + u : ℕ) : ℝ)))
  let B := (Finset.Icc 1 (N + u)).filter (fun n =>
    (n.primeFactors.card : ℝ) ≤
      α * Real.log (Real.log ((N + u : ℕ) : ℝ)))
  have hinj : Function.Injective (fun n : Fin N => n.val + u) := by
    intro x y hxy
    exact Fin.ext (Nat.add_right_cancel hxy)
  have himage : A.image (fun n => n.val + u) ⊆ B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
    rcases Finset.mem_filter.mp hn with ⟨_, hnpoor⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hnpoor⟩
  have hcard : (A.card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast (show A.card ≤ B.card by
      rw [← Finset.card_image_of_injective A hinj]
      exact Finset.card_le_card himage)
  have hNu : ((N + u : ℕ) : ℝ) ≤ ((u + 1 : ℕ) : ℝ) * N := by
    exact_mod_cast (show N + u ≤ (u + 1) * N by
      calc
        N + u ≤ N + u * N := Nat.add_le_add_left (Nat.le_mul_of_pos_right u (by omega)) N
        _ = (u + 1) * N := by ring)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogle : Real.log (N : ℝ) ≤ Real.log (N + u : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.le_add_right N u)
  have hrpow : Real.rpow (Real.log (N + u : ℕ)) (-q) ≤
      Real.rpow (Real.log N) (-q) :=
    Real.rpow_le_rpow_of_nonpos hlogN hlogle (by linarith)
  change (A.card : ℝ) ≤ _
  calc
    (A.card : ℝ) ≤ (B.card : ℝ) := hcard
    _ ≤ C * ((N + u : ℕ) : ℝ) * Real.rpow (Real.log (N + u : ℕ)) (-q) := by
      simpa only [B] using hbound (N + u) (by omega)
    _ ≤ C * (((u + 1 : ℕ) : ℝ) * N) *
        Real.rpow (Real.log (N + u : ℕ)) (-q) := by
      have hrpow0 : 0 ≤ Real.rpow (Real.log (N + u : ℕ)) (-q) :=
        Real.rpow_nonneg (by positivity) _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNu hC.le) hrpow0
    _ ≤ C * (((u + 1 : ℕ) : ℝ) * N) * Real.rpow (Real.log N) (-q) := by
      exact mul_le_mul_of_nonneg_left hrpow (mul_nonneg hC.le (by positivity))
    _ = (C * (u + 1)) * N * Real.rpow (Real.log N) (-q) := by
      push_cast
      ring

/-- Outside the Hardy--Ramanujan exceptional set, the squarefree-divisor supply has the
advertised logarithmic power.  This is the exact real-power conversion used before subtracting
the fixed cutoff and the collision loss. -/
theorem log_rpow_lt_two_pow_primeFactors (M n : ℕ) (α : ℝ) (hM : 3 ≤ M)
    (hrich : α * Real.log (Real.log M) < (n.primeFactors.card : ℝ)) :
    Real.rpow (Real.log M) (α * Real.log 2) <
      ((2 ^ n.primeFactors.card : ℕ) : ℝ) := by
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := mul_lt_mul_of_pos_right hrich hlog2
  rw [Nat.cast_pow, Real.rpow_eq_pow, ← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hlogM,
    Real.rpow_def_of_pos (x := ((2 : ℕ) : ℝ)) (by norm_num)]
  apply Real.exp_lt_exp.mpr
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

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

/-! ### Divisor-series summability -/

/-- On prime powers, the `r`-th power of the divisor count is bounded by the coefficient of
the `2 ^ r`-fold Dirichlet convolution of the arithmetic zeta function. -/
theorem divisorCard_pow_le_zetaPow_primePow (r e : ℕ) {p : ℕ} (hp : p.Prime) :
    (e + 1) ^ r ≤ ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ e) := by
  induction r generalizing e with
  | zero =>
      simp [ArithmeticFunction.zeta_apply_ne (pow_ne_zero e hp.ne_zero)]
  | succ r ih =>
      have htwo : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
      rw [htwo]
      rw [show (ζ : ArithmeticFunction ℕ) ^ (2 ^ r + 2 ^ r) =
          (ζ : ArithmeticFunction ℕ) ^ (2 ^ r) *
            (ζ : ArithmeticFunction ℕ) ^ (2 ^ r) by rw [pow_add]]
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b =>
          ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) a *
            ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) b),
        Nat.sum_divisors_prime_pow hp]
      calc
        (e + 1) ^ (r + 1) = ∑ j ∈ Finset.range (e + 1), (e + 1) ^ r := by
          simp [pow_succ, Nat.mul_comm]
        _ ≤ ∑ j ∈ Finset.range (e + 1),
            ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ j) *
              ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ e / p ^ j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hje : j ≤ e := by simpa using Finset.mem_range.mp hj
          have hbase : e + 1 ≤ (j + 1) * (e - j + 1) := by
            have hsplit : j + (e - j) = e := Nat.add_sub_of_le hje
            nlinarith [Nat.zero_le (j * (e - j))]
          calc
            (e + 1) ^ r ≤ ((j + 1) * (e - j + 1)) ^ r :=
              Nat.pow_le_pow_left hbase r
            _ = (j + 1) ^ r * (e - j + 1) ^ r := by rw [mul_pow]
            _ ≤ ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ j) *
                ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ (e - j)) :=
              Nat.mul_le_mul (ih j) (ih (e - j))
            _ = ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ j) *
                ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) (p ^ e / p ^ j) := by
              rw [Nat.pow_div hje hp.pos]
        _ = _ := rfl

/-- The divisor-count domination extends from prime powers to every natural number. -/
theorem divisorCard_pow_le_zetaPow (n r : ℕ) (hr : 1 ≤ r) :
    n.divisors.card ^ r ≤ ((ζ : ArithmeticFunction ℕ) ^ (2 ^ r)) n := by
  by_cases hn : n = 0
  · subst n
    simp [show r ≠ 0 by omega]
  · rw [Nat.card_divisors hn, ← Finset.prod_pow]
    rw [(isMultiplicative_zeta.pow).multiplicative_factorization _ hn]
    apply Finset.prod_le_prod'
    intro p hp
    exact divisorCard_pow_le_zetaPow_primePow r (n.factorization p)
      (Nat.prime_of_mem_primeFactors hp)

/-- Casting the coefficients of a convolution power of zeta commutes with evaluation. -/
theorem natCast_zetaPow_apply (k n : ℕ) :
    ((((ζ : ArithmeticFunction ℕ) ^ k) n : ℕ) : ℂ) =
      ((ζ : ArithmeticFunction ℂ) ^ k) n := by
  induction k generalizing n with
  | zero => simp [ArithmeticFunction.one_apply]
  | succ k ih =>
      rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih]
      simp only [ArithmeticFunction.natCoe_apply]

/-- Every positive convolution power of zeta has summable coefficients after division by `n²`. -/
theorem summable_zetaPow_div_sq (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ =>
      (((((ζ : ArithmeticFunction ℕ) ^ k) n : ℕ) : ℝ) / (n : ℝ) ^ 2)) := by
  let Z : ArithmeticFunction ℂ := (ζ : ArithmeticFunction ℂ)
  have hZ : LSeriesSummable (Z ·) (2 : ℂ) := by
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by norm_num)
  have hpow : ∀ j : ℕ, LSeriesSummable ((Z ^ (j + 1)) ·) (2 : ℂ) := by
    intro j
    induction j with
    | zero => simpa using hZ
    | succ j ih =>
        rw [show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
        exact ArithmeticFunction.LSeriesSummable_mul ih hZ
  have hk' : k - 1 + 1 = k := by omega
  have hseries : LSeriesSummable ((Z ^ k) ·) (2 : ℂ) := by
    rw [← hk']
    exact hpow (k - 1)
  refine hseries.norm.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    congr 1
    rw [show (Z ^ k) n =
        (((((ζ : ArithmeticFunction ℕ) ^ k) n : ℕ) : ℂ)) by
      simpa [Z] using (natCast_zetaPow_apply k n).symm]
    simp
    norm_num

/-- The divisor-count Dirichlet series needed by the shifted gcd moment is summable. -/
theorem summable_divisorCard_pow_div_sq (r : ℕ) (hr : 1 ≤ r) :
    Summable (fun n : ℕ => ((n.divisors.card : ℝ) ^ r) / (n : ℝ) ^ 2) := by
  apply (summable_zetaPow_div_sq (2 ^ r) (one_le_pow₀ (by omega))).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    gcongr
    exact_mod_cast divisorCard_pow_le_zetaPow n r hr

/-- All fixed positive integer moments of the shifted gcd divisor count are bounded (codex2,
95%).  Dominate `τ(gcd)^r` by `Σ_{d ∣ gcd} τ(d)^r`, count simultaneous divisibility
(`≤ 9/d²`), and sum `Σ τ(d)^r/d² < ∞`. -/
theorem shifted_gcd_divisor_moment (u v r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (((Nat.gcd (n + u) (m + v)).divisors.card : ℝ) ^ r)) ≤ C * (N : ℝ)^2 := by
  exact shifted_gcd_divisor_moment_of_summable u v r
    (summable_divisorCard_pow_div_sq r hr)

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

/-! ### Good moduli and their Bernoulli contraction -/

/-- The moduli anchored at coordinate `i` and separated from the last `K` residue classes of
every other coordinate. -/
def tupleGoodModuli (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k)) : Finset ℕ :=
  (n i + a₀).divisors.filter fun p =>
    P₀ < p ∧ ∀ j, j ≠ i → n j % p < p - K

theorem mem_tupleGoodModuli {a₀ K P₀ k p : ℕ} {n : Fin (2 * k) → ℕ}
    {i : Fin (2 * k)} (ha₀ : 1 ≤ a₀) :
      p ∈ tupleGoodModuli a₀ K P₀ k n i ↔
      p ∣ n i + a₀ ∧ P₀ < p ∧ ∀ j, j ≠ i → n j % p < p - K := by
  rw [tupleGoodModuli, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hp, _⟩, hP, hsep⟩
    exact ⟨hp, hP, hsep⟩
  · rintro ⟨hp, hP, hsep⟩
    exact ⟨⟨hp, by omega⟩, hP, hsep⟩

/-- A modulus excluded by another coordinate's last `K` residue classes divides one of the
shifted gcds used in the moment estimate. -/
theorem bad_modulus_dvd_shifted_gcd {a₀ K k p : ℕ} {n : Fin (2 * k) → ℕ}
    {i : Fin (2 * k)} (hpK : K < p) (hpi : p ∣ n i + a₀)
    (hbad : ¬ ∀ j, j ≠ i → n j % p < p - K) :
    ∃ j, j ≠ i ∧ ∃ r ∈ Finset.Icc 1 K,
      p ∣ Nat.gcd (n i + a₀) (n j + r) := by
  push Not at hbad
  obtain ⟨j, hji, hj⟩ := hbad
  let r := p - n j % p
  have hp0 : 0 < p := by omega
  have hmodlt : n j % p < p := Nat.mod_lt _ hp0
  have hr1 : 1 ≤ r := by dsimp [r]; omega
  have hrK : r ≤ K := by dsimp [r]; omega
  have hpjr : p ∣ n j + r := by
    refine ⟨n j / p + 1, ?_⟩
    have hdecomp := Nat.mod_add_div (n j) p
    calc
      n j + r = (n j % p + p * (n j / p)) + (p - n j % p) := by
        rw [hdecomp]
      _ = p * (n j / p) + p := by omega
      _ = p * (n j / p + 1) := by rw [Nat.mul_add, Nat.mul_one]
  exact ⟨j, hji, r, Finset.mem_Icc.mpr ⟨hr1, hrK⟩, Nat.dvd_gcd hpi hpjr⟩

/-- The divisors anchored at `i` that fail separation from another coordinate. -/
def tupleBadModuli (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k)) : Finset ℕ :=
  (n i + a₀).divisors.filter fun p =>
    P₀ < p ∧ ¬ ∀ j, j ≠ i → n j % p < p - K

/-- The finite pool of shifted-gcd divisors that contains every bad anchored modulus. -/
def shiftedGcdDivisorPool (a₀ K k : ℕ) (n : Fin (2 * k) → ℕ)
    (i : Fin (2 * k)) : Finset ℕ :=
  (Finset.univ.erase i).biUnion fun j =>
    (Finset.Icc 1 K).biUnion fun r => (Nat.gcd (n i + a₀) (n j + r)).divisors

/-- The number of moduli lost to coordinate collisions is bounded by the advertised finite sum
of shifted-gcd divisor counts. -/
theorem card_tupleBadModuli_le (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ)
    (i : Fin (2 * k)) (ha₀ : 1 ≤ a₀) (hKP : K ≤ P₀) :
    (tupleBadModuli a₀ K P₀ k n i).card ≤
      ∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
        (Nat.gcd (n i + a₀) (n j + r)).divisors.card := by
  have hsubset : tupleBadModuli a₀ K P₀ k n i ⊆
      shiftedGcdDivisorPool a₀ K k n i := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpdiv, hPp, hbad⟩
    have hpK : K < p := lt_of_le_of_lt hKP hPp
    obtain ⟨j, hji, r, hr, hpgcd⟩ :=
      bad_modulus_dvd_shifted_gcd hpK (Nat.dvd_of_mem_divisors hpdiv) hbad
    rw [shiftedGcdDivisorPool, Finset.mem_biUnion]
    refine ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨r, hr, ?_⟩
    exact Nat.mem_divisors.mpr ⟨hpgcd,
      (Nat.gcd_pos_of_pos_left _ (by omega)).ne'⟩
  calc
    (tupleBadModuli a₀ K P₀ k n i).card ≤
        (shiftedGcdDivisorPool a₀ K k n i).card := Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        ((Finset.Icc 1 K).biUnion fun r =>
          (Nat.gcd (n i + a₀) (n j + r)).divisors).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
        (Nat.gcd (n i + a₀) (n j + r)).divisors.card := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.card_biUnion_le

/-! ### High moments of the tuple collision loss -/

/-- Split a function at two distinct coordinates, retaining all remaining coordinates as a
separate function. -/
def piSplitTwoEquiv {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    (ι → β) ≃ (β × β) × ({l : ι // l ≠ i ∧ l ≠ j} → β) where
  toFun n := ((n i, n j), fun l => n l)
  invFun z l := if hli : l = i then z.1.1 else if hlj : l = j then z.1.2
    else z.2 ⟨l, hli, hlj⟩
  left_inv n := by
    funext l
    by_cases hli : l = i
    · subst l
      simp
    · by_cases hlj : l = j
      · subst l
        simp [hli]
      · simp [hli, hlj]
  right_inv z := by
    rcases z with ⟨⟨x, y⟩, r⟩
    apply Prod.ext
    · apply Prod.ext <;> simp [Ne.symm hij]
    · funext l
      simp [l.2.1, l.2.2]

/-- Removing two distinct coordinates reduces the cardinality by two. -/
theorem card_piSplitTwo_remainder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    Fintype.card {l : ι // l ≠ i ∧ l ≠ j} = Fintype.card ι - 2 := by
  let e : {l : ι // l ≠ i ∧ l ≠ j} ≃ {l : ι // ¬ (l = i ∨ l = j)} :=
    Equiv.subtypeEquivRight (fun l => not_or.symm)
  calc
    Fintype.card {l : ι // l ≠ i ∧ l ≠ j} =
        Fintype.card {l : ι // ¬ (l = i ∨ l = j)} := Fintype.card_congr e
    _ = Fintype.card ι - Fintype.card {l : ι // l = i ∨ l = j} :=
      Fintype.card_subtype_compl (fun l : ι => l = i ∨ l = j)
    _ = Fintype.card ι - 2 := by rw [Fintype.card_subtype_eq_or_eq_of_ne hij]

/-- A sum over all functions whose summand sees only two distinct coordinates factors as the
two-coordinate sum times the number of assignments to the remaining coordinates. -/
theorem sum_pair_over_pi {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (i j : ι) (hij : i ≠ j) (f : β → β → ℝ) :
    (∑ n : ι → β, f (n i) (n j)) =
      (Fintype.card β : ℝ) ^ (Fintype.card ι - 2) * ∑ x : β, ∑ y : β, f x y := by
  let e := piSplitTwoEquiv (β := β) i j hij
  rw [Fintype.sum_equiv e (fun n => f (n i) (n j))
    (fun z => f z.1.1 z.1.2) (fun n => rfl)]
  rw [Fintype.sum_prod_type]
  have hcard : Fintype.card ({l : ι // l ≠ i ∧ l ≠ j} → β) =
      Fintype.card β ^ (Fintype.card ι - 2) := by
    rw [Fintype.card_fun, card_piSplitTwo_remainder i j hij]
  simp_rw [Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul]
  rw [show (Finset.univ : Finset ({l : ι // l ≠ i ∧ l ≠ j} → β)).card =
      Fintype.card β ^ (Fintype.card ι - 2) by simpa using hcard]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]

/-- The shifted-gcd moment bound in the zero-based `Fin N` coordinates used by the Weyl tuple
expansion. -/
theorem shifted_gcd_divisor_moment_fin (u v r : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ x : Fin N, ∑ y : Fin N,
        (((Nat.gcd (x.val + u) (y.val + v)).divisors.card : ℝ) ^ r)) ≤
          C * (N : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := shifted_gcd_divisor_moment (u - 1) (v - 1) r hr
  refine ⟨C, hC, fun N hN => ?_⟩
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hrewrite (x y : ℕ) :
      Nat.gcd (x + u) (y + v) = Nat.gcd (1 + x + (u - 1)) (1 + y + (v - 1)) := by
    congr 1 <;> omega
  calc
    (∑ x : Fin N, ∑ y : Fin N,
        (((Nat.gcd (x.val + u) (y.val + v)).divisors.card : ℝ) ^ r)) =
        ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
          (((Nat.gcd (x + u) (y + v)).divisors.card : ℝ) ^ r) := by
      rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin N,
        (((Nat.gcd (x + u) (y.val + v)).divisors.card : ℝ) ^ r)) N]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fin.sum_univ_eq_sum_range (fun y =>
        (((Nat.gcd (x + u) (y + v)).divisors.card : ℝ) ^ r)) N]
    _ = ∑ x ∈ Finset.Icc 1 N, ∑ y ∈ Finset.Icc 1 N,
          (((Nat.gcd (x + (u - 1)) (y + (v - 1))).divisors.card : ℝ) ^ r) := by
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hrewrite]
    _ ≤ C * (N : ℝ)^2 := hbound N hN

/-- A shifted-gcd summand depending on two tuple coordinates has total mass `O(N^(2k))` over
all `2k`-tuples. -/
theorem shifted_gcd_divisor_moment_over_tuples (a₀ v R k : ℕ) (hk : 1 ≤ k)
    (ha₀ : 1 ≤ a₀) (hv : 1 ≤ v) (hR : 1 ≤ R)
    (i j : Fin (2 * k)) (hij : i ≠ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n : Fin (2 * k) → Fin N,
        (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R)) ≤
          C * (N : ℝ) ^ (2 * k) := by
  obtain ⟨C, hC, hpair⟩ := shifted_gcd_divisor_moment_fin a₀ v R ha₀ hv hR
  refine ⟨C, hC, fun N hN => ?_⟩
  rw [sum_pair_over_pi i j hij (fun x y : Fin N =>
    (((Nat.gcd (x.val + a₀) (y.val + v)).divisors.card : ℝ) ^ R))]
  calc
    (Fintype.card (Fin N) : ℝ) ^ (Fintype.card (Fin (2 * k)) - 2) *
        (∑ x : Fin N, ∑ y : Fin N,
          (((Nat.gcd (x.val + a₀) (y.val + v)).divisors.card : ℝ) ^ R)) ≤
        (N : ℝ) ^ (2 * k - 2) * (C * (N : ℝ) ^ 2) := by
      simp only [Fintype.card_fin]
      gcongr
      exact hpair N hN
    _ = C * (N : ℝ) ^ (2 * k) := by
      calc
        (N : ℝ) ^ (2 * k - 2) * (C * (N : ℝ) ^ 2) =
            C * ((N : ℝ) ^ (2 * k - 2) * (N : ℝ) ^ 2) := by ring
        _ = C * (N : ℝ) ^ (2 * k) := by
          rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ 2 * k)]

/-- Jensen's inequality converts the collision pool bound into a pointwise bound for every
positive integral moment of its cardinality. -/
theorem card_tupleBadModuli_pow_le (a₀ K P₀ k R : ℕ)
    (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (ha₀ : 1 ≤ a₀) (hKP : K ≤ P₀) (hR : 1 ≤ R) :
    (((tupleBadModuli a₀ K P₀ k n i).card : ℝ) ^ R) ≤
      (((Finset.univ.erase i).card : ℝ) ^ (R - 1)) *
      (((Finset.Icc 1 K).card : ℝ) ^ (R - 1)) *
      (∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
        (((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ) ^ R)) := by
  have hcard := card_tupleBadModuli_le a₀ K P₀ k n i ha₀ hKP
  have hcardR : ((tupleBadModuli a₀ K P₀ k n i).card : ℝ) ≤
      ∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
        ((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ) := by
    exact_mod_cast hcard
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      ((tupleBadModuli a₀ K P₀ k n i).card : ℝ)) hcardR R
  calc
    (((tupleBadModuli a₀ K P₀ k n i).card : ℝ) ^ R) ≤
        (∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
          ((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ)) ^ R := hpow
    _ ≤ (((Finset.univ.erase i).card : ℝ) ^ (R - 1)) *
        ∑ j ∈ Finset.univ.erase i,
          (∑ r ∈ Finset.Icc 1 K,
            ((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ)) ^ R := by
      simpa only [Nat.sub_add_cancel hR] using
        (pow_sum_le_card_mul_sum_pow (s := Finset.univ.erase i)
          (f := fun j => ∑ r ∈ Finset.Icc 1 K,
            ((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ))
          (fun j hj => Finset.sum_nonneg fun r hr => by positivity) (R - 1))
    _ ≤ (((Finset.univ.erase i).card : ℝ) ^ (R - 1)) *
        ∑ j ∈ Finset.univ.erase i,
          (((Finset.Icc 1 K).card : ℝ) ^ (R - 1)) *
            ∑ r ∈ Finset.Icc 1 K,
              (((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ) ^ R) := by
      gcongr with j hj
      simpa only [Nat.sub_add_cancel hR] using
        (pow_sum_le_card_mul_sum_pow (s := Finset.Icc 1 K)
          (f := fun r => ((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ))
          (fun r hr => by positivity) (R - 1))
    _ = (((Finset.univ.erase i).card : ℝ) ^ (R - 1)) *
        (((Finset.Icc 1 K).card : ℝ) ^ (R - 1)) *
        (∑ j ∈ Finset.univ.erase i, ∑ r ∈ Finset.Icc 1 K,
          (((Nat.gcd (n i + a₀) (n j + r)).divisors.card : ℝ) ^ R)) := by
      simp_rw [Finset.mul_sum, mul_assoc]

/-- For every fixed anchor coordinate, every positive moment of the bad-modulus count is
uniformly bounded under the uniform measure on `2k`-tuples. -/
theorem tupleBadModuli_moment (a₀ K P₀ k R : ℕ) (hk : 1 ≤ k)
    (ha₀ : 1 ≤ a₀) (hK : 1 ≤ K) (hKP : K ≤ P₀) (hR : 1 ≤ R)
    (i : Fin (2 * k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n : Fin (2 * k) → Fin N,
        (((tupleBadModuli a₀ K P₀ k (fun j => (n j).val) i).card : ℝ) ^ R)) ≤
          C * (N : ℝ) ^ (2 * k) := by
  classical
  let J := Finset.univ.erase i
  let V := Finset.Icc 1 K
  choose C hC hbound using fun (j : J) (v : V) =>
    shifted_gcd_divisor_moment_over_tuples a₀ v R k hk ha₀
      (by
        have hv := v.2
        change v.val ∈ Finset.Icc 1 K at hv
        exact (Finset.mem_Icc.mp hv).1) hR i j
      (by
        have hj := j.2
        change j.val ∈ Finset.univ.erase i at hj
        exact (Finset.ne_of_mem_erase hj).symm)
  let A : ℝ := (J.card : ℝ) ^ (R - 1) * (V.card : ℝ) ^ (R - 1)
  let D : Fin (2 * k) → ℕ → ℝ := fun j v =>
    if hj : j ∈ J then if hv : v ∈ V then C ⟨j, hj⟩ ⟨v, hv⟩ else 0 else 0
  let S : ℝ := ∑ j ∈ J, ∑ v ∈ V, D j v
  refine ⟨1 + A * S, ?_, fun N hN => ?_⟩
  · have hA : 0 ≤ A := by dsimp [A]; positivity
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun v hv => by
        rw [show D j v = C ⟨j, hj⟩ ⟨v, hv⟩ by simp [D, hj, hv]]
        exact (hC ⟨j, hj⟩ ⟨v, hv⟩).le
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun v hv => by
      rw [show D j v = C ⟨j, hj⟩ ⟨v, hv⟩ by simp [D, hj, hv]]
      exact (hC ⟨j, hj⟩ ⟨v, hv⟩).le
  have hpoint (n : Fin (2 * k) → Fin N) :
      (((tupleBadModuli a₀ K P₀ k (fun j => (n j).val) i).card : ℝ) ^ R) ≤
        A * ∑ j ∈ J, ∑ v ∈ V,
          (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R) := by
    simpa only [J, V, A] using
        card_tupleBadModuli_pow_le a₀ K P₀ k R (fun j => (n j).val) i ha₀ hKP hR
  have hswap :
      (∑ n : Fin (2 * k) → Fin N, ∑ j ∈ J, ∑ v ∈ V,
        (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R)) =
      ∑ j ∈ J, ∑ v ∈ V, ∑ n : Fin (2 * k) → Fin N,
        (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R) := by
    rw [show (∑ n : Fin (2 * k) → Fin N, ∑ j ∈ J, ∑ v ∈ V,
        (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R)) =
        ∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)),
          ∑ j ∈ J, ∑ v ∈ V,
            (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R) by simp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  calc
    (∑ n : Fin (2 * k) → Fin N,
        (((tupleBadModuli a₀ K P₀ k (fun j => (n j).val) i).card : ℝ) ^ R)) ≤
        ∑ n : Fin (2 * k) → Fin N, A * ∑ j ∈ J, ∑ v ∈ V,
          (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R) :=
      Finset.sum_le_sum fun n _ => hpoint n
    _ = A * ∑ j ∈ J, ∑ v ∈ V, ∑ n : Fin (2 * k) → Fin N,
          (((Nat.gcd (n i + a₀) (n j + v)).divisors.card : ℝ) ^ R) := by
      rw [← Finset.mul_sum, hswap]
    _ ≤ A * ∑ j ∈ J, ∑ v ∈ V,
        D j v * (N : ℝ) ^ (2 * k) := by
      gcongr with j hj v hv
      rw [show D j v = C ⟨j, hj⟩ ⟨v, hv⟩ by simp [D, hj, hv]]
      exact hbound ⟨j, hj⟩ ⟨v, hv⟩ N hN
    _ = A * S * (N : ℝ) ^ (2 * k) := by
      dsimp [S]
      calc
        A * ∑ j ∈ J, ∑ v ∈ V, D j v * (N : ℝ) ^ (2 * k) =
            A * ((∑ j ∈ J, ∑ v ∈ V, D j v) * (N : ℝ) ^ (2 * k)) := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
        _ = (A * ∑ j ∈ J, ∑ v ∈ V, D j v) * (N : ℝ) ^ (2 * k) := by ring
    _ ≤ (1 + A * S) * (N : ℝ) ^ (2 * k) := by
      have hpow : 0 ≤ (N : ℝ) ^ (2 * k) := by positivity
      gcongr
      linarith

/-! ### The two finite exceptional sets

The moment proof partitions the tuple box into tuples all of whose coordinates lie in the
Hardy--Ramanujan lower tail, tuples with a rich coordinate but excessive collision loss, and the
remaining contracting tuples.  The next lemmas make the first two pieces exact finite objects.
-/

/-- The zero-based coordinates whose shifted prime-factor count lies in the Hardy--Ramanujan
lower tail at endpoint `N + u`. -/
noncomputable def poorCoordinates (u N : ℕ) (α : ℝ) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter fun n =>
    ((n.val + u).primeFactors.card : ℝ) ≤
      α * Real.log (Real.log ((N + u : ℕ) : ℝ))

/-- Tuples all of whose coordinates are in the shifted Hardy--Ramanujan lower tail. -/
noncomputable def poorTuples (u N k : ℕ) (α : ℝ) : Finset (Fin (2 * k) → Fin N) :=
  Fintype.piFinset fun _ : Fin (2 * k) ↦ poorCoordinates u N α

@[simp] theorem mem_poorTuples {u N k : ℕ} {α : ℝ}
    {n : Fin (2 * k) → Fin N} :
    n ∈ poorTuples u N k α ↔ ∀ i, n i ∈ poorCoordinates u N α := by
  simp [poorTuples]

/-- Independence of the tuple coordinates appears combinatorially as the exact power formula for
the all-poor exceptional set. -/
theorem card_poorTuples (u N k : ℕ) (α : ℝ) :
    (poorTuples u N k α).card = (poorCoordinates u N α).card ^ (2 * k) := by
  exact Fintype.card_piFinset_const _ _

/-- The shifted Hardy--Ramanujan estimate raises to the exact number of tuple coordinates. -/
theorem poorTuples_card_le_of_HR (hHR : HardyRamanujanLowerTail)
    (u k : ℕ) (hu : 1 ≤ u) (α q : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hq0 : 0 < q) (hq : q < 1 - α + α * Real.log α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ((poorTuples u N k α).card : ℝ) ≤
        (C * N * Real.rpow (Real.log N) (-q)) ^ (2 * k) := by
  obtain ⟨C, hC, hbound⟩ :=
    shifted_hardyRamanujanLowerTail hHR u hu α q hα0 hα1 hq0 hq
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  rw [card_poorTuples]
  push_cast
  exact pow_le_pow_left₀ (show 0 ≤ ((poorCoordinates u N α).card : ℝ) by positivity)
    (by simpa only [poorCoordinates] using hbound N hN) (2 * k)

/-- Tuples for which one fixed anchor loses at least `T` good moduli to coordinate collisions. -/
noncomputable def collisionHeavyTuples (a₀ K P₀ k N : ℕ) (i : Fin (2 * k)) (T : ℝ) :
    Finset (Fin (2 * k) → Fin N) :=
  (Finset.univ : Finset (Fin (2 * k) → Fin N)).filter fun n =>
    T ≤ ((tupleBadModuli a₀ K P₀ k (fun j ↦ (n j).val) i).card : ℝ)

/-- Finite Markov inequality for the collision-loss exceptional set at a fixed anchor. -/
theorem card_collisionHeavyTuples_mul_pow_le (a₀ K P₀ k R N : ℕ)
    (i : Fin (2 * k)) (T C : ℝ) (hT : 0 ≤ T)
    (hMoment :
      (∑ n : Fin (2 * k) → Fin N,
        (((tupleBadModuli a₀ K P₀ k (fun j ↦ (n j).val) i).card : ℝ) ^ R)) ≤
          C * (N : ℝ) ^ (2 * k)) :
    ((collisionHeavyTuples a₀ K P₀ k N i T).card : ℝ) * T ^ R ≤
      C * (N : ℝ) ^ (2 * k) := by
  calc
    ((collisionHeavyTuples a₀ K P₀ k N i T).card : ℝ) * T ^ R =
        ∑ _n ∈ collisionHeavyTuples a₀ K P₀ k N i T, T ^ R := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ collisionHeavyTuples a₀ K P₀ k N i T,
        (((tupleBadModuli a₀ K P₀ k (fun j ↦ (n j).val) i).card : ℝ) ^ R) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ hT (Finset.mem_filter.mp hn).2 R
    _ ≤ ∑ n : Fin (2 * k) → Fin N,
        (((tupleBadModuli a₀ K P₀ k (fun j ↦ (n j).val) i).card : ℝ) ^ R) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ by positivity
    _ ≤ C * (N : ℝ) ^ (2 * k) := hMoment

/-- The finite exceptional set: either every coordinate is Hardy--Ramanujan-poor, or at least one
anchor has collision loss at least `T`. -/
noncomputable def exceptionalTuples (u K P₀ k N : ℕ) (α T : ℝ) :
    Finset (Fin (2 * k) → Fin N) :=
  poorTuples u N k α ∪ (Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
    collisionHeavyTuples u K P₀ k N i T

/-- Outside the exceptional set there is a rich anchor whose collision loss is below `T`. -/
theorem exists_rich_light_anchor_of_not_mem_exceptional
    (u K P₀ k N : ℕ) (α T : ℝ) (n : Fin (2 * k) → Fin N)
    (hn : n ∉ exceptionalTuples u K P₀ k N α T) :
    ∃ i : Fin (2 * k),
      α * Real.log (Real.log ((N + u : ℕ) : ℝ)) <
          ((n i).val + u).primeFactors.card ∧
        ((tupleBadModuli u K P₀ k (fun j ↦ (n j).val) i).card : ℝ) < T := by
  classical
  have hnpoor : n ∉ poorTuples u N k α := fun hmem =>
    hn (Finset.mem_union_left _ hmem)
  have hnotall : ¬ ∀ i, n i ∈ poorCoordinates u N α := by
    simpa only [mem_poorTuples] using hnpoor
  push Not at hnotall
  obtain ⟨i, hi⟩ := hnotall
  refine ⟨i, ?_, ?_⟩
  · have hi' : ¬ (((n i).val + u).primeFactors.card : ℝ) ≤
        α * Real.log (Real.log ((N + u : ℕ) : ℝ)) := by
      simpa only [poorCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact lt_of_not_ge hi'
  · have hnheavy : n ∉ collisionHeavyTuples u K P₀ k N i T := by
      intro hmem
      apply hn
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩
    simpa only [collisionHeavyTuples, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le] using hnheavy

/-- Union bounding the two exceptional mechanisms loses only the sum over the `2k` possible
anchors. -/
theorem card_exceptionalTuples_le (u K P₀ k N : ℕ) (α T : ℝ) :
    (exceptionalTuples u K P₀ k N α T).card ≤
      (poorTuples u N k α).card +
        ∑ i : Fin (2 * k), (collisionHeavyTuples u K P₀ k N i T).card := by
  rw [exceptionalTuples]
  calc
    (poorTuples u N k α ∪
        (Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
          collisionHeavyTuples u K P₀ k N i T).card ≤
        (poorTuples u N k α).card +
          ((Finset.univ : Finset (Fin (2 * k))).biUnion fun i =>
            collisionHeavyTuples u K P₀ k N i T).card := by
      exact Finset.card_union_le _ _
    _ ≤ (poorTuples u N k α).card +
        ∑ i : Fin (2 * k), (collisionHeavyTuples u K P₀ k N i T).card := by
      gcongr
      exact Finset.card_biUnion_le

/-- Abstract finite-sum split used after the two exceptional sets have been counted: exceptional
tuples cost at most one each, while every tuple outside costs at most the uniform contraction
`E`. -/
theorem sum_le_card_exceptional_add_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : I → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hS : ∀ i ∈ S, f i ≤ 1) (hout : ∀ i, i ∉ S → f i ≤ E) :
    (∑ i, f i) ≤ (S.card : ℝ) + (Fintype.card I : ℝ) * E := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i ↦ i ∈ S) f
  calc
    (∑ i, f i) =
        (∑ i ∈ (Finset.univ : Finset I) with i ∈ S, f i) +
          ∑ i ∈ (Finset.univ : Finset I) with i ∉ S, f i := hsplit.symm
    _ ≤ (((Finset.univ : Finset I).filter fun i ↦ i ∈ S).card : ℝ) +
        (((Finset.univ : Finset I).filter fun i ↦ i ∉ S).card : ℝ) * E := by
      gcongr
      · simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] using
          (Finset.sum_le_card_nsmul
            ((Finset.univ : Finset I).filter fun i ↦ i ∈ S) f 1
            (fun i hi ↦ hS i (Finset.mem_filter.mp hi).2))
      · simpa only [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul
            ((Finset.univ : Finset I).filter fun i ↦ i ∉ S) f E
            (fun i hi ↦ hout i (Finset.mem_filter.mp hi).2))
    _ ≤ (S.card : ℝ) + (Fintype.card I : ℝ) * E := by
      gcongr
      · simp
      · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ### Retained Bernoulli variance mass -/

/-- Choosing whether to include each distinct prime factor injects `2 ^ ω(m)` squarefree
divisors into the full divisor set. -/
theorem two_pow_primeFactors_card_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun p hp => ?_
  have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm
    (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- Discarding divisors at most `P₀` loses at most `P₀` elements. -/
theorem card_divisors_le_cutoff_add_large (m P₀ : ℕ) (hm : m ≠ 0) :
    m.divisors.card ≤ P₀ + (m.divisors.filter fun p => P₀ < p).card := by
  have hsmall : (m.divisors.filter fun p => ¬ P₀ < p).card ≤ P₀ := by
    calc
      (m.divisors.filter fun p => ¬ P₀ < p).card ≤ (Finset.Icc 1 P₀).card := by
        apply Finset.card_le_card
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpdiv, hpP₀⟩
        exact Finset.mem_Icc.mpr ⟨
          Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hpdiv) (Nat.pos_of_ne_zero hm),
          by omega⟩
      _ = P₀ := by rw [Nat.card_Icc]; omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := m.divisors) (p := fun p => P₀ < p)
  omega

/-- Every anchored divisor above the cutoff is uniquely classified as good or bad. -/
theorem card_large_anchor_moduli_eq_good_add_bad
    (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k)) :
    ((n i + a₀).divisors.filter fun p => P₀ < p).card =
      (tupleGoodModuli a₀ K P₀ k n i).card +
        (tupleBadModuli a₀ K P₀ k n i).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (n i + a₀).divisors.filter fun p => P₀ < p)
    (p := fun p => ∀ j, j ≠ i → n j % p < p - K)
  simpa only [tupleGoodModuli, tupleBadModuli, Finset.filter_filter] using hsplit.symm

/-- The variance hypothesis at each good modulus can be frozen at the anchor scale
`n i + a₀`: the exponent `-a` reverses the logarithmic comparison. -/
theorem tupleGoodModuli_variance_mass (delta : ℕ → ℝ) (a c : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m))
    (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (ha₀ : 1 ≤ a₀) (hP₀ : 1 ≤ P₀) :
    c * Real.rpow (Real.log (n i + a₀)) (-a) *
        ((tupleGoodModuli a₀ K P₀ k n i).card : ℝ) ≤
      ∑ p ∈ tupleGoodModuli a₀ K P₀ k n i, delta p * (1 - delta p) := by
  calc
    c * Real.rpow (Real.log (n i + a₀)) (-a) *
        ((tupleGoodModuli a₀ K P₀ k n i).card : ℝ) =
        ∑ p ∈ tupleGoodModuli a₀ K P₀ k n i,
          c * Real.rpow (Real.log (n i + a₀)) (-a) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ p ∈ tupleGoodModuli a₀ K P₀ k n i,
        delta p * (1 - delta p) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases (mem_tupleGoodModuli ha₀).mp hp with ⟨hpdiv, hP₀p, hsep⟩
      have hp2 : 2 ≤ p := by omega
      have hpM : p ≤ n i + a₀ := Nat.le_of_dvd (by omega) hpdiv
      have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
      have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp2)
      have hlogle : Real.log (p : ℝ) ≤ Real.log ((n i : ℝ) + a₀) :=
        Real.log_le_log hpR (by exact_mod_cast hpM)
      have hrpow : Real.rpow (Real.log (n i + a₀)) (-a) ≤
          Real.rpow (Real.log p) (-a) :=
        Real.rpow_le_rpow_of_nonpos hlogp hlogle (by linarith)
      exact (mul_le_mul_of_nonneg_left hrpow hc.le).trans (hvar p hp2)

/-- After the cutoff and collision losses, the surviving good moduli retain at least the
advertised `2 ^ ω` amount of Bernoulli variance.  A negative bracket makes the claim automatic;
later Hardy--Ramanujan and shifted-gcd estimates make it quantitatively positive. -/
theorem retained_variance_mass_le (delta : ℕ → ℝ) (a c : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-a) ≤ delta m * (1 - delta m))
    (a₀ K P₀ k : ℕ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (ha₀ : 1 ≤ a₀) (hP₀ : 1 ≤ P₀) :
    c * Real.rpow (Real.log (n i + a₀)) (-a) *
        ((((2 ^ (n i + a₀).primeFactors.card : ℕ) : ℝ) - P₀) -
          ((tupleBadModuli a₀ K P₀ k n i).card : ℝ)) ≤
      ∑ p ∈ tupleGoodModuli a₀ K P₀ k n i, delta p * (1 - delta p) := by
  have hM0 : n i + a₀ ≠ 0 := by omega
  have hcardNat : 2 ^ (n i + a₀).primeFactors.card ≤
      P₀ + (tupleGoodModuli a₀ K P₀ k n i).card +
        (tupleBadModuli a₀ K P₀ k n i).card := by
    have htwo := two_pow_primeFactors_card_le_card_divisors hM0
    have hlarge := card_divisors_le_cutoff_add_large (n i + a₀) P₀ hM0
    have hpart := card_large_anchor_moduli_eq_good_add_bad a₀ K P₀ k n i
    omega
  have hcardRadd : ((2 ^ (n i + a₀).primeFactors.card : ℕ) : ℝ) ≤
      (P₀ : ℝ) + ((tupleGoodModuli a₀ K P₀ k n i).card : ℝ) +
        ((tupleBadModuli a₀ K P₀ k n i).card : ℝ) := by
    exact_mod_cast hcardNat
  have hretain : (((2 ^ (n i + a₀).primeFactors.card : ℕ) : ℝ) - P₀) -
        ((tupleBadModuli a₀ K P₀ k n i).card : ℝ) ≤
      ((tupleGoodModuli a₀ K P₀ k n i).card : ℝ) := by
    linarith
  have hlognonneg : 0 ≤ Real.log ((n i : ℝ) + a₀) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n i + a₀ by omega))
  have hcoeff : 0 ≤ c * Real.rpow (Real.log (n i + a₀)) (-a) :=
    mul_nonneg hc.le (Real.rpow_nonneg hlognonneg _)
  exact (mul_le_mul_of_nonneg_left hretain hcoeff).trans
    (tupleGoodModuli_variance_mass delta a c ha hc hvar a₀ K P₀ k n i ha₀ hP₀)

/-! ### The full-tuple good-modulus phase gap -/

/-- A residue at least `K` places below the top of the period contributes at most its share of
the tuple's phase-error budget. -/
theorem scaled_residuePhase_le (b H L K p t : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hlarge : 16 * H * L ≤ b ^ K) (hp : 2 * K < p) (ht : t < p - K) :
    (H : ℝ) * residuePhase b p t ≤ 1 / (8 * (b : ℝ) * L) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have htK : t + (K + 1) ≤ p := by omega
  have hpow2 : (2 : ℝ) ≤ (b : ℝ) ^ p := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
  have hdenpos : 0 < (b : ℝ) ^ p - 1 := by linarith
  have hdenhalf : (b : ℝ) ^ p / 2 ≤ (b : ℝ) ^ p - 1 := by linarith
  have hpowmono : (b : ℝ) ^ t * (b : ℝ) ^ (K + 1) ≤ (b : ℝ) ^ p := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) htK
  have hlargeR : (16 : ℝ) * H * L ≤ (b : ℝ) ^ K := by exact_mod_cast hlarge
  have hpowK : (b : ℝ) ^ (K + 1) = (b : ℝ) ^ K * b := by rw [pow_succ]
  rw [hpowK] at hpowmono
  have hmain : (16 : ℝ) * b * H * L * (b : ℝ) ^ t ≤ (b : ℝ) ^ p := by
    calc
      (16 : ℝ) * b * H * L * (b : ℝ) ^ t =
          (b : ℝ) ^ t * ((16 : ℝ) * H * L) * b := by ring
      _ ≤ (b : ℝ) ^ t * (b : ℝ) ^ K * b := by gcongr
      _ ≤ (b : ℝ) ^ p := by simpa [mul_assoc] using hpowmono
  have hcross : (8 : ℝ) * b * L * H * (b : ℝ) ^ t ≤ (b : ℝ) ^ p - 1 := by
    nlinarith
  unfold residuePhase
  rw [show (H : ℝ) * ((b : ℝ) ^ t / ((b : ℝ) ^ p - 1)) =
    ((H : ℝ) * (b : ℝ) ^ t) / ((b : ℝ) ^ p - 1) by ring]
  rw [div_le_div_iff₀ hdenpos (by positivity : (0 : ℝ) < 8 * b * L)]
  nlinarith [hcross]

/-- The finite-period correction at the anchor also fits in one share of the phase-error
budget. -/
theorem scaled_anchor_phase_error (b e m H L K p : ℕ) (hb : 2 ≤ b)
    (hH : H = b ^ e * m) (hL : 1 ≤ L) (hK : e + 1 ≤ K)
    (hlarge : 16 * H * L ≤ b ^ K) (hp : 2 * K < p) :
    |(H : ℝ) * residuePhase b p (p - (e + 1)) - (m : ℝ) / b| ≤
      1 / (8 * (b : ℝ) * L) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hep : e + 1 ≤ p := by omega
  have hpow2 : (2 : ℝ) ≤ (b : ℝ) ^ p := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
  have hdenpos : 0 < (b : ℝ) ^ p - 1 := by linarith
  have hKp : K ≤ p := by omega
  have hpowKp : (b : ℝ) ^ K ≤ (b : ℝ) ^ p :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) hKp
  have hlargeR : (16 : ℝ) * H * L ≤ (b : ℝ) ^ K := by exact_mod_cast hlarge
  have hmH : m ≤ H := by
    rw [hH]
    exact Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
  have hmHR : (m : ℝ) ≤ H := by exact_mod_cast hmH
  have hcross : (8 : ℝ) * m * L ≤ (b : ℝ) ^ p - 1 := by
    have hbig : (16 : ℝ) * H * L ≤ (b : ℝ) ^ p := hlargeR.trans hpowKp
    nlinarith
  have hanchor := anchor_phase_formula b e m p hb hep
  rw [← hH] at hanchor
  have herr :
      (H : ℝ) * residuePhase b p (p - (e + 1)) - (m : ℝ) / b =
        (m : ℝ) / b / ((b : ℝ) ^ p - 1) := by
    rw [hanchor]
    ring
  rw [herr, abs_of_nonneg (by positivity)]
  rw [div_div]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < b * ((b : ℝ) ^ p - 1))
    (by positivity : (0 : ℝ) < 8 * b * L)]
  nlinarith [hcross]

/-- The anchor coordinate dominates the signed sum of all other coordinates: after orienting by
the anchor sign, the whole residue phase remains within `1/(4b)` of `m/b`. -/
theorem signed_tuple_phase_error (b e m H K k p : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hH : H = b ^ e * m) (hK : e + 1 ≤ K)
    (hlarge : 16 * H * (2 * k) ≤ b ^ K) (hp : 2 * K < p)
    (t : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hti : t i = p - (e + 1)) (htail : ∀ j, j ≠ i → t j < p - K) :
    |(tupleSign k i : ℝ) *
        ((H : ℝ) * ∑ j, (tupleSign k j : ℝ) * residuePhase b p (t j)) -
          (m : ℝ) / b| ≤ 1 / (4 * (b : ℝ)) := by
  classical
  have hL : 1 ≤ 2 * k := by omega
  have hsabs (j : Fin (2 * k)) : |(tupleSign k j : ℝ)| = 1 := by
    by_cases hj : j.val < k <;> simp [tupleSign, hj]
  have hssq : (tupleSign k i : ℝ) * (tupleSign k i : ℝ) = 1 := by
    by_cases hi : i.val < k <;> simp [tupleSign, hi]
  have hres0 (r : ℕ) : 0 ≤ residuePhase b p r := by
    unfold residuePhase
    have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < b))
      (by omega)
    positivity
  have hanchor := scaled_anchor_phase_error b e m H (2 * k) K p hb hH hL hK hlarge hp
  have htail_each (j : Fin (2 * k)) (hji : j ≠ i) :
      (H : ℝ) * residuePhase b p (t j) ≤
        1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ)) :=
    scaled_residuePhase_le b H (2 * k) K p (t j) hb hL hlarge hp (htail j hji)
  let S : ℝ := ∑ j ∈ Finset.univ.erase i,
    (tupleSign k j : ℝ) * residuePhase b p (t j)
  have hsum :
      (∑ j, (tupleSign k j : ℝ) * residuePhase b p (t j)) =
        (tupleSign k i : ℝ) * residuePhase b p (t i) + S := by
    rw [show (∑ j, (tupleSign k j : ℝ) * residuePhase b p (t j)) =
        ∑ j ∈ Finset.univ, (tupleSign k j : ℝ) * residuePhase b p (t j) by simp]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [S]
    ring
  have hother : |(tupleSign k i : ℝ) * (H : ℝ) * S| ≤ 1 / (8 * (b : ℝ)) := by
    calc
      |(tupleSign k i : ℝ) * (H : ℝ) * S| =
          (H : ℝ) * |S| := by
        rw [abs_mul, abs_mul, hsabs, abs_of_nonneg (Nat.cast_nonneg H)]
        ring
      _ ≤ (H : ℝ) * ∑ j ∈ Finset.univ.erase i,
          |(tupleSign k j : ℝ) * residuePhase b p (t j)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.univ.erase i, (H : ℝ) * residuePhase b p (t j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, hsabs, one_mul, abs_of_nonneg]
        exact hres0 (t j)
      _ ≤ ∑ _j ∈ Finset.univ.erase i,
          1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact htail_each j (Finset.ne_of_mem_erase hj)
      _ ≤ 1 / (8 * (b : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : (Finset.univ.erase i).card ≤ 2 * k := by
          calc
            (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin (2 * k))).card :=
              Finset.card_le_card (Finset.erase_subset i _)
            _ = 2 * k := Fintype.card_fin (2 * k)
        have hconst : 0 ≤ 1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ)) := by positivity
        calc
          ((Finset.univ.erase i).card : ℝ) *
              (1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ))) ≤
              ((2 * k : ℕ) : ℝ) *
                (1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ))) := by
            gcongr
          _ = 1 / (8 * (b : ℝ)) := by field_simp
  have hdecomp :
      (tupleSign k i : ℝ) *
          ((H : ℝ) * ∑ j, (tupleSign k j : ℝ) * residuePhase b p (t j)) -
            (m : ℝ) / b =
        ((H : ℝ) * residuePhase b p (t i) - (m : ℝ) / b) +
          (tupleSign k i : ℝ) * (H : ℝ) * S := by
    calc
      _ = ((tupleSign k i : ℝ) * (tupleSign k i : ℝ)) *
            ((H : ℝ) * residuePhase b p (t i)) - (m : ℝ) / b +
          (tupleSign k i : ℝ) * (H : ℝ) * S := by rw [hsum]; ring
      _ = _ := by rw [hssq]; ring
  rw [hdecomp, hti]
  calc
    |(H : ℝ) * residuePhase b p (p - (e + 1)) - (m : ℝ) / b +
        (tupleSign k i : ℝ) * (H : ℝ) * S| ≤
        |(H : ℝ) * residuePhase b p (p - (e + 1)) - (m : ℝ) / b| +
          |(tupleSign k i : ℝ) * (H : ℝ) * S| := abs_add_le _ _
    _ ≤ 1 / (8 * (b : ℝ) * ((2 * k : ℕ) : ℝ)) + 1 / (8 * (b : ℝ)) :=
      add_le_add hanchor hother
    _ ≤ 1 / (4 * (b : ℝ)) := by
      have hbpos : (0 : ℝ) < b := by positivity
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hLR : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hL
      field_simp
      nlinarith

/-- Reducing every tuple coordinate modulo `p` changes the phase only by an integer and hence
does not change its cosine. -/
theorem cos_tuplePhase_mod (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (k p : ℕ) (hp : 1 ≤ p)
    (n : Fin (2 * k) → ℕ) :
    Real.cos (2 * Real.pi * tuplePhase b h k p n) =
      Real.cos (2 * Real.pi * tuplePhase b h k p (fun i ↦ n i % p)) := by
  classical
  choose w hw using fun i : Fin (2 * k) ↦ residuePhase_add_int b (n i) p hb hp
  have hsum :
      (∑ i, (tupleSign k i : ℝ) *
          ((b : ℝ) ^ (n i) / ((b : ℝ) ^ p - 1))) =
        (∑ i, (tupleSign k i : ℝ) *
          ((b : ℝ) ^ (n i % p) / ((b : ℝ) ^ p - 1))) +
          ((∑ i, tupleSign k i * w i : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw i]
    ring
  have hphase : tuplePhase b h k p n = tuplePhase b h k p (fun i ↦ n i % p) +
      ((h * ∑ i, tupleSign k i * w i : ℤ) : ℝ) := by
    unfold tuplePhase
    rw [hsum]
    push_cast
    ring
  calc
    Real.cos (2 * Real.pi * tuplePhase b h k p n) = (ePh (tuplePhase b h k p n)).re :=
      (ePh_re _).symm
    _ = (ePh (tuplePhase b h k p (fun i ↦ n i % p))).re := by
      rw [hphase, ePh_add_int]
    _ = Real.cos (2 * Real.pi * tuplePhase b h k p (fun i ↦ n i % p)) := ePh_re _

/-- An anchored divisor forces the anchor coordinate into the residue `p - a₀`. -/
theorem anchor_residue_of_dvd {a₀ p n : ℕ} (ha₀ : 1 ≤ a₀) (ha₀p : a₀ < p)
    (hp : p ∣ n + a₀) : n % p = p - a₀ := by
  have hp0 : 0 < p := by omega
  have hnmod : n % p < p := Nat.mod_lt _ hp0
  have hzero : (n % p + a₀) % p = 0 := by
    have := Nat.mod_eq_zero_of_dvd hp
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha₀p] using this
  have hdvd : p ∣ n % p + a₀ := Nat.dvd_of_mod_eq_zero hzero
  have hsumpos : 0 < n % p + a₀ := by omega
  have hge : p ≤ n % p + a₀ := Nat.le_of_dvd hsumpos hdvd
  have hsub : n % p + a₀ - p < p := by omega
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hzero
  omega

/-- Every modulus in `tupleGoodModuli` forces the advertised spectral cosine gap for the complete
signed tuple, not merely for an anchor/tail pair. -/
theorem tupleGoodModuli_cos_le (b e m K P₀ k p : ℕ) (h : ℤ)
    (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀)
    (hgood : p ∈ tupleGoodModuli (e + 1) K P₀ k n i) :
    Real.cos (2 * Real.pi * tuplePhase b h k p n) ≤ Real.cos (Real.pi / b) := by
  classical
  rcases (mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
    (k := k) (p := p) (n := n) (i := i) (by omega)).mp hgood with ⟨hpi, hPp, hsep⟩
  have hpK : 2 * K < p := lt_of_le_of_lt hKP hPp
  have hep : e + 1 < p := by omega
  have hp1 : 1 ≤ p := by omega
  have hti : n i % p = p - (e + 1) := anchor_residue_of_dvd (by omega) hep hpi
  have herr := signed_tuple_phase_error b e m h.natAbs K k p hb hk hfac hK hlarge hpK
    (fun j ↦ n j % p) i hti hsep
  have herr' :
      |(tupleSign k i : ℝ) *
          ((h.natAbs : ℝ) * ∑ j, (tupleSign k j : ℝ) *
            residuePhase b p (n j % p)) - (m : ℝ) / b| ≤
        1 / (2 * (b : ℝ)) :=
    herr.trans (by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * b)
        (by positivity : (0 : ℝ) < 2 * b)]
      nlinarith)
  let S : ℝ := ∑ j, (tupleSign k j : ℝ) * residuePhase b p (n j % p)
  have hphase : tuplePhase b h k p (fun j ↦ n j % p) = (h : ℝ) * S := by
    simp only [tuplePhase, residuePhase, S]
  have hcosS :
      Real.cos (2 * Real.pi * tuplePhase b h k p (fun j ↦ n j % p)) =
        Real.cos (2 * Real.pi * ((tupleSign k i : ℝ) * (h.natAbs : ℝ) * S)) := by
    rw [hphase]
    by_cases hhpos : 0 ≤ h
    · have hcast : (h : ℝ) = (h.natAbs : ℝ) := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hhpos]
      rw [hcast]
      by_cases hi : i.val < k
      · simp [tupleSign, hi]
      · simp only [tupleSign, hi, if_false, Int.cast_neg, Int.cast_one, neg_mul]
        rw [show 2 * Real.pi * -(1 * (h.natAbs : ℝ) * S) =
          -(2 * Real.pi * ((h.natAbs : ℝ) * S)) by ring, Real.cos_neg]
    · have hhneg : h < 0 := lt_of_not_ge hhpos
      have hcast : (h : ℝ) = -(h.natAbs : ℝ) := by
        have habs : (h.natAbs : ℝ) = -(h : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg]
          exact_mod_cast hhneg
        linarith
      rw [hcast]
      by_cases hi : i.val < k
      · simp only [tupleSign, hi, if_true, Int.cast_one, one_mul]
        rw [show 2 * Real.pi * (-(h.natAbs : ℝ) * S) =
          -(2 * Real.pi * ((h.natAbs : ℝ) * S)) by ring, Real.cos_neg]
      · simp [tupleSign, hi]
  calc
    Real.cos (2 * Real.pi * tuplePhase b h k p n) =
        Real.cos (2 * Real.pi * tuplePhase b h k p (fun j ↦ n j % p)) :=
      cos_tuplePhase_mod b hb h k p hp1 n
    _ = Real.cos (2 * Real.pi * ((tupleSign k i : ℝ) * (h.natAbs : ℝ) * S)) := hcosS
    _ ≤ Real.cos (Real.pi / b) := by
      apply cos_two_pi_le_of_near_rational hb hm
      simpa only [S, mul_assoc] using herr'

/-- A fixed cosine gap turns a Bernoulli characteristic factor into exponential variance
decay. -/
theorem bernMod_le_exp_of_cos_le {delta theta kappa : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hcos : Real.cos (2 * Real.pi * theta) ≤ 1 - kappa) :
    bernMod delta theta ≤ Real.exp (-kappa * (delta * (1 - delta))) := by
  let v := delta * (1 - delta)
  let x := v * (1 - Real.cos (2 * Real.pi * theta))
  have hv0 : 0 ≤ v := mul_nonneg hdelta0 (sub_nonneg.mpr hdelta1)
  have hcos1 : Real.cos (2 * Real.pi * theta) ≤ 1 := Real.cos_le_one _
  have hx0 : 0 ≤ x := mul_nonneg hv0 (sub_nonneg.mpr hcos1)
  have hsq : bernMod delta theta ^ 2 = 1 - 2 * x := by
    rw [bernMod_sq]
    dsimp [x, v]
    ring
  have hxhalf : x ≤ 1 / 2 := by
    nlinarith [sq_nonneg (bernMod delta theta)]
  have hsqrt : Real.sqrt (1 - 2 * x) ≤ Real.exp (-x) :=
    sqrt_one_sub_two_mul_le_exp_neg hx0 hxhalf
  have hbern : bernMod delta theta ≤ Real.exp (-x) := by
    have hroot : bernMod delta theta = Real.sqrt (1 - 2 * x) := by
      rw [← hsq, Real.sqrt_sq (bernMod_nonneg _ _)]
    rw [hroot]
    exact hsqrt
  have hxgap : kappa * v ≤ x := by
    calc
      kappa * v = v * kappa := by ring
      _ ≤ v * (1 - Real.cos (2 * Real.pi * theta)) := by
        apply mul_le_mul_of_nonneg_left _ hv0
        linarith
      _ = x := rfl
  exact hbern.trans (Real.exp_le_exp.mpr (by linarith))

/-- The anchor cosine gap gives the precise spectral contraction used for a good modulus. -/
theorem bernMod_le_exp_spectral_of_cos_le (b : ℕ) {delta theta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hcos : Real.cos (2 * Real.pi * theta) ≤ Real.cos (Real.pi / b)) :
    bernMod delta theta ≤
      Real.exp (-spectralConst b * (delta * (1 - delta))) := by
  apply bernMod_le_exp_of_cos_le hdelta0 hdelta1
  simpa only [spectralConst, sub_sub_cancel] using hcos

/-- Good-modulus contractions multiply to the exponential of their total Bernoulli variance. -/
theorem prod_bernMod_le_exp_neg_spectral (b : ℕ) (F : Finset ℕ)
    (delta theta : ℕ → ℝ) (hdelta : ∀ p ∈ F, 0 ≤ delta p ∧ delta p ≤ 1)
    (hcos : ∀ p ∈ F,
      Real.cos (2 * Real.pi * theta p) ≤ Real.cos (Real.pi / b)) :
    ∏ p ∈ F, bernMod (delta p) (theta p) ≤
      Real.exp (-spectralConst b * ∑ p ∈ F, delta p * (1 - delta p)) := by
  calc
    ∏ p ∈ F, bernMod (delta p) (theta p) ≤
        ∏ p ∈ F, Real.exp (-spectralConst b * (delta p * (1 - delta p))) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact bernMod_nonneg _ _
      · intro p hp
        exact bernMod_le_exp_spectral_of_cos_le b (hdelta p hp).1 (hdelta p hp).2
          (hcos p hp)
    _ = Real.exp (-spectralConst b * ∑ p ∈ F, delta p * (1 - delta p)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

/-- The spectral gap `1 - cos (π / b)` is strictly positive for every admissible base. -/
theorem spectralConst_pos (b : ℕ) (hb : 2 ≤ b) : 0 < spectralConst b := by
  have hbpos : (0 : ℝ) < b := by positivity
  have hxpos : 0 < Real.pi / (b : ℝ) := div_pos Real.pi_pos hbpos
  have hxle : Real.pi / (b : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hbpos).2
    have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / (b : ℝ)) < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hxle hxpos
  unfold spectralConst
  rw [Real.cos_zero] at hcos
  linarith

/-- The zero-based Bernoulli indices attached to one tuple anchor inherit the full retained-mass
contraction.  This is the deterministic per-tuple bridge between `ebMoment_le_tupleAvg` and the
Hardy--Ramanujan / shifted-gcd exceptional-set estimates. -/
theorem tupleGoodModuli_bernMod_product_le (delta : ℕ → ℝ) (a c : ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hvar : ∀ p : ℕ, 2 ≤ p →
      c * Real.rpow (Real.log p) (-a) ≤ delta p * (1 - delta p))
    (b e m K P₀ k : ℕ) (h : ℤ) (n : Fin (2 * k) → ℕ) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀)
    (hP₀ : 1 ≤ P₀) :
    ∏ r ∈ (tupleGoodModuli (e + 1) K P₀ k n i).image (fun p => p - 1),
        bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) n) ≤
      Real.exp (-spectralConst b *
        (c * Real.rpow (Real.log (n i + (e + 1))) (-a) *
          ((((2 ^ (n i + (e + 1)).primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k n i).card : ℝ)))) := by
  classical
  let G := tupleGoodModuli (e + 1) K P₀ k n i
  have hp_two (p : ℕ) (hp : p ∈ G) : 2 ≤ p := by
    have hcut := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := n) (i := i) (by omega)).mp hp).2.1
    omega
  have hinj : Set.InjOn (fun p : ℕ => p - 1) ↑G := by
    intro p hp q hq hpq
    change p ∈ G at hp
    change q ∈ G at hq
    have hp1 : 1 ≤ p := le_trans (by omega) (hp_two p hp)
    have hq1 : 1 ≤ q := le_trans (by omega) (hp_two q hq)
    change p - 1 = q - 1 at hpq
    omega
  have hreindex :
      (∏ r ∈ G.image (fun p => p - 1),
          bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) n)) =
        ∏ p ∈ G, bernMod (delta p) (tuplePhase b h k p n) := by
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (by have := hp_two p hp; omega : 1 ≤ p)]
  have hproduct :
      (∏ p ∈ G, bernMod (delta p) (tuplePhase b h k p n)) ≤
        Real.exp (-spectralConst b *
          ∑ p ∈ G, delta p * (1 - delta p)) := by
    apply prod_bernMod_le_exp_neg_spectral
    · intro p hp
      exact hdelta p
    · intro p hp
      exact tupleGoodModuli_cos_le b e m K P₀ k p h n i hb hk hfac hm hK hlarge hKP hp
  have hmass := retained_variance_mass_le delta a c ha hc hvar
    (e + 1) K P₀ k n i (by omega) hP₀
  have hspectral := (spectralConst_pos b hb).le
  rw [show tupleGoodModuli (e + 1) K P₀ k n i = G by rfl] at hmass
  rw [show tupleGoodModuli (e + 1) K P₀ k n i = G by rfl, hreindex]
  refine hproduct.trans (Real.exp_le_exp.mpr ?_)
  have hmul := mul_le_mul_of_nonneg_left hmass hspectral
  calc
    -spectralConst b * (∑ p ∈ G, delta p * (1 - delta p)) =
        -(spectralConst b * (∑ p ∈ G, delta p * (1 - delta p))) := by ring
    _ ≤ -(spectralConst b *
        (c * Real.rpow (Real.log (n i + (e + 1))) (-a) *
          ((((2 ^ (n i + (e + 1)).primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k n i).card : ℝ)))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using neg_le_neg hmul
    _ = -spectralConst b *
        (c * Real.rpow (Real.log (n i + (e + 1))) (-a) *
          ((((2 ^ (n i + (e + 1)).primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k n i).card : ℝ))) := by ring

/-- A fixed initial set of Bernoulli coordinates contains every tuple-dependent good modulus.
Consequently its characteristic product inherits the contraction from any chosen good anchor.
This is the bridge needed because `ebMoment_le_tupleAvg` chooses its finite set before summing over
tuples. -/
theorem global_bernMod_product_le_good_anchor (delta : ℕ → ℝ) (a c : ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hvar : ∀ p : ℕ, 2 ≤ p →
      c * Real.rpow (Real.log p) (-a) ≤ delta p * (1 - delta p))
    (b e m K P₀ k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀)
    (hP₀ : 1 ≤ P₀) :
    ∏ r ∈ Finset.range (N + e + 1),
        bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) (fun j ↦ (n j).val)) ≤
      Real.exp (-spectralConst b *
        (c * Real.rpow (Real.log ((n i).val + (e + 1))) (-a) *
          ((((2 ^ ((n i).val + (e + 1)).primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).card : ℝ)))) := by
  let G := (tupleGoodModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).image
    (fun p ↦ p - 1)
  have hsubset : G ⊆ Finset.range (N + e + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    have hpdiv := ((mem_tupleGoodModuli (a₀ := e + 1) (K := K) (P₀ := P₀)
      (k := k) (p := p) (n := fun j ↦ (n j).val) (i := i) (by omega)).mp hp).1
    have hple : p ≤ (n i).val + (e + 1) := Nat.le_of_dvd (by omega) hpdiv
    rw [Finset.mem_range]
    omega
  have hglobal :
      (∏ r ∈ Finset.range (N + e + 1),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun j ↦ (n j).val))) ≤
        ∏ r ∈ G, bernMod (delta (r + 1))
          (tuplePhase b h k (r + 1) (fun j ↦ (n j).val)) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hsubset
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr hrG
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  refine hglobal.trans ?_
  simpa only [G] using tupleGoodModuli_bernMod_product_le delta a c hdelta ha hc hvar
    b e m K P₀ k h (fun j ↦ (n j).val) i hb hk hfac hm hK hlarge hKP hP₀

/-! ### Scalar assembly for the moment bound -/

/-- After multiplying by the variance weight `(log x)^{-a}`, a logarithmic divisor supply of
exponent `s` absorbs both a fixed cutoff and a collision threshold of exponent `η < s - a`.
This is the eventual scalar inequality needed on every rich/light tuple. -/
theorem eventually_retained_log_power (P₀ : ℕ) {a s η : ℝ}
    (ha : 0 ≤ a) (hη : 0 < η) (hgap : η < s - a) :
    ∀ᶠ L : ℝ in atTop,
      L ^ (-a) * ((L ^ s - P₀) - L ^ η) ≥ L ^ η := by
  have hs : 0 < s := by linarith
  have hd : 0 < s - (a + η) := by linarith
  have hmain := (tendsto_rpow_atTop hs).eventually_ge_atTop (2 * P₀)
  have hratio := (tendsto_rpow_atTop hd).eventually_ge_atTop 4
  filter_upwards [eventually_ge_atTop (1 : ℝ), hmain, hratio] with L hL hmain hratio
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow_aη_nonneg : 0 ≤ L ^ (a + η) := Real.rpow_nonneg hLpos.le _
  have hpowη_le : L ^ η ≤ L ^ (a + η) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hfactor : 4 * L ^ (a + η) ≤ L ^ s := by
    calc
      4 * L ^ (a + η) ≤ L ^ (s - (a + η)) * L ^ (a + η) := by
        exact mul_le_mul_of_nonneg_right hratio hpow_aη_nonneg
      _ = L ^ s := by
        rw [← Real.rpow_add hLpos]
        congr 1
        ring
  have hbracket : L ^ (a + η) ≤ (L ^ s - P₀) - L ^ η := by
    nlinarith
  calc
    L ^ η = L ^ (-a) * L ^ (a + η) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    _ ≤ L ^ (-a) * ((L ^ s - P₀) - L ^ η) := by
      exact mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg hLpos.le _)

/-- Natural endpoints inherit `eventually_retained_log_power` after the shifted logarithmic
scale `N ↦ log (N + u)`, which tends to infinity. -/
theorem eventually_retained_log_power_nat (u P₀ : ℕ) {a s η : ℝ}
    (ha : 0 ≤ a) (hη : 0 < η) (hgap : η < s - a) :
    ∀ᶠ N : ℕ in atTop,
      Real.rpow (Real.log ((N + u : ℕ) : ℝ)) (-a) *
          ((Real.rpow (Real.log ((N + u : ℕ) : ℝ)) s - P₀) -
            Real.rpow (Real.log ((N + u : ℕ) : ℝ)) η) ≥
        Real.rpow (Real.log ((N + u : ℕ) : ℝ)) η := by
  have hNu : Tendsto (fun N : ℕ ↦ ((N + u : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add] using
      (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (u : ℝ)) atTop (nhds u)))
  exact (Real.tendsto_log_atTop.comp hNu).eventually
    (eventually_retained_log_power P₀ ha hη hgap)

/-- A rich coordinate whose collision loss is below the chosen logarithmic threshold retains
at least that threshold after the variance weight is applied. -/
theorem retained_log_mass_ge_of_rich_light
    (M x P₀ : ℕ) (a α η B : ℝ)
    (hM : 3 ≤ M) (hx : 2 ≤ x) (hxM : x ≤ M)
    (ha : 0 ≤ a)
    (hrich : α * Real.log (Real.log M) < (x.primeFactors.card : ℝ))
    (hB : B < Real.rpow (Real.log M) η)
    (hscalar :
      Real.rpow (Real.log M) (-a) *
          ((Real.rpow (Real.log M) (α * Real.log 2) - P₀) -
            Real.rpow (Real.log M) η) ≥
        Real.rpow (Real.log M) η) :
    Real.rpow (Real.log x) (-a) *
        ((((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) - B) ≥
      Real.rpow (Real.log M) η := by
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogle : Real.log (x : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hxM)
  have hsupply := log_rpow_lt_two_pow_primeFactors M x α hM hrich
  have hbracket :
      (Real.rpow (Real.log M) (α * Real.log 2) - P₀) -
          Real.rpow (Real.log M) η <
        (((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) - B := by
    linarith
  have htarget_pos : 0 < Real.rpow (Real.log M) η :=
    Real.rpow_pos_of_pos hlogM _
  have hcoeff_pos : 0 < Real.rpow (Real.log M) (-a) :=
    Real.rpow_pos_of_pos hlogM _
  have hbase_nonneg :
      0 ≤ (Real.rpow (Real.log M) (α * Real.log 2) - P₀) -
        Real.rpow (Real.log M) η := by
    by_contra hneg
    have hneg' :
        (Real.rpow (Real.log M) (α * Real.log 2) - P₀) -
            Real.rpow (Real.log M) η < 0 := lt_of_not_ge hneg
    have hprodneg := mul_neg_of_pos_of_neg hcoeff_pos hneg'
    linarith
  have hactual_nonneg :
      0 ≤ (((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) - B :=
    hbase_nonneg.trans hbracket.le
  have hcoeff_le : Real.rpow (Real.log M) (-a) ≤
      Real.rpow (Real.log x) (-a) :=
    Real.rpow_le_rpow_of_nonpos hlogx hlogle (by linarith)
  calc
    Real.rpow (Real.log M) η ≤
        Real.rpow (Real.log M) (-a) *
          ((Real.rpow (Real.log M) (α * Real.log 2) - P₀) -
            Real.rpow (Real.log M) η) := hscalar
    _ ≤ Real.rpow (Real.log M) (-a) *
        ((((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) - B) := by
      exact mul_le_mul_of_nonneg_left hbracket.le hcoeff_pos.le
    _ ≤ Real.rpow (Real.log x) (-a) *
        ((((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) - B) := by
      exact mul_le_mul_of_nonneg_right hcoeff_le hactual_nonneg

/-- Choose integral moments making both the Hardy--Ramanujan and collision exceptional sets
decay faster than the square-log threshold required downstream. -/
theorem exists_moment_parameters {q η : ℝ} (hq : 0 < q) (hη : 0 < η) :
    ∃ k R : ℕ, 1 ≤ k ∧ 1 ≤ R ∧ 2 < 2 * (k : ℝ) * q ∧ 2 < η * R := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / q)
  obtain ⟨R, hR⟩ := exists_nat_gt (2 / η)
  have hk1 : 1 ≤ k := by
    have hkpos : (0 : ℝ) < k := (div_pos one_pos hq).trans hk
    exact_mod_cast hkpos
  have hR1 : 1 ≤ R := by
    have hRpos : (0 : ℝ) < R := (div_pos (by norm_num) hη).trans hR
    exact_mod_cast hRpos
  refine ⟨k, R, hk1, hR1, ?_, ?_⟩
  · rw [div_lt_iff₀ hq] at hk
    nlinarith
  · rw [div_lt_iff₀ hη] at hR
    nlinarith

/-- Simultaneously choose the Hardy--Ramanujan exponent, retained-mass exponent, Weyl moment,
and collision moment with both exceptional powers strictly greater than two. -/
theorem exists_eb_decay_parameters (a : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.log 2) :
    ∃ α q η : ℝ, ∃ k R : ℕ,
      0 < α ∧ α < 1 ∧ 0 < q ∧ q < 1 - α + α * Real.log α ∧
      0 < η ∧ η < α * Real.log 2 - a ∧
      1 ≤ k ∧ 1 ≤ R ∧ 2 < 2 * (k : ℝ) * q ∧ 2 < η * R := by
  obtain ⟨α, q, hα0, hα1, hq0, hq, hgap⟩ := exists_hardyRamanujan_parameters a ha0 ha
  let η := (α * Real.log 2 - a) / 2
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hηgap : η < α * Real.log 2 - a := by dsimp [η]; linarith
  obtain ⟨k, R, hk, hR, hkq, hRη⟩ := exists_moment_parameters hq0 hη0
  exact ⟨α, q, η, k, R, hα0, hα1, hq0, hq, hη0, hηgap, hk, hR, hkq, hRη⟩

/-- Outside the finite exceptional set, the common Bernoulli characteristic product has uniform
stretched-exponential contraction.  This closes the scalar bridge from rich/light anchors to the
tuple summand used by `ebMoment_le_tupleAvg`. -/
theorem global_bernMod_product_le_rich_light
    (delta : ℕ → ℝ) (a c α η : ℝ)
    (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (ha : 0 ≤ a) (hc : 0 < c) (hα : 0 < α)
    (hvar : ∀ p : ℕ, 2 ≤ p →
      c * Real.rpow (Real.log p) (-a) ≤ delta p * (1 - delta p))
    (b e m K P₀ k N : ℕ) (h : ℤ) (n : Fin (2 * k) → Fin N) (i : Fin (2 * k))
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 3 ≤ N)
    (hfac : h.natAbs = b ^ e * m) (hm : ¬ b ∣ m) (hK : e + 1 ≤ K)
    (hlarge : 16 * h.natAbs * (2 * k) ≤ b ^ K) (hKP : 2 * K ≤ P₀)
    (hP₀ : 1 ≤ P₀)
    (hrich : α * Real.log (Real.log ((N + (e + 1) : ℕ) : ℝ)) <
      (((n i).val + (e + 1)).primeFactors.card : ℝ))
    (hlight :
      ((tupleBadModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).card : ℝ) <
        Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) η)
    (hscalar :
      Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) (-a) *
          ((Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) (α * Real.log 2) - P₀) -
            Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) η) ≥
        Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) η) :
    ∏ r ∈ Finset.range (N + e + 1),
        bernMod (delta (r + 1)) (tuplePhase b h k (r + 1) (fun j ↦ (n j).val)) ≤
      Real.exp (-spectralConst b *
        (c * Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) η)) := by
  let M := N + (e + 1)
  let x := (n i).val + (e + 1)
  have hM : 3 ≤ M := by omega
  have hxM : x ≤ M := by
    dsimp [x, M]
    have := (n i).isLt
    omega
  have hloglog : 0 < Real.log (Real.log (M : ℝ)) := by
    apply Real.log_pos
    rw [Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < M)]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hM)
  have homega : 0 < (x.primeFactors.card : ℝ) := by
    exact (mul_pos hα hloglog).trans (by simpa only [M, x] using hrich)
  have hx1 : 1 ≤ x := by dsimp [x]; omega
  have hx : 2 ≤ x := by
    by_contra hxnot
    have hxone : x = 1 := by omega
    subst x
    norm_num at homega
    omega
  have hmass := retained_log_mass_ge_of_rich_light M x P₀ a α η
    ((tupleBadModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).card : ℝ)
    hM hx hxM ha (by simpa only [M, x] using hrich)
    (by simpa only [M] using hlight) (by simpa only [M] using hscalar)
  have hglobal := global_bernMod_product_le_good_anchor delta a c hdelta ha hc hvar
    b e m K P₀ k N h n i hb hk hfac hm hK hlarge hKP hP₀
  refine hglobal.trans (Real.exp_le_exp.mpr ?_)
  have hscale :
      c * Real.rpow (Real.log M) η ≤
        c * (Real.rpow (Real.log x) (-a) *
          ((((2 ^ x.primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).card : ℝ))) :=
    mul_le_mul_of_nonneg_left hmass hc.le
  have hspectral := (spectralConst_pos b hb).le
  have hscale' :
      c * Real.rpow (Real.log ((N + (e + 1) : ℕ) : ℝ)) η ≤
        c * (Real.rpow (Real.log (((n i).val : ℝ) + ((e : ℝ) + 1))) (-a) *
          ((((2 ^ ((n i).val + (e + 1)).primeFactors.card : ℕ) : ℝ) - P₀) -
            ((tupleBadModuli (e + 1) K P₀ k (fun j ↦ (n j).val) i).card : ℝ))) := by
    simpa only [M, x, Nat.cast_add, Nat.cast_one] using hscale
  nlinarith [mul_le_mul_of_nonneg_left hscale' hspectral]

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
