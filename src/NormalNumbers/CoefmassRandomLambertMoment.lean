/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect

/-!
# Whole-factor high moments for random prime Lambert sums (skeleton)

Target: `finiteCRT_moment_bound`, copied VERBATIM (statement and the definitions it uses) from the
private research packet `NNLambertWindowMoments.lean` at KB commit 96ee3b68 (Astra research,
thread 01a12e16).  Paper proof: `nn-lambert-window-moments-2026-10-12.md`, first two proof sections.
Assignment: codex2 mail 20261012T041621Z.  The statement is frozen; any strengthening is added
alongside, never in place.

For fixed `b, h`, let `X_p` be independent Bernoulli(`δ_p`) prime selections and
`Y = Σ_p X_p/(b^p-1)`.  For any finite set `F` of primes above `P₀`, any translate `c`, any sign:

  `E ‖A_N(c ± Y; h)‖^{2k} ≤ exp(-γ Σ_{p∈F} δ_p(1-δ_p) min(k/p, 1)) + 2k (∏_{p∈F} p)/N`,

with `P₀, γ` depending only on `b, h`.

## Proof chain (each step is a separate declaration below)

1. `moment_le_tupleAvg`: expand `‖A‖^{2k} = A^k conj(A)^k` over `n ∈ [0,N)^{2k}`.  The translate
   contributes a unit phase.  Split the Lambert sum into the `F`-primes and the rest.  The rest is
   independent of the `F`-primes, so its factor has modulus at most 1.  Independence across `F`
   factorizes the remaining expectation into `∏_{p∈F} bernMod δ_p (phase_p)`.
   Two routes for the grinder: `indep_iSup_of_disjoint` for (F, complement), or truncate to
   primes `≤ M` and pass `M → ∞` by dominated convergence (integrand `≤ 1`).
2. `bernMod_tuplePhase_mod`: each prime factor depends only on the residues `n_i mod p`, since
   `(b^n - b^(n mod p))/(b^p-1) ∈ ℤ`.
3. `prefix_tuple_mean_le`: the prefix tuple average of a `[0,1]`-valued `Q`-periodic function
   exceeds its full-period average by at most `d·Q/N`, via a per-coordinate hybrid argument with
   total variation at most `Q/N` per coordinate.
4. `crt_tuple_prod_mean`: the pairwise-coprime abstraction.  For periods `q_i` that are pairwise
   coprime, the full-period average of `∏ g_i` with `g_i` `q_i`-periodic is `∏` of the averages
   (CRT, `ZMod.prodEquivPi`).  No prime indices or Lambert phases are used.
5. `bernMod_sq`: `|1-δ+δe(θ)|² = 1 - 2δ(1-δ)(1 - cos 2πθ)`.
6. `residueTuple_mean_sq`: over uniform residues `(r_1..r_{2k})` with signs `+^k -^k`,
   `E bernMod² = 1 - 2v(1 - ‖f_p(h)‖^{2k})`, where `f_p(h) = localMean b h p`.
7. `localMean_normSq_le`, the one-prime spectral gap: `‖f_p(h)‖² ≤ 1 - c₀/p` for `p > P₀`,
   with `c₀ = 1 - cos(π/b)`.  Pair the residue `p - a₀` (where `a₀ = 1 + v_b(h)`) with every
   `t ≤ p-K-1`, choosing `K ≥ a₀` and `b^K ≥ 16|h|`; the phase difference is at least `1/(2b)`
   from `ℤ`.  Take `P₀ = 2K`.
8. `residueTuple_mean_le`: Cauchy–Schwarz (`E G ≤ √(E G²)`), then `√(1-2x) ≤ e^{-x}`, then
   `‖f‖^{2k} ≤ e^{-c₀k/p}` and concavity give `E G ≤ exp(-γ v min(k/p,1))`, with
   `γ = 1 - e^{-c₀}`.

Status: IN PROGRESS.  The finite local analytic layer and the infinite-series characteristic bound
are proved.  The finite even-moment expansion and final assembly declarations remain.
-/

namespace NormalNumbers.RandomLambertMoment

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ComplexConjugate

/-! ### Verbatim copies from `NNLambertWindowMoments` (96ee3b68) -/

abbrev Prime := {p : ℕ // p.Prime}

def BernoulliLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (delta : Prime → ℝ) (X : Prime → Ω → Bool) : Prop :=
  (∀ p, 0 ≤ delta p ∧ delta p ≤ 1) ∧
  (∀ p, Measurable (X p)) ∧ iIndepFun X μ ∧
    ∀ p, μ {w | X p w = true} = ENNReal.ofReal (delta p)

noncomputable def randomLambert {Ω : Type*} (b : ℕ)
    (X : Prime → Ω → Bool) (w : Ω) : ℝ :=
  ∑' p : Prime, (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)

noncomputable def weylMean (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (b : ℂ)^n * (x : ℂ))) / N

noncomputable def primeVariance (delta : Prime → ℝ) (p : Prime) : ℝ :=
  delta p * (1 - delta p)

/-! ### Local objects -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def ePh (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp] theorem norm_ePh (x : ℝ) : ‖ePh x‖ = 1 := by
  have hx : ePh x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold ePh
    congr 1
    push_cast
    ring
  rw [hx]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ePh_add_int (x : ℝ) (w : ℤ) : ePh (x + w) = ePh x := by
  unfold ePh
  have hx : (2 * Real.pi * Complex.I * ((x + w : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (x : ℂ) + (w : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hx, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `α_p(r) = b^r/(b^p-1)`. -/
noncomputable def residuePhase (b p r : ℕ) : ℝ := (b : ℝ) ^ r / ((b : ℝ) ^ p - 1)

/-- `f_p(h) = (1/p) Σ_{r<p} e(h α_p(r))`. -/
noncomputable def localMean (b : ℕ) (h : ℤ) (p : ℕ) : ℂ :=
  (∑ r ∈ Finset.range p, ePh ((h : ℝ) * residuePhase b p r)) / p

/-- `c₀ = 1 - cos(π/b)`. -/
noncomputable def spectralConst (b : ℕ) : ℝ := 1 - Real.cos (Real.pi / b)

/-- `γ = 1 - e^{-c₀}`. -/
noncomputable def momentGamma (b : ℕ) : ℝ := 1 - Real.exp (-spectralConst b)

/-- Signs of a `2k`-tuple: the first `k` coordinates `+1`, the last `k` coordinates `-1`. -/
def tupleSign (k : ℕ) (i : Fin (2 * k)) : ℤ := if i.val < k then 1 else -1

/-- Bernoulli characteristic modulus `|1-δ+δe(θ)|`. -/
noncomputable def bernMod (δ θ : ℝ) : ℝ := ‖((1 - δ : ℝ) : ℂ) + (δ : ℂ) * ePh θ‖

/-- The prime-`p` phase of a tuple: `h Σ_i ε_i b^{n_i}/(b^p-1)`. -/
noncomputable def tuplePhase (b : ℕ) (h : ℤ) (k p : ℕ) (n : Fin (2 * k) → ℕ) : ℝ :=
  (h : ℝ) * ∑ i, (tupleSign k i : ℝ) * ((b : ℝ) ^ (n i) / ((b : ℝ) ^ p - 1))

/-! ### Step 5: the Bernoulli factor -/

theorem bernMod_sq (δ θ : ℝ) :
    bernMod δ θ ^ 2 = 1 - 2 * (δ * (1 - δ)) * (1 - Real.cos (2 * Real.pi * θ)) := by
  rw [bernMod, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, ePh, Complex.exp_re, Complex.exp_im]
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * θ * 2)
  ring_nf at htrig ⊢
  nlinarith

theorem bernMod_nonneg (δ θ : ℝ) : 0 ≤ bernMod δ θ := norm_nonneg _

theorem bernMod_le_one {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (θ : ℝ) : bernMod δ θ ≤ 1 := by
  calc
    bernMod δ θ ≤ ‖((1 - δ : ℝ) : ℂ)‖ + ‖(δ : ℂ) * ePh θ‖ := norm_add_le _ _
    _ = (1 - δ) + δ := by
      rw [norm_mul, norm_ePh, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr h1)]
    _ = 1 := by ring

/-! ### Step 2: periodicity in each residue -/

theorem pow_sub_pow_mod_dvd (b n p : ℕ) :
    (b : ℤ) ^ p - 1 ∣ (b : ℤ) ^ n - (b : ℤ) ^ (n % p) := by
  conv_rhs =>
    lhs
    rw [← Nat.mod_add_div n p, pow_add, pow_mul]
  simpa [mul_sub] using
    (dvd_mul_of_dvd_right (sub_one_dvd_pow_sub_one ((b : ℤ) ^ p) (n / p))
      ((b : ℤ) ^ (n % p)))

theorem residuePhase_add_int (b n p : ℕ) (hb : 2 ≤ b) (hp : 1 ≤ p) :
    ∃ w : ℤ, (b : ℝ) ^ n / ((b : ℝ) ^ p - 1) =
      (b : ℝ) ^ (n % p) / ((b : ℝ) ^ p - 1) + w := by
  obtain ⟨w, hw⟩ := pow_sub_pow_mod_dvd b n p
  refine ⟨w, ?_⟩
  have hden : (b : ℝ) ^ p - 1 ≠ 0 := by
    have hb' : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    have : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ hb' (Nat.ne_of_gt hp)
    linarith
  have hwR : (b : ℝ) ^ n - (b : ℝ) ^ (n % p) =
      ((b : ℝ) ^ p - 1) * (w : ℝ) := by
    exact_mod_cast hw
  apply (div_eq_iff hden).2
  rw [add_mul, div_mul_cancel₀ _ hden]
  nlinarith

theorem bernMod_tuplePhase_mod (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (k p : ℕ) (hp : 1 ≤ p) (δ : ℝ)
    (n : Fin (2 * k) → ℕ) :
    bernMod δ (tuplePhase b h k p n) = bernMod δ (tuplePhase b h k p (fun i => n i % p)) := by
  classical
  choose w hw using fun i : Fin (2 * k) => residuePhase_add_int b (n i) p hb hp
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
  have hphase : tuplePhase b h k p n = tuplePhase b h k p (fun i => n i % p) +
      ((h * ∑ i, tupleSign k i * w i : ℤ) : ℝ) := by
    unfold tuplePhase
    rw [hsum]
    push_cast
    ring
  unfold bernMod
  rw [hphase, ePh_add_int]

/-! ### Spectral-gap preliminaries -/

/-- Negating a phase conjugates its unit exponential. -/
theorem ePh_neg (x : ℝ) : ePh (-x) = conj (ePh x) := by
  unfold ePh
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The real part of `ePh x` is `cos (2πx)`. -/
theorem ePh_re (x : ℝ) : (ePh x).re = Real.cos (2 * Real.pi * x) := by
  simp [ePh, Complex.exp_re]

/-- On the part of a period at distance at least `1/(2b)` from either endpoint, the cosine
loses at least `spectralConst b` from its maximum. -/
theorem cos_two_pi_le_cos_pi_div {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx0 : 1 / (2 * (b : ℝ)) ≤ x) (hx1 : x ≤ 1 - 1 / (2 * (b : ℝ))) :
    Real.cos (2 * Real.pi * x) ≤ Real.cos (Real.pi / b) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith
    · have hbase : 1 / (b : ℝ) ≤ 2 * x := by
        calc
          1 / (b : ℝ) = 2 * (1 / (2 * (b : ℝ))) := by field_simp
          _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx0 (by norm_num)
      calc
        Real.pi / (b : ℝ) = Real.pi * (1 / (b : ℝ)) := by ring
        _ ≤ Real.pi * (2 * x) := mul_le_mul_of_nonneg_left hbase hpi.le
        _ = 2 * Real.pi * x := by ring
  · have hcos : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (1 - x)) := by
      rw [show 2 * Real.pi * x = 2 * Real.pi - 2 * Real.pi * (1 - x) by ring,
        Real.cos_two_pi_sub]
    rw [hcos]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have : x ≥ 1 / 2 := le_of_not_ge hx
      nlinarith
    · have hbase : 1 / (b : ℝ) ≤ 2 * (1 - x) := by
        calc
          1 / (b : ℝ) = 2 * (1 / (2 * (b : ℝ))) := by field_simp
          _ ≤ 2 * (1 - x) := by nlinarith
      calc
        Real.pi / (b : ℝ) = Real.pi * (1 / (b : ℝ)) := by ring
        _ ≤ Real.pi * (2 * (1 - x)) := mul_le_mul_of_nonneg_left hbase hpi.le
        _ = 2 * Real.pi * (1 - x) := by ring

/-- Exact phase of the anchor residue `p-(e+1)` when the frequency has base-`b` factor
`b^e`.  The main term is the nonintegral rational `m/b`; the second factor is the small
finite-period correction. -/
theorem anchor_phase_formula (b e m p : ℕ) (hb : 2 ≤ b) (hep : e + 1 ≤ p) :
    (((b ^ e * m : ℕ) : ℝ) * residuePhase b p (p - (e + 1))) =
      (m : ℝ) / b * (1 + 1 / ((b : ℝ) ^ p - 1)) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hp : 0 < p := lt_of_lt_of_le (by omega) hep
  have hden : (b : ℝ) ^ p - 1 ≠ 0 := by
    have : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ hbR hp.ne'
    linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hbR)
  unfold residuePhase
  rw [Nat.cast_mul, Nat.cast_pow]
  field_simp
  have heq : e + (p - (e + 1)) + 1 = p := by omega
  have hpow : (b : ℝ) ^ e * (b : ℝ) ^ (p - (e + 1)) * b = (b : ℝ) ^ p := by
    rw [← pow_add, ← pow_succ, heq]
  rw [show (b : ℝ) ^ p - 1 + 1 = (b : ℝ) ^ p by ring]
  calc
    (b : ℝ) ^ e * (m : ℝ) * (b : ℝ) ^ (p - (e + 1)) * b =
        (m : ℝ) * ((b : ℝ) ^ e * (b : ℝ) ^ (p - (e + 1)) * b) := by ring
    _ = (m : ℝ) * (b : ℝ) ^ p := by rw [hpow]

/-- A perturbation of a nonintegral rational with denominator `b` by at most `1/(2b)`
still has a representative in the central part `[1/(2b), 1-1/(2b)]` of a period. -/
theorem rational_phase_central {b m : ℕ} (hb : 2 ≤ b) (hm : ¬ b ∣ m)
    {ε : ℝ} (hε : |ε| ≤ 1 / (2 * (b : ℝ))) :
    ∃ z : ℤ, 1 / (2 * (b : ℝ)) ≤ (m : ℝ) / b + ε - z ∧
      (m : ℝ) / b + ε - z ≤ 1 - 1 / (2 * (b : ℝ)) := by
  have hbpos : 0 < b := by omega
  have hrpos : 0 < m % b := Nat.pos_of_ne_zero (fun hr => hm (Nat.dvd_of_mod_eq_zero hr))
  have hrlt : m % b < b := Nat.mod_lt _ hbpos
  refine ⟨(m / b : ℕ), ?_⟩
  have hmdecomp : (m : ℝ) / b - (m / b : ℕ) = (m % b : ℕ) / b := by
    have hn := Nat.mod_add_div m b
    have hnR : ((m % b : ℕ) : ℝ) + (b : ℝ) * ((m / b : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast hn
    field_simp
    nlinarith [hnR]
  change 1 / (2 * (b : ℝ)) ≤ (m : ℝ) / b + ε - (m / b : ℕ) ∧
    (m : ℝ) / b + ε - (m / b : ℕ) ≤ 1 - 1 / (2 * (b : ℝ))
  rw [show (m : ℝ) / b + ε - (m / b : ℕ) =
      ((m : ℝ) / b - (m / b : ℕ)) + ε by ring, hmdecomp]
  constructor
  · have hrR : (1 : ℝ) ≤ ((m % b : ℕ) : ℝ) := by exact_mod_cast hrpos
    have helo : -(1 / (2 * (b : ℝ))) ≤ ε := (abs_le.mp hε).1
    have hbR : (0 : ℝ) < b := by positivity
    have hdiv : 2 * (1 / (2 * (b : ℝ))) ≤ ((m % b : ℕ) : ℝ) / b := by
      rw [show 2 * (1 / (2 * (b : ℝ))) = 1 / (b : ℝ) by ring]
      exact (div_le_div_iff_of_pos_right hbR).2 hrR
    nlinarith
  · have hrR : ((m % b : ℕ) : ℝ) ≤ (b : ℝ) - 1 := by
      have hrNat : m % b + 1 ≤ b := by omega
      have hrNatR : ((m % b : ℕ) : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hrNat
      linarith
    have hehi : ε ≤ 1 / (2 * (b : ℝ)) := (abs_le.mp hε).2
    have hbR : (0 : ℝ) < b := by positivity
    have hdiv : ((m % b : ℕ) : ℝ) / b ≤ 1 - 2 * (1 / (2 * (b : ℝ))) := by
      rw [show 1 - 2 * (1 / (2 * (b : ℝ))) = ((b : ℝ) - 1) / b by field_simp]
      exact (div_le_div_iff_of_pos_right hbR).2 hrR
    nlinarith

/-- A phase within `1/(2b)` of a rational `m/b` with `b ∤ m` incurs the spectral loss. -/
theorem cos_two_pi_le_of_near_rational {b m : ℕ} (hb : 2 ≤ b) (hm : ¬ b ∣ m)
    {x : ℝ} (hx : |x - (m : ℝ) / b| ≤ 1 / (2 * (b : ℝ))) :
    Real.cos (2 * Real.pi * x) ≤ Real.cos (Real.pi / b) := by
  obtain ⟨z, hz0, hz1⟩ :=
    rational_phase_central hb hm (ε := x - (m : ℝ) / b) hx
  have harg : (m : ℝ) / b + (x - (m : ℝ) / b) - (z : ℝ) = x - z := by ring
  rw [harg] at hz0 hz1
  have hperiod : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x - z)) := by
    rw [show 2 * Real.pi * (x - z) = 2 * Real.pi * x - (z : ℝ) * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  rw [hperiod]
  exact cos_two_pi_le_cos_pi_div hb hz0 hz1

/-- The finite-period correction to the anchor phase and a sufficiently short tail phase
together move the rational main term `m/b` by at most `1/(4b)`. -/
theorem anchor_tail_phase_error (b e m H K p t : ℕ) (hb : 2 ≤ b)
    (hH : H = b ^ e * m) (hK : e + 1 ≤ K) (hlarge : 16 * H ≤ b ^ K)
    (hp : 2 * K < p) (ht : t < p - K) :
    |(H : ℝ) * (residuePhase b p (p - (e + 1)) - residuePhase b p t) -
        (m : ℝ) / b| ≤ 1 / (4 * (b : ℝ)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hep : e + 1 ≤ p := by omega
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
  have hlargeR : (16 : ℝ) * H ≤ (b : ℝ) ^ K := by exact_mod_cast hlarge
  have htailCross : (8 : ℝ) * b * H * (b : ℝ) ^ t ≤ (b : ℝ) ^ p - 1 := by
    have hpowK : (b : ℝ) ^ (K + 1) = (b : ℝ) ^ K * b := by rw [pow_succ]
    rw [hpowK] at hpowmono
    have hmain : (16 : ℝ) * b * H * (b : ℝ) ^ t ≤ (b : ℝ) ^ p := by
      calc
        (16 : ℝ) * b * H * (b : ℝ) ^ t =
            (b : ℝ) ^ t * ((16 : ℝ) * H) * b := by ring
        _ ≤ (b : ℝ) ^ t * (b : ℝ) ^ K * b := by gcongr
        _ ≤ (b : ℝ) ^ p := by simpa [mul_assoc] using hpowmono
    nlinarith
  have htail : (H : ℝ) * residuePhase b p t ≤ 1 / (8 * (b : ℝ)) := by
    unfold residuePhase
    rw [show (H : ℝ) * ((b : ℝ) ^ t / ((b : ℝ) ^ p - 1)) =
      ((H : ℝ) * (b : ℝ) ^ t) / ((b : ℝ) ^ p - 1) by ring]
    rw [div_le_div_iff₀ hdenpos (by positivity : (0 : ℝ) < 8 * b)]
    nlinarith [htailCross]
  have hmH : m ≤ H := by
    rw [hH]
    exact Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
  have hcorrCross : (8 : ℝ) * m ≤ (b : ℝ) ^ p - 1 := by
    have hKp : K ≤ p := by omega
    have hpowKp : (b : ℝ) ^ K ≤ (b : ℝ) ^ p :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) hKp
    have hbig : (16 : ℝ) * H ≤ (b : ℝ) ^ p := hlargeR.trans hpowKp
    have hmHR : (m : ℝ) ≤ H := by exact_mod_cast hmH
    nlinarith
  have hcorr : (m : ℝ) / b / ((b : ℝ) ^ p - 1) ≤ 1 / (8 * (b : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * b)).2
    calc
      (m : ℝ) / b / ((b : ℝ) ^ p - 1) * (8 * b) =
          8 * (m : ℝ) / ((b : ℝ) ^ p - 1) := by field_simp
      _ ≤ 1 := (div_le_one hdenpos).2 hcorrCross
  have hanchor := anchor_phase_formula b e m p hb hep
  rw [← hH] at hanchor
  have herr :
      (H : ℝ) * (residuePhase b p (p - (e + 1)) - residuePhase b p t) -
          (m : ℝ) / b =
        (m : ℝ) / b / ((b : ℝ) ^ p - 1) - (H : ℝ) * residuePhase b p t := by
    rw [mul_sub, hanchor]
    ring
  rw [herr]
  have hcorr0 : 0 ≤ (m : ℝ) / b / ((b : ℝ) ^ p - 1) := by positivity
  have htail0 : 0 ≤ (H : ℝ) * residuePhase b p t := by
    unfold residuePhase
    positivity
  calc
    |(m : ℝ) / b / ((b : ℝ) ^ p - 1) - (H : ℝ) * residuePhase b p t| ≤
        (m : ℝ) / b / ((b : ℝ) ^ p - 1) + (H : ℝ) * residuePhase b p t := by
      simpa [abs_of_nonneg hcorr0, abs_of_nonneg htail0] using
        (abs_sub ((m : ℝ) / b / ((b : ℝ) ^ p - 1))
          ((H : ℝ) * residuePhase b p t))
    _ ≤ 1 / (8 * (b : ℝ)) + 1 / (8 * (b : ℝ)) := add_le_add hcorr htail
    _ = 1 / (4 * (b : ℝ)) := by ring

/-- Every anchor/tail pair selected by the spectral-gap argument loses at least
`spectralConst b` from the maximal cosine value. -/
theorem anchor_tail_cos_le (b e m H K p t : ℕ) (hb : 2 ≤ b) (hm : ¬ b ∣ m)
    (hH : H = b ^ e * m) (hK : e + 1 ≤ K) (hlarge : 16 * H ≤ b ^ K)
    (hp : 2 * K < p) (ht : t < p - K) :
    Real.cos (2 * Real.pi * ((H : ℝ) *
      (residuePhase b p (p - (e + 1)) - residuePhase b p t))) ≤
        Real.cos (Real.pi / b) := by
  apply cos_two_pi_le_of_near_rational hb hm
  exact (anchor_tail_phase_error b e m H K p t hb hH hK hlarge hp ht).trans (by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * b)
      (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith)

/-- If a row and column of a square sum each contain `L` entries losing at least `c`,
and the two selected arms are disjoint, the whole sum loses at least `2Lc`. -/
theorem double_sum_le_of_anchor (p L a : ℕ) (C : ℕ → ℕ → ℝ) (c : ℝ)
    (ha : a < p) (hLa : L ≤ a)
    (hone : ∀ r < p, ∀ t < p, C r t ≤ 1)
    (hleft : ∀ t < L, C a t ≤ 1 - c)
    (hright : ∀ r < L, C r a ≤ 1 - c) :
    (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, C r t) ≤
      (p : ℝ) ^ 2 - 2 * L * c := by
  let I : ℕ → ℕ → ℝ := fun r t =>
    (if r = a ∧ t < L then c else 0) + (if t = a ∧ r < L then c else 0)
  have hpoint (r : ℕ) (hr : r < p) (t : ℕ) (ht : t < p) : I r t ≤ 1 - C r t := by
    dsimp [I]
    by_cases hra : r = a
    · subst r
      have hnot : ¬a < L := by omega
      by_cases htL : t < L
      · simp [htL, hnot]
        linarith [hleft t htL]
      · simp [htL, hnot]
        linarith [hone a ha t ht]
    · by_cases hta : t = a
      · subst t
        by_cases hrL : r < L
        · simp [hra, hrL]
          linarith [hright r hrL]
        · simp [hra, hrL]
          linarith [hone r hr a ha]
      · simp [hra, hta]
        linarith [hone r hr t ht]
  have hsum : (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, I r t) ≤
      ∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, (1 - C r t) := by
    exact Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun t ht =>
      hpoint r (Finset.mem_range.mp hr) t (Finset.mem_range.mp ht)
  have hIsum : (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, I r t) = 2 * L * c := by
    dsimp [I]
    rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_add_distrib)]
    rw [Finset.sum_add_distrib]
    have hf : (Finset.range p).filter (fun t => t < L) = Finset.range L := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hrow (r : ℕ) : (∑ t ∈ Finset.range p, (if r = a ∧ t < L then c else 0)) =
        if r = a then L * c else 0 := by
      by_cases hra : r = a
      · simp [hra, Finset.sum_ite, hf]
      · simp [hra]
    have hfirst : (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        (if r = a ∧ t < L then c else 0)) = L * c := by
      simp_rw [hrow]
      simp [ha]
    have hsecond : (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        (if t = a ∧ r < L then c else 0)) = L * c := by
      rw [Finset.sum_comm]
      simpa [and_comm] using hfirst
    rw [hfirst, hsecond]
    ring
  have hDsum : (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, (1 - C r t)) =
      (p : ℝ) ^ 2 - ∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p, C r t := by
    simp_rw [Finset.sum_sub_distrib]
    simp
    ring
  rw [hIsum, hDsum] at hsum
  linarith

/-- The squared local mean is the normalized double cosine sum of phase differences. -/
theorem localMean_norm_sq_eq (b : ℕ) (h : ℤ) (p : ℕ) (hp : 0 < p) :
    ‖localMean b h p‖ ^ 2 =
      (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        Real.cos (2 * Real.pi * ((h : ℝ) *
          (residuePhase b p r - residuePhase b p t)))) / (p : ℝ) ^ 2 := by
  let z : ℕ → ℂ := fun r => ePh ((h : ℝ) * residuePhase b p r)
  let S : ℂ := ∑ r ∈ Finset.range p, z r
  have he (r t : ℕ) :
      z r * conj (z t) = ePh ((h : ℝ) * (residuePhase b p r - residuePhase b p t)) := by
    dsimp [z]
    rw [← ePh_neg]
    unfold ePh
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmul : S * conj S =
      ∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        ePh ((h : ℝ) * (residuePhase b p r - residuePhase b p t)) := by
    dsimp [S]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact he r t
  have hnormS : ‖S‖ ^ 2 =
      ∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        Real.cos (2 * Real.pi * ((h : ℝ) *
          (residuePhase b p r - residuePhase b p t))) := by
    have hre := congrArg Complex.re hmul
    rw [Complex.mul_conj] at hre
    simpa only [Complex.normSq_eq_norm_sq, Complex.ofReal_re, Complex.re_sum, ePh_re] using hre
  change ‖S / (p : ℂ)‖ ^ 2 = _
  rw [norm_div, Complex.norm_natCast]
  rw [show (‖S‖ / (p : ℝ)) ^ 2 = ‖S‖ ^ 2 / (p : ℝ) ^ 2 by ring, hnormS]

/-! ### Step 7: the one-prime spectral gap -/

theorem localMean_normSq_le (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ < p → ‖localMean b h p‖ ^ 2 ≤ 1 - spectralConst b / p := by
  have hH0 : h.natAbs ≠ 0 := (Int.natAbs_pos.mpr hh).ne'
  obtain ⟨e, m, hm, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hH0 b (by omega : b ≠ 1)
  let K : ℕ := e + 1 + 16 * h.natAbs
  have heK : e + 1 ≤ K := by simp [K]
  have hlarge : 16 * h.natAbs ≤ b ^ K := by
    have hlinR : (K : ℝ) + 1 ≤ (2 : ℝ) ^ K := by
      have hbern := one_add_mul_sub_le_pow (a := (2 : ℝ)) (by norm_num) K
      norm_num at hbern ⊢
      linarith
    have hlin : K + 1 ≤ 2 ^ K := by exact_mod_cast hlinR
    calc
      16 * h.natAbs ≤ K + 1 := by dsimp [K]; omega
      _ ≤ 2 ^ K := hlin
      _ ≤ b ^ K := Nat.pow_le_pow_left hb K
  refine ⟨2 * K, fun p hp => ?_⟩
  have hp0 : 0 < p := by omega
  let a := p - (e + 1)
  let L := p - K
  let C : ℕ → ℕ → ℝ := fun r t =>
    Real.cos (2 * Real.pi * ((h.natAbs : ℝ) *
      (residuePhase b p r - residuePhase b p t)))
  have ha : a < p := by dsimp [a]; omega
  have hLa : L ≤ a := by dsimp [L, a]; omega
  have hone : ∀ r < p, ∀ t < p, C r t ≤ 1 := by
    intro r hr t ht
    exact Real.cos_le_one _
  have hleft : ∀ t < L, C a t ≤ 1 - spectralConst b := by
    intro t ht
    dsimp [C, a]
    have hcos := anchor_tail_cos_le b e m h.natAbs K p t hb hm hfac heK hlarge hp ht
    convert hcos using 1 <;> simp [spectralConst]
  have hright : ∀ r < L, C r a ≤ 1 - spectralConst b := by
    intro r hr
    have hcos := anchor_tail_cos_le b e m h.natAbs K p r hb hm hfac heK hlarge hp hr
    dsimp [C, a]
    rw [show (h.natAbs : ℝ) *
        (residuePhase b p r - residuePhase b p (p - (e + 1))) =
      -((h.natAbs : ℝ) *
        (residuePhase b p (p - (e + 1)) - residuePhase b p r)) by ring]
    rw [show 2 * Real.pi * -((h.natAbs : ℝ) *
        (residuePhase b p (p - (e + 1)) - residuePhase b p r)) =
      -(2 * Real.pi * ((h.natAbs : ℝ) *
        (residuePhase b p (p - (e + 1)) - residuePhase b p r))) by ring,
      Real.cos_neg]
    convert hcos using 1 <;> simp [spectralConst]
  have hsum := double_sum_le_of_anchor p L a C (spectralConst b) ha hLa hone hleft hright
  have hcosSign (x : ℝ) :
      Real.cos (2 * Real.pi * ((h : ℝ) * x)) =
        Real.cos (2 * Real.pi * ((h.natAbs : ℝ) * x)) := by
    cases h with
    | ofNat n => simp
    | negSucc n =>
      rw [show (((Int.negSucc n : ℤ) : ℝ) * x) = -(((n + 1 : ℕ) : ℝ) * x) by
        norm_num [Int.cast_negSucc]
        ring]
      rw [show 2 * Real.pi * -(((n + 1 : ℕ) : ℝ) * x) =
        -(2 * Real.pi * (((n + 1 : ℕ) : ℝ) * x)) by ring, Real.cos_neg]
      rfl
  rw [localMean_norm_sq_eq b h p hp0]
  have hsum' :
      (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        Real.cos (2 * Real.pi * ((h : ℝ) *
          (residuePhase b p r - residuePhase b p t)))) ≤
        (p : ℝ) ^ 2 - 2 * L * spectralConst b := by
    simpa only [C, hcosSign] using hsum
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  apply (div_le_iff₀ (sq_pos_of_pos hpR)).2
  have hL : 2 * L ≥ p := by
    dsimp [L]
    omega
  have hc : 0 ≤ spectralConst b := by
    unfold spectralConst
    linarith [Real.neg_one_le_cos (Real.pi / b), Real.cos_le_one (Real.pi / b)]
  calc
    (∑ r ∈ Finset.range p, ∑ t ∈ Finset.range p,
        Real.cos (2 * Real.pi * ((h : ℝ) *
          (residuePhase b p r - residuePhase b p t)))) ≤
        (p : ℝ) ^ 2 - 2 * L * spectralConst b := hsum'
    _ ≤ (1 - spectralConst b / p) * (p : ℝ) ^ 2 := by
      have hLR : (p : ℝ) ≤ 2 * L := by exact_mod_cast hL
      field_simp
      nlinarith

/-! ### Step 6: exact second moment over residues -/

/-- The exponential of a finite real sum is the product of its exponentials. -/
theorem ePh_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ePh (∑ i, x i) = ∏ i, ePh (x i) := by
  unfold ePh
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/-- A `2k`-fold product with one value on each half splits into two `k`th powers. -/
theorem prod_fin_two_blocks (k : ℕ) (z w : ℂ) :
    (∏ i : Fin (2 * k), if i.val < k then z else w) = z ^ k * w ^ k := by
  classical
  have hcard : ((Finset.univ.filter fun i : Fin (2 * k) => i.val < k).card) = k := by
    rw [Fin.card_filter_val_lt]
    omega
  have hcardNot : ((Finset.univ.filter fun i : Fin (2 * k) => ¬i.val < k).card) = k := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * k)))) (p := fun i => i.val < k)
    simp only [hcard, Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hcard, hcardNot]

/-- The tuple phase exponential is the product of its signed coordinate phases. -/
theorem ePh_tuplePhase_prod (b : ℕ) (h : ℤ) (k p : ℕ)
    (r : Fin (2 * k) → Fin p) :
    ePh (tuplePhase b h k p (fun i => (r i).val)) =
      ∏ i, ePh ((tupleSign k i : ℝ) * (h : ℝ) * residuePhase b p (r i).val) := by
  unfold tuplePhase
  have harg :
      (h : ℝ) * ∑ i, (tupleSign k i : ℝ) *
          ((b : ℝ) ^ (r i).val / ((b : ℝ) ^ p - 1)) =
        ∑ i, (tupleSign k i : ℝ) * (h : ℝ) * residuePhase b p (r i).val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold residuePhase
    ring
  rw [harg, ePh_sum]

/-- The complete tuple exponential sum factorizes into a power and its conjugate. -/
theorem tuple_ePh_sum (b : ℕ) (h : ℤ) (k p : ℕ) :
    (∑ r : Fin (2 * k) → Fin p, ePh (tuplePhase b h k p (fun i => (r i).val))) =
      (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) ^ k *
        conj (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) ^ k := by
  classical
  let z : ℂ := ∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)
  calc
    (∑ r : Fin (2 * k) → Fin p, ePh (tuplePhase b h k p (fun i => (r i).val))) =
        ∑ r : Fin (2 * k) → Fin p,
          ∏ i, ePh ((tupleSign k i : ℝ) * (h : ℝ) * residuePhase b p (r i).val) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact ePh_tuplePhase_prod b h k p r
    _ = ∏ i : Fin (2 * k),
          ∑ x : Fin p, ePh ((tupleSign k i : ℝ) * (h : ℝ) * residuePhase b p x.val) := by
      rw [Fintype.prod_sum]
    _ = ∏ i : Fin (2 * k), if i.val < k then z else conj z := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hik : i.val < k
      · rw [if_pos hik]
        simp only [tupleSign, hik, if_pos, Int.cast_one, one_mul]
        exact rfl
      · rw [if_neg hik]
        simp only [tupleSign, hik, if_false, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
        change (∑ x : Fin p, ePh (-((h : ℝ) * residuePhase b p x.val))) = conj z
        calc
          (∑ x : Fin p, ePh (-((h : ℝ) * residuePhase b p x.val))) =
              ∑ x : Fin p, conj (ePh ((h : ℝ) * residuePhase b p x.val)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [ePh_neg]
          _ = conj (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) := by
            rw [map_sum]
          _ = conj z := rfl
    _ = z ^ k * conj z ^ k := prod_fin_two_blocks k z (conj z)
    _ = (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) ^ k *
        conj (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) ^ k := rfl

/-- `localMean` written as a sum over `Fin p`. -/
theorem localMean_eq_fin_sum (b : ℕ) (h : ℤ) (p : ℕ) :
    localMean b h p =
      (∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)) / (p : ℂ) := by
  unfold localMean
  rw [← Fin.sum_univ_eq_sum_range]

/-- A power times the conjugate power is the corresponding even power of the norm. -/
theorem pow_mul_conj_pow_eq_norm_pow (z : ℂ) (k : ℕ) :
    z ^ k * conj z ^ k = (‖z‖ ^ (2 * k) : ℝ) := by
  rw [← mul_pow, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, ← pow_mul]

/-- The normalized complete tuple exponential sum is the even norm power of `localMean`. -/
theorem tuple_ePh_mean_eq_norm_pow (b : ℕ) (h : ℤ) (k p : ℕ) (hp : 0 < p) :
    (∑ r : Fin (2 * k) → Fin p, ePh (tuplePhase b h k p (fun i => (r i).val))) /
        (p : ℂ) ^ (2 * k) = (‖localMean b h p‖ ^ (2 * k) : ℝ) := by
  let S : ℂ := ∑ x : Fin p, ePh ((h : ℝ) * residuePhase b p x.val)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hS : S = (p : ℂ) * localMean b h p := by
    rw [localMean_eq_fin_sum]
    dsimp [S]
    field_simp
  rw [tuple_ePh_sum]
  change S ^ k * conj S ^ k / (p : ℂ) ^ (2 * k) = _
  rw [hS, map_mul, map_natCast]
  rw [mul_pow, mul_pow]
  rw [show (p : ℂ) ^ (2 * k) = (p : ℂ) ^ k * (p : ℂ) ^ k by rw [two_mul, pow_add]]
  field_simp
  exact pow_mul_conj_pow_eq_norm_pow _ _

/-- The complete signed-tuple cosine sum is the local-mean norm power times its cardinality. -/
theorem tuple_cos_sum_eq (b : ℕ) (h : ℤ) (k p : ℕ) (hp : 0 < p) :
    (∑ r : Fin (2 * k) → Fin p,
        Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val))) =
      (p : ℝ) ^ (2 * k) * ‖localMean b h p‖ ^ (2 * k) := by
  have hpCpow : (p : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  have hmean := tuple_ePh_mean_eq_norm_pow b h k p hp
  have hsum :
      (∑ r : Fin (2 * k) → Fin p, ePh (tuplePhase b h k p (fun i => (r i).val))) =
        ((‖localMean b h p‖ ^ (2 * k) : ℝ) : ℂ) * (p : ℂ) ^ (2 * k) :=
    (div_eq_iff hpCpow).mp hmean
  have hpPow : (p : ℂ) ^ (2 * k) = (((p : ℝ) ^ (2 * k) : ℝ) : ℂ) := by
    norm_cast
  have hre := congrArg Complex.re hsum
  rw [hpPow] at hre
  simpa only [Complex.re_sum, ePh_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_comm] using hre

theorem residueTuple_mean_sq (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (k p : ℕ) (hp : 0 < p) (δ : ℝ) :
    (∑ r : Fin (2 * k) → Fin p, bernMod δ (tuplePhase b h k p (fun i => (r i).val)) ^ 2) /
        (p : ℝ) ^ (2 * k) =
      1 - 2 * (δ * (1 - δ)) * (1 - ‖localMean b h p‖ ^ (2 * k)) := by
  let P : ℝ := (p : ℝ) ^ (2 * k)
  let L : ℝ := ‖localMean b h p‖ ^ (2 * k)
  have hPpos : 0 < P := pow_pos (by exact_mod_cast hp) _
  have hcos :
      (∑ r : Fin (2 * k) → Fin p,
          Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val))) = P * L := by
    exact tuple_cos_sum_eq b h k p hp
  have hcard :
      ((Fintype.card (Fin (2 * k) → Fin p) : ℕ) : ℝ) = P := by
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_pow]
    rfl
  have hnum :
      (∑ r : Fin (2 * k) → Fin p,
          bernMod δ (tuplePhase b h k p (fun i => (r i).val)) ^ 2) =
        P - 2 * (δ * (1 - δ)) *
          (P - ∑ r : Fin (2 * k) → Fin p,
            Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val))) := by
    calc
      (∑ r : Fin (2 * k) → Fin p,
          bernMod δ (tuplePhase b h k p (fun i => (r i).val)) ^ 2) =
          ∑ r : Fin (2 * k) → Fin p,
            ((1 - 2 * (δ * (1 - δ))) + 2 * (δ * (1 - δ)) *
              Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val))) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [bernMod_sq]
        ring
      _ = P * (1 - 2 * (δ * (1 - δ))) + 2 * (δ * (1 - δ)) *
          ∑ r : Fin (2 * k) → Fin p,
            Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [hcard]
      _ = P - 2 * (δ * (1 - δ)) *
          (P - ∑ r : Fin (2 * k) → Fin p,
            Real.cos (2 * Real.pi * tuplePhase b h k p (fun i => (r i).val))) := by ring
  rw [hnum, hcos]
  change (P - 2 * (δ * (1 - δ)) * (P - P * L)) / P =
    1 - 2 * (δ * (1 - δ)) * (1 - L)
  field_simp

/-! ### Step 8: the local first-moment bound -/

theorem momentGamma_pos (b : ℕ) (hb : 2 ≤ b) : 0 < momentGamma b := by
  have hbpos : (0 : ℝ) < b := by positivity
  have hxpos : 0 < Real.pi / (b : ℝ) := div_pos Real.pi_pos hbpos
  have hxle : Real.pi / (b : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hbpos).2
    have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / (b : ℝ)) < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hxle hxpos
  have hc : 0 < spectralConst b := by
    rw [spectralConst]
    rw [Real.cos_zero] at hcos
    linarith
  rw [momentGamma]
  have hexp : Real.exp (-spectralConst b) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  linarith

/-- The square-root loss produced by Cauchy--Schwarz is absorbed by an exponential. -/
theorem sqrt_one_sub_two_mul_le_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.sqrt (1 - 2 * x) ≤ Real.exp (-x) := by
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le]
  rw [Real.sq_sqrt (by nlinarith)]
  rw [← Real.exp_nat_mul]
  simpa only [Nat.cast_ofNat, show (2 : ℝ) * -x = -(2 * x) by ring] using
    Real.one_sub_le_exp_neg (2 * x)

/-- The chord from `0` to `1` for `1 - exp (-c t)`, continued monotonically after `1`. -/
theorem momentGamma_mul_min_le_one_sub_exp {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    (1 - Real.exp (-c)) * min t 1 ≤ 1 - Real.exp (-c * t) := by
  by_cases ht1 : t ≤ 1
  · have hconv : Real.exp ((1 - t) * 0 + t * (-c)) ≤
        (1 - t) * Real.exp 0 + t * Real.exp (-c) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) ht (by ring)
    have hconv' : Real.exp (-c * t) ≤ 1 - t + t * Real.exp (-c) := by
      calc
        Real.exp (-c * t) = Real.exp ((1 - t) * 0 + t * (-c)) := by congr 1 <;> ring
        _ ≤ (1 - t) * Real.exp 0 + t * Real.exp (-c) := hconv
        _ = 1 - t + t * Real.exp (-c) := by rw [Real.exp_zero]; ring
    rw [min_eq_left ht1]
    nlinarith [hconv']
  · have hone : 1 ≤ t := le_of_not_ge ht1
    have harg : -c * t ≤ -c := by nlinarith
    have hexp := Real.exp_le_exp.mpr harg
    rw [min_eq_right hone]
    linarith

theorem residueTuple_mean_le (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ < p → ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ r : Fin (2 * k) → Fin p, bernMod δ (tuplePhase b h k p (fun i => (r i).val))) /
          (p : ℝ) ^ (2 * k) ≤
        Real.exp (-(momentGamma b) * (δ * (1 - δ)) * min ((k : ℝ) / p) 1) := by
  obtain ⟨P₀, hgap⟩ := localMean_normSq_le b hb h hh
  refine ⟨P₀, fun p hp k hk δ hδ0 hδ1 => ?_⟩
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  let v : ℝ := δ * (1 - δ)
  let L : ℝ := ‖localMean b h p‖ ^ (2 * k)
  let T : ℝ := (k : ℝ) / p
  let A : ℝ :=
    (∑ r : Fin (2 * k) → Fin p,
      bernMod δ (tuplePhase b h k p (fun i => (r i).val))) / (p : ℝ) ^ (2 * k)
  have hc : 0 < spectralConst b := by
    have hgamma := momentGamma_pos b hb
    rw [momentGamma] at hgamma
    by_contra hnot
    have hc0 : spectralConst b ≤ 0 := le_of_not_gt hnot
    have hexp : 1 ≤ Real.exp (-spectralConst b) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hv0 : 0 ≤ v := mul_nonneg hδ0 (sub_nonneg.mpr hδ1)
  have hv4 : v ≤ 1 / 4 := by
    dsimp [v]
    nlinarith [sq_nonneg (δ - 1 / 2)]
  have hT0 : 0 ≤ T := div_nonneg (by positivity) hpR.le
  have hnormSq : ‖localMean b h p‖ ^ 2 ≤ 1 - spectralConst b / p := hgap p hp
  have hbase0 : 0 ≤ 1 - spectralConst b / p :=
    (sq_nonneg ‖localMean b h p‖).trans hnormSq
  have hbase1 : 1 - spectralConst b / p ≤ 1 := by
    exact sub_le_self _ (div_nonneg hc.le hpR.le)
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L ≤ 1 := by
    change ‖localMean b h p‖ ^ (2 * k) ≤ 1
    rw [pow_mul]
    calc
      (‖localMean b h p‖ ^ 2) ^ k ≤ (1 - spectralConst b / p) ^ k :=
        pow_le_pow_left₀ (sq_nonneg _) hnormSq k
      _ ≤ 1 ^ k := pow_le_pow_left₀ hbase0 hbase1 k
      _ = 1 := one_pow k
  have hLexp : L ≤ Real.exp (-spectralConst b * T) := by
    change ‖localMean b h p‖ ^ (2 * k) ≤ _
    rw [pow_mul]
    calc
      (‖localMean b h p‖ ^ 2) ^ k ≤ (1 - spectralConst b / p) ^ k :=
        pow_le_pow_left₀ (sq_nonneg _) hnormSq k
      _ ≤ (Real.exp (-(spectralConst b / p))) ^ k :=
        pow_le_pow_left₀ hbase0 (Real.one_sub_le_exp_neg _) k
      _ = Real.exp (-spectralConst b * T) := by
        rw [← Real.exp_nat_mul]
        dsimp [T]
        congr 1
        push_cast
        field_simp
  have hgammaLoss : momentGamma b * min T 1 ≤ 1 - L := by
    have hchord := momentGamma_mul_min_le_one_sub_exp (c := spectralConst b) (t := T) hc.le hT0
    exact (show momentGamma b * min T 1 ≤ 1 - Real.exp (-spectralConst b * T) by
      simpa only [momentGamma] using hchord).trans (sub_le_sub_left hLexp 1)
  let x : ℝ := v * (1 - L)
  have hx0 : 0 ≤ x := mul_nonneg hv0 (sub_nonneg.mpr hL1)
  have hxhalf : x ≤ 1 / 2 := by
    have honeL : 1 - L ≤ 1 := by linarith
    calc
      x ≤ v * 1 := mul_le_mul_of_nonneg_left honeL hv0
      _ ≤ 1 / 4 := by simpa using hv4
      _ ≤ 1 / 2 := by norm_num
  have hxgamma : momentGamma b * v * min T 1 ≤ x := by
    dsimp [x]
    calc
      momentGamma b * v * min T 1 = v * (momentGamma b * min T 1) := by ring
      _ ≤ v * (1 - L) := mul_le_mul_of_nonneg_left hgammaLoss hv0
  have hcard :
      ((Fintype.card (Fin (2 * k) → Fin p) : ℕ) : ℝ) = (p : ℝ) ^ (2 * k) := by
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_pow]
  have hcs : A ^ 2 ≤
      (∑ r : Fin (2 * k) → Fin p,
        bernMod δ (tuplePhase b h k p (fun i => (r i).val)) ^ 2) /
          (p : ℝ) ^ (2 * k) := by
    have h := sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset (Fin (2 * k) → Fin p)))
      (f := fun r => bernMod δ (tuplePhase b h k p (fun i => (r i).val)))
    simp only [Finset.card_univ] at h
    rw [hcard] at h
    exact h
  have hsq : A ^ 2 ≤ 1 - 2 * x := by
    rw [residueTuple_mean_sq b hb h k p hp0 δ] at hcs
    simpa only [A, x, v, L, mul_assoc] using hcs
  have hAsqrt : A ≤ Real.sqrt (1 - 2 * x) := Real.le_sqrt_of_sq_le hsq
  have hsqrt : Real.sqrt (1 - 2 * x) ≤ Real.exp (-x) :=
    sqrt_one_sub_two_mul_le_exp_neg hx0 hxhalf
  have hexp : Real.exp (-x) ≤ Real.exp (-(momentGamma b * v * min T 1)) :=
    Real.exp_le_exp.mpr (neg_le_neg hxgamma)
  simpa only [A, v, T, neg_mul, mul_assoc] using hAsqrt.trans (hsqrt.trans hexp)

/-! ### Step 4: the pairwise-coprime CRT abstraction -/

theorem crt_tuple_prod_mean {ι : Type*} (F : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ F, 0 < q i)
    (hcop : (F : Set ι).Pairwise (Function.onFun Nat.Coprime q)) (d : ℕ)
    (g : ι → (Fin d → ℕ) → ℝ) (hper : ∀ i ∈ F, ∀ n, g i n = g i (fun j => n j % q i)) :
    (∑ n : Fin d → Fin (∏ i ∈ F, q i), ∏ i ∈ F, g i (fun j => (n j).val)) /
        ((∏ i ∈ F, q i : ℕ) : ℝ) ^ d =
      ∏ i ∈ F, (∑ r : Fin d → Fin (q i), g i (fun j => (r j).val)) / (q i : ℝ) ^ d := by
  classical
  let a : F → ℕ := fun i => q i
  have ha : ∀ i : F, 0 < a i := fun i => hq i i.property
  let _ (i : F) : NeZero (a i) := ⟨Nat.ne_of_gt (ha i)⟩
  have hc : Pairwise (Function.onFun Nat.Coprime a) := by
    intro i j hij
    exact hcop i.property j.property (fun h => hij (Subtype.ext h))
  have hprod : 0 < ∏ i : F, a i := Finset.prod_pos fun _ _ => ha _
  let _ : NeZero (∏ i : F, a i) := ⟨Nat.ne_of_gt hprod⟩
  let crt : Fin (∏ i : F, a i) ≃ (∀ i : F, Fin (a i)) :=
    (ZMod.finEquiv (∏ i : F, a i)).toEquiv |>.trans
      ((ZMod.prodEquivPi a hc).toEquiv |>.trans
        (Equiv.piCongrRight fun i => (ZMod.finEquiv (a i)).symm.toEquiv))
  have hfin (n : ℕ) [NeZero n] (x : Fin n) : (ZMod.finEquiv n x).val = x.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  have hinv (n : ℕ) [NeZero n] (x : ZMod n) : ((ZMod.finEquiv n).symm x).val = x.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  have hcrt (x : Fin (∏ i : F, a i)) (i : F) :
      (crt x i).val = x.val % a i := by
    simp only [crt, Equiv.trans_apply]
    rw [Equiv.piCongrRight_apply, Pi.map_apply]
    change ((ZMod.finEquiv (a i)).symm
      (ZMod.prodEquivPi a hc (ZMod.finEquiv (∏ i : F, a i) x) i)).val = _
    rw [hinv, ZMod.prodEquivPi_apply, ZMod.castHom_apply]
    rw [ZMod.cast_eq_val, hfin, ZMod.val_natCast]
  let tupleCrt : (Fin d → Fin (∏ i : F, a i)) ≃
      (∀ i : F, Fin d → Fin (a i)) :=
    (Equiv.piCongrRight fun _ : Fin d => crt).trans (Equiv.piComm _)
  have htuple (n : Fin d → Fin (∏ i : F, a i)) (i : F) (j : Fin d) :
      (tupleCrt n i j).val = (n j).val % a i := by
    change (crt (n j) i).val = _
    exact hcrt (n j) i
  have hprod_eq : (∏ i ∈ F, q i) = ∏ i : F, a i := by
    change (∏ i ∈ F, q i) = ∏ i ∈ F.attach, q i
    exact (Finset.prod_attach F q).symm
  rw [hprod_eq]
  have hsum :
      (∑ n : Fin d → Fin (∏ i : F, a i), ∏ i ∈ F, g i (fun j => (n j).val)) =
        ∑ r : ∀ i : F, Fin d → Fin (a i), ∏ i : F, g i (fun j => (r i j).val) := by
    apply Fintype.sum_equiv tupleCrt
    intro n
    rw [Finset.prod_subtype F (p := fun x => x ∈ F) (by simp)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hper i i.property]
    congr 1
    funext j
    exact (htuple n i j).symm
  rw [hsum]
  rw [← Fintype.prod_sum (fun i (r : Fin d → Fin (a i)) =>
    g i (fun j => (r j).val))]
  rw [Finset.prod_subtype F (p := fun x => x ∈ F) (by simp)]
  simp only [Finset.prod_div_distrib]
  congr 1
  push_cast
  simp [a, Finset.prod_pow]

/-! ### Step 3: prefix-to-period transfer -/

/-- A sum over `a` complete residue blocks is `a` times the one-block sum. -/
theorem sum_range_mul_mod (Q a : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (a * Q), f (n % Q)) =
      (a : ℝ) * ∑ r ∈ Finset.range Q, f r := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.mul_add_mod_self_right]
      have hr : (∑ x ∈ Finset.range Q, f (x % Q)) = ∑ x ∈ Finset.range Q, f x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]
      rw [hr]
      push_cast
      ring

/-- A bounded periodic function has prefix mean at most its period mean plus `Q / N`. -/
theorem prefix_mean_one_le (Q N : ℕ) (hQ : 0 < Q) (hN : 1 ≤ N) (f : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hper : ∀ n, f n = f (n % Q)) :
    (∑ n : Fin N, f n.val) / (N : ℝ) ≤
      (∑ r : Fin Q, f r.val) / (Q : ℝ) + (Q : ℝ) / N := by
  let a := N / Q
  let R := N % Q
  let S : ℝ := ∑ r ∈ Finset.range Q, f r
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => h0 i
  have hblocks : (∑ n ∈ Finset.range (a * Q), f n) = (a : ℝ) * S := by
    calc
      (∑ n ∈ Finset.range (a * Q), f n) =
          ∑ n ∈ Finset.range (a * Q), f (n % Q) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hper n
      _ = (a : ℝ) * S := sum_range_mul_mod Q a f
  have htail : (∑ r ∈ Finset.range R, f (a * Q + r)) ≤ (Q : ℝ) := by
    calc
      (∑ r ∈ Finset.range R, f (a * Q + r)) ≤ ∑ _r ∈ Finset.range R, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => h1 _
      _ = (R : ℝ) := by simp
      _ ≤ (Q : ℝ) := by exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N hQ))
  have haQ : (a : ℝ) * Q ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N Q
  have hblockMean : (a : ℝ) * S / (N : ℝ) ≤ S / (Q : ℝ) := by
    apply (div_le_iff₀ hNpos).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hQpos).2
    calc
      (a : ℝ) * S * Q = S * ((a : ℝ) * Q) := by ring
      _ ≤ S * N := mul_le_mul_of_nonneg_left haQ hS0
      _ = S * (N : ℝ) := rfl
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  have hdecomp : a * Q + R = N := by
    simpa [a, R, Nat.mul_comm] using Nat.div_add_mod N Q
  have hsplit : (∑ x ∈ Finset.range N, f x) =
      (a : ℝ) * S + ∑ x ∈ Finset.range R, f (a * Q + x) := by
    rw [← hdecomp, Finset.sum_range_add, hblocks]
  rw [hsplit]
  change ((a : ℝ) * S + ∑ x ∈ Finset.range R, f (a * Q + x)) / (N : ℝ) ≤
    S / (Q : ℝ) + (Q : ℝ) / N
  calc
    ((a : ℝ) * S + ∑ x ∈ Finset.range R, f (a * Q + x)) / (N : ℝ)
        ≤ ((a : ℝ) * S + Q) / (N : ℝ) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl htail) (le_of_lt hNpos)
    _ = (a : ℝ) * S / N + (Q : ℝ) / N := by ring
    _ ≤ S / Q + (Q : ℝ) / N := add_le_add hblockMean le_rfl

/-- Split a sum over `(d + 1)`-tuples into its head and tail coordinates. -/
theorem sum_pi_succ {M d : ℕ} (H : (Fin (d + 1) → Fin M) → ℝ) :
    ∑ n, H n = ∑ x : Fin M, ∑ m : Fin d → Fin M, H (Fin.cons x m) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin M) H, Fintype.sum_prod_type]
  rfl

/-- The head-tail tuple split after coercing every coordinate to `ℕ`. -/
theorem sum_pi_succ_val {M d : ℕ} (G : (Fin (d + 1) → ℕ) → ℝ) :
    (∑ n : Fin (d + 1) → Fin M, G (fun j => (n j).val)) =
      ∑ x : Fin M, ∑ m : Fin d → Fin M, G (Fin.cons x.val (fun j => (m j).val)) := by
  rw [sum_pi_succ]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

theorem prefix_tuple_mean_le (Q d N : ℕ) (hQ : 0 < Q) (hN : 1 ≤ N) (G : (Fin d → ℕ) → ℝ)
    (h0 : ∀ n, 0 ≤ G n) (h1 : ∀ n, G n ≤ 1) (hper : ∀ n, G n = G (fun j => n j % Q)) :
    (∑ n : Fin d → Fin N, G (fun j => (n j).val)) / (N : ℝ) ^ d ≤
      (∑ r : Fin d → Fin Q, G (fun j => (r j).val)) / (Q : ℝ) ^ d + d * Q / N := by
  induction d with
  | zero =>
      simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, zero_div, add_zero,
        Fintype.sum_unique]
      exact le_of_eq (congrArg G (Subsingleton.elim _ _))
  | succ d ih =>
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
      have htailper (x : ℕ) (m : Fin d → ℕ) :
          G (Fin.cons x m) = G (Fin.cons x (fun j => m j % Q)) := by
        have heq : (fun j => (Fin.cons x m : Fin (d + 1) → ℕ) j % Q) =
            (fun j => (Fin.cons x (fun i : Fin d => m i % Q) : Fin (d + 1) → ℕ) j % Q) := by
          funext j
          refine Fin.cases ?_ (fun i => ?_) j
          · rfl
          · exact (Nat.mod_mod _ _).symm
        calc
          G (Fin.cons x m) =
              G (fun j => (Fin.cons x m : Fin (d + 1) → ℕ) j % Q) := hper _
          _ = G (fun j => (Fin.cons x (fun i : Fin d => m i % Q) :
              Fin (d + 1) → ℕ) j % Q) := congrArg G heq
          _ = G (Fin.cons x (fun j : Fin d => m j % Q)) :=
            (hper (Fin.cons x (fun j : Fin d => m j % Q))).symm
      let f : ℕ → ℝ := fun x =>
        (∑ r : Fin d → Fin Q, G (Fin.cons x (fun j => (r j).val))) / (Q : ℝ) ^ d
      have hf0 (x : ℕ) : 0 ≤ f x := by
        apply div_nonneg
        · exact Finset.sum_nonneg fun i _ => h0 _
        · positivity
      have hf1 (x : ℕ) : f x ≤ 1 := by
        apply (div_le_one (pow_pos hQpos d)).2
        calc
          (∑ r : Fin d → Fin Q, G (Fin.cons x (fun j => (r j).val))) ≤
              ∑ _r : Fin d → Fin Q, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 _
          _ = (Q : ℝ) ^ d := by simp
      have hfper (x : ℕ) : f x = f (x % Q) := by
        unfold f
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        have heq :
            (fun j => (Fin.cons x (fun i : Fin d => (r i).val) : Fin (d + 1) → ℕ) j % Q) =
            (fun j => (Fin.cons (x % Q) (fun i : Fin d => (r i).val) :
              Fin (d + 1) → ℕ) j % Q) := by
          funext j
          refine Fin.cases ?_ (fun i => ?_) j
          · exact (Nat.mod_mod _ _).symm
          · rfl
        calc
          G (Fin.cons x (fun j => (r j).val)) =
              G (fun j => (Fin.cons x (fun i : Fin d => (r i).val) :
                Fin (d + 1) → ℕ) j % Q) := hper _
          _ = G (fun j => (Fin.cons (x % Q) (fun i : Fin d => (r i).val) :
              Fin (d + 1) → ℕ) j % Q) := congrArg G heq
          _ = G (Fin.cons (x % Q) (fun j : Fin d => (r j).val)) :=
            (hper (Fin.cons (x % Q) (fun j : Fin d => (r j).val))).symm
      have hinner (x : Fin N) :
          (∑ m : Fin d → Fin N, G (Fin.cons x.val (fun j => (m j).val))) /
              (N : ℝ) ^ d ≤ f x.val + (d : ℝ) * Q / N := by
        exact ih (fun m => G (Fin.cons x.val m)) (fun m => h0 _) (fun m => h1 _)
          (fun m => htailper x.val m)
      have hsplitN :
          (∑ n : Fin (d + 1) → Fin N, G (fun j => (n j).val)) / (N : ℝ) ^ (d + 1) =
            (∑ x : Fin N,
              (∑ m : Fin d → Fin N, G (Fin.cons x.val (fun j => (m j).val))) /
                (N : ℝ) ^ d) / N := by
        rw [sum_pi_succ_val]
        rw [pow_succ]
        conv_lhs => rw [Finset.sum_div]
        conv_rhs => rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have hsplitQ :
          (∑ r : Fin (d + 1) → Fin Q, G (fun j => (r j).val)) / (Q : ℝ) ^ (d + 1) =
            (∑ x : Fin Q, f x.val) / Q := by
        rw [sum_pi_succ_val]
        unfold f
        rw [pow_succ]
        conv_lhs => rw [Finset.sum_div]
        conv_rhs => rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsplitN, hsplitQ]
      calc
        (∑ x : Fin N,
            (∑ m : Fin d → Fin N, G (Fin.cons x.val (fun j => (m j).val))) /
              (N : ℝ) ^ d) / N ≤
            (∑ x : Fin N, (f x.val + (d : ℝ) * Q / N)) / N :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hinner x) hNpos.le
        _ = (∑ x : Fin N, f x.val) / N + (d : ℝ) * Q / N := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp
        _ ≤ ((∑ x : Fin Q, f x.val) / Q + (Q : ℝ) / N) + (d : ℝ) * Q / N :=
          add_le_add (prefix_mean_one_le Q N hQ hN f hf0 hf1 hfper) le_rfl
        _ = (∑ x : Fin Q, f x.val) / Q + (↑(d + 1) : ℝ) * Q / N := by
          push_cast
          ring

/-! ### Step 1: moment expansion and independence -/

/-- The deterministic Lambert denominators are summable, uniformly before inserting the
Bernoulli selectors. -/
theorem summable_lambert_denom (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun p : Prime => (1 : ℝ) / ((b : ℝ) ^ p.val - 1)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hgeom : Summable (fun p : Prime => 2 * (1 / (b : ℝ)) ^ p.val) := by
    exact ((summable_geometric_of_lt_one (by positivity)
      (by simpa using one_div_lt_one_div_of_lt zero_lt_one hb1)).mul_left 2).comp_injective
        Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun p => by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (one_le_pow₀ hb1.le))) (fun p => ?_) hgeom
  have hp2 : 2 ≤ p.val := p.property.two_le
  have hpow : (2 : ℝ) ≤ (b : ℝ) ^ p.val := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ p.val := pow_le_pow_right₀ hb1.le (by omega)
  have hden : 0 < (b : ℝ) ^ p.val - 1 := by linarith
  have hbpowpos : (0 : ℝ) < (b : ℝ) ^ p.val := by positivity
  calc
    1 / ((b : ℝ) ^ p.val - 1) ≤ 2 / (b : ℝ) ^ p.val := by
      rw [div_le_div_iff₀ hden hbpowpos]
      nlinarith
    _ = 2 * (1 / (b : ℝ)) ^ p.val := by
      rw [div_pow]
      simp only [one_pow]
      ring

/-- The selected Lambert series is absolutely summable at every sample point. -/
theorem summable_randomLambert_terms (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} (X : Prime → Ω → Bool) (w : Ω) :
    Summable (fun p : Prime =>
      (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) := by
  apply (summable_lambert_denom b hb).of_norm_bounded
  intro p
  have hbR : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden : 0 < (b : ℝ) ^ p.val - 1 :=
    sub_pos.mpr (one_lt_pow₀ hbR p.property.pos.ne')
  split_ifs <;> simp only [norm_div, Real.norm_eq_abs, abs_one, abs_zero, zero_div]
  · rw [abs_of_pos hden]
  · exact div_nonneg (by norm_num) hden.le

/-- The random Lambert series is measurable when its Bernoulli coordinates are measurable. -/
theorem measurable_randomLambert (b : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (X : Prime → Ω → Bool) (hX : ∀ p, Measurable (X p)) :
    Measurable (randomLambert b X) := by
  unfold randomLambert
  exact Measurable.tsum fun p => by
    have hm : Measurable (fun w => if X p w then (1 : ℝ) else 0) :=
      (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX p)
    exact hm.div_const _

/-- The characteristic function of one Bernoulli coordinate. -/
theorem integral_ePh_bernoulli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (delta : Prime → ℝ)
    (X : Prime → Ω → Bool) (hX : BernoulliLaw μ delta X) (p : Prime) (θ : ℝ) :
    (∫ w, ePh (if X p w then θ else 0) ∂μ) =
      ((1 - delta p : ℝ) : ℂ) + (delta p : ℂ) * ePh θ := by
  let A : Set Ω := {w | X p w = true}
  have hA : MeasurableSet A := (hX.2.1 p) (measurableSet_singleton true)
  have hdelta0 : 0 ≤ delta p := (hX.1 p).1
  have hreal : μ.real A = delta p := by
    rw [measureReal_def, hX.2.2.2 p, ENNReal.toReal_ofReal hdelta0]
  have hfun : (fun w => ePh (if X p w then θ else 0)) =
      fun w => A.indicator (fun _ => ePh θ - 1) w + 1 := by
    funext w
    by_cases hw : X p w = true
    · simp [A, hw]
    · have hw' : X p w = false := Bool.eq_false_of_not_eq_true hw
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

/-- Independence factorizes the characteristic function of every finite prime truncation. -/
theorem integral_ePh_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (delta : Prime → ℝ) (X : Prime → Ω → Bool) (hX : BernoulliLaw μ delta X)
    (G : Finset Prime) (a : ℝ) :
    (∫ w, ePh (a * ∑ p ∈ G,
        (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) ∂μ) =
      ∏ p ∈ G, (((1 - delta p : ℝ) : ℂ) +
        (delta p : ℂ) * ePh (a / ((b : ℝ) ^ p.val - 1))) := by
  classical
  let Y : G → Ω → ℂ := fun p w =>
    ePh (if X p.1 w then a / ((b : ℝ) ^ p.1.val - 1) else 0)
  have hI : iIndepFun (fun p : G => X p.1) μ :=
    iIndepFun.precomp Subtype.val_injective hX.2.2.1
  have hprod := hI.integral_fun_prod_comp
    (fun p => (hX.2.1 p.1).aemeasurable)
    (fun p => (measurable_of_finite (f := fun z : Bool =>
      ePh (if z then a / ((b : ℝ) ^ p.1.val - 1) else 0))).aestronglyMeasurable)
  have hpoint (w : Ω) :
      ePh (a * ∑ p ∈ G,
          (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) =
        ∏ p : G, Y p w := by
    rw [Finset.mul_sum]
    rw [show (∑ p ∈ G, a * ((if X p w then (1 : ℝ) else 0) /
        ((b : ℝ) ^ p.val - 1))) =
        ∑ p : G, (if X p.1 w then a / ((b : ℝ) ^ p.1.val - 1) else 0) by
      calc
        _ = ∑ p : G, a * ((if X p.1 w then (1 : ℝ) else 0) /
            ((b : ℝ) ^ p.1.val - 1)) :=
          Finset.sum_subtype G (p := fun p : Prime => p ∈ G) (by simp) _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p hp
          split_ifs <;> ring]
    unfold ePh Y
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    rfl
  rw [show (∫ w, ePh (a * ∑ p ∈ G,
      (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) ∂μ) =
      ∫ w, ∏ p : G, Y p w ∂μ by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint]
  rw [hprod]
  calc
    (∏ p : G, ∫ w, Y p w ∂μ) =
        ∏ p ∈ G, ∫ w, ePh (if X p w then a / ((b : ℝ) ^ p.val - 1) else 0) ∂μ := by
      rw [Finset.prod_subtype G (p := fun p : Prime => p ∈ G) (by simp)]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact integral_ePh_bernoulli μ delta X hX p _

/-- Moduli of the finite characteristic factors are exactly `bernMod`. -/
theorem norm_integral_ePh_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ)
    (delta : Prime → ℝ) (X : Prime → Ω → Bool) (hX : BernoulliLaw μ delta X)
    (G : Finset Prime) (a : ℝ) :
    ‖∫ w, ePh (a * ∑ p ∈ G,
        (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) ∂μ‖ =
      ∏ p ∈ G, bernMod (delta p) (a / ((b : ℝ) ^ p.val - 1)) := by
  rw [integral_ePh_finset_sum μ b delta X hX G a, norm_prod]
  simp only [bernMod]

/-- The finite set of primes with value below `M`. -/
noncomputable def primesBelow (M : ℕ) : Finset Prime :=
  Finset.map ⟨fun p : {p // p ∈ (Finset.range M).filter Nat.Prime} =>
      (⟨p.1, (Finset.mem_filter.mp p.2).2⟩ : Prime), by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : Prime => z.val) h⟩ Finset.univ

@[simp] theorem mem_primesBelow {M : ℕ} {p : Prime} :
    p ∈ primesBelow M ↔ p.val < M := by
  classical
  simp only [primesBelow, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    have hv := congrArg (fun z : Prime => z.val) hq
    have hlt : q.val < M := Finset.mem_range.mp (Finset.mem_filter.mp q.2).1
    exact hv.symm ▸ hlt
  · intro hp
    let q : {p // p ∈ (Finset.range M).filter Nat.Prime} :=
      ⟨p.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, p.property⟩⟩
    refine ⟨q, ?_⟩
    exact Subtype.ext rfl

/-- Prime-value cutoffs converge to the full random Lambert series. -/
theorem tendsto_sum_primesBelow (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} (X : Prime → Ω → Bool) (w : Ω) :
    Tendsto (fun M => ∑ p ∈ primesBelow M,
      (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) atTop
      (𝓝 (randomLambert b X w)) := by
  have hs := (summable_randomLambert_terms b hb X w).hasSum
  have hcof : Tendsto primesBelow atTop (atTop : Filter (Finset Prime)) := by
    rw [tendsto_atTop_atTop]
    intro G
    refine ⟨(G.sup fun p => p.val) + 1, fun M hM => ?_⟩
    intro p hp
    rw [mem_primesBelow]
    have hle : p.val ≤ G.sup fun q => q.val := Finset.le_sup hp
    omega
  change Tendsto ((fun G : Finset Prime => ∑ p ∈ G,
    (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) ∘ primesBelow)
      atTop (𝓝 (∑' p : Prime,
        (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)))
  exact hs.comp hcof

theorem continuous_ePh : Continuous ePh := by
  unfold ePh
  fun_prop

theorem measurable_lambert_finset_sum (b : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (X : Prime → Ω → Bool) (hX : ∀ p, Measurable (X p)) (G : Finset Prime) :
    Measurable (fun w => ∑ p ∈ G,
      (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1)) := by
  apply Finset.measurable_sum
  intro p hp
  have hm : Measurable (fun w => if X p w then (1 : ℝ) else 0) :=
    (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX p)
  exact hm.div_const _

/-- The full infinite characteristic function is bounded by the product over any prescribed
finite collection of Bernoulli prime coordinates. -/
theorem norm_integral_ePh_randomLambert_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : Prime → ℝ) (X : Prime → Ω → Bool) (hX : BernoulliLaw μ delta X)
    (F : Finset Prime) (a : ℝ) :
    ‖∫ w, ePh (a * randomLambert b X w) ∂μ‖ ≤
      ∏ p ∈ F, bernMod (delta p) (a / ((b : ℝ) ^ p.val - 1)) := by
  let Z : ℕ → Ω → ℂ := fun M w => ePh (a * ∑ p ∈ primesBelow M,
    (if X p w then (1 : ℝ) else 0) / ((b : ℝ) ^ p.val - 1))
  have hZm : ∀ M, AEStronglyMeasurable (Z M) μ := by
    intro M
    exact (continuous_ePh.measurable.comp
      (measurable_const.mul (measurable_lambert_finset_sum b X hX.2.1 _))).aestronglyMeasurable
  have hbound : ∀ M, ∀ᵐ w ∂μ, ‖Z M w‖ ≤ (1 : ℝ) := by
    intro M
    exact Filter.Eventually.of_forall fun w => (norm_ePh _).le
  have hlim : ∀ᵐ w ∂μ, Tendsto (fun M => Z M w) atTop
      (𝓝 (ePh (a * randomLambert b X w))) := by
    apply Filter.Eventually.of_forall
    intro w
    exact continuous_ePh.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (tendsto_sum_primesBelow b hb X w))
  have hint := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    hZm (integrable_const 1) hbound hlim
  have hnorm : Tendsto (fun M => ‖∫ w, Z M w ∂μ‖) atTop
      (𝓝 ‖∫ w, ePh (a * randomLambert b X w) ∂μ‖) :=
    (continuous_norm.tendsto _).comp hint
  apply le_of_tendsto hnorm
  have hcof : ∀ᶠ M in atTop, F ⊆ primesBelow M := by
    filter_upwards [eventually_ge_atTop ((F.sup fun p => p.val) + 1)] with M hM
    intro p hp
    rw [mem_primesBelow]
    have hle : p.val ≤ F.sup fun q => q.val := Finset.le_sup hp
    omega
  filter_upwards [hcof] with M hFM
  rw [norm_integral_ePh_finset_sum μ b delta X hX (primesBelow M) a]
  apply Finset.prod_le_prod_of_subset_of_le_one hFM
  · intro p hp
    exact bernMod_nonneg _ _
  · intro p hp hpF
    exact bernMod_le_one (hX.1 p).1 (hX.1 p).2 _

theorem moment_le_tupleAvg (b : ℕ) (hb : 2 ≤ b) (h : ℤ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : Prime → ℝ) (X : Prime → Ω → Bool) (hX : BernoulliLaw μ delta X)
    (F : Finset Prime) (k N : ℕ) (hN : 1 ≤ N) (c : ℝ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (∫ w, ‖weylMean b h (c + (s : ℝ) * randomLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
      (∑ n : Fin (2 * k) → Fin N,
          ∏ p ∈ F, bernMod (delta p) (tuplePhase b h k p.val (fun i => (n i).val))) /
        (N : ℝ) ^ (2 * k) := by
  sorry

/-! ### The frozen target (verbatim) -/

/-- Average the entire Bernoulli characteristic modulus at each prime.
For a tuple of 2k uniform residues, its squared modulus has mean
1-2v_p(1-|f_p(h)|^(2k)).  Jensen, CRT, and the one-prime spectral gap
give the bound.  Constants depend on b,h, never k,F,N,delta or the translate.
Author's paper confidence 90%; not independently reviewed or Lean-proved. -/
@[blueprint (title := "Whole-factor high moments for random prime Lambert sums")]
theorem finiteCRT_moment_bound (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ P₀ : ℕ, ∃ γ : ℝ, 0 < γ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (delta : Prime → ℝ) (X : Prime → Ω → Bool), BernoulliLaw μ delta X →
      ∀ (F : Finset Prime), (∀ p ∈ F, P₀ < p.val) →
      ∀ (k N : ℕ), 1 ≤ k → 1 ≤ N → ∀ c : ℝ, ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (∫ w, ‖weylMean b h (c + (s : ℝ) * randomLambert b X w) N‖^(2*k) ∂μ) ≤
        Real.exp (-γ * ∑ p ∈ F, primeVariance delta p * min ((k : ℝ) / p.val) 1) +
        2 * (k : ℝ) * (∏ p ∈ F, (p.val : ℝ)) / N := by
  sorry

end NormalNumbers.RandomLambertMoment
