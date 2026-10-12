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

Status: IN PROGRESS.  The Bernoulli algebra, phase periodicity, positivity of `momentGamma`,
pairwise-coprime CRT factorization, prefix transfer, and exact residue moment are proved;
the spectral gap, local bound, moment expansion, and assembly declarations remain.
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
  sorry

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

theorem residueTuple_mean_le (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ < p → ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ r : Fin (2 * k) → Fin p, bernMod δ (tuplePhase b h k p (fun i => (r i).val))) /
          (p : ℝ) ^ (2 * k) ≤
        Real.exp (-(momentGamma b) * (δ * (1 - δ)) * min ((k : ℝ) / p) 1) := by
  sorry

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
