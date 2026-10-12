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

Status: IN PROGRESS.  The Bernoulli algebra, phase periodicity, positivity of `momentGamma`, and
the pairwise-coprime CRT factorization are proved; the prefix transfer, exact residue moment,
spectral-gap, local bound, moment-expansion, and assembly declarations remain.
-/

namespace NormalNumbers.RandomLambertMoment

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

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

/-! ### Step 7: the one-prime spectral gap -/

theorem localMean_normSq_le (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ < p → ‖localMean b h p‖ ^ 2 ≤ 1 - spectralConst b / p := by
  sorry

/-! ### Step 6: exact second moment over residues -/

theorem residueTuple_mean_sq (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (k p : ℕ) (hp : 0 < p) (δ : ℝ) :
    (∑ r : Fin (2 * k) → Fin p, bernMod δ (tuplePhase b h k p (fun i => (r i).val)) ^ 2) /
        (p : ℝ) ^ (2 * k) =
      1 - 2 * (δ * (1 - δ)) * (1 - ‖localMean b h p‖ ^ (2 * k)) := by
  sorry

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

theorem prefix_tuple_mean_le (Q d N : ℕ) (hQ : 0 < Q) (hN : 1 ≤ N) (G : (Fin d → ℕ) → ℝ)
    (h0 : ∀ n, 0 ≤ G n) (h1 : ∀ n, G n ≤ 1) (hper : ∀ n, G n = G (fun j => n j % Q)) :
    (∑ n : Fin d → Fin N, G (fun j => (n j).val)) / (N : ℝ) ^ d ≤
      (∑ r : Fin d → Fin Q, G (fun j => (r j).val)) / (Q : ℝ) ^ d + d * Q / N := by
  sorry

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
