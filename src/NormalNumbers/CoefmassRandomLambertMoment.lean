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

Status: SKELETON.  Every analytic declaration is `sorry`.  The proof grind runs outside the
attended session.
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
  sorry

theorem bernMod_nonneg (δ θ : ℝ) : 0 ≤ bernMod δ θ := norm_nonneg _

theorem bernMod_le_one {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (θ : ℝ) : bernMod δ θ ≤ 1 := by
  sorry

/-! ### Step 2: periodicity in each residue -/

theorem bernMod_tuplePhase_mod (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (k p : ℕ) (hp : 1 ≤ p) (δ : ℝ)
    (n : Fin (2 * k) → ℕ) :
    bernMod δ (tuplePhase b h k p n) = bernMod δ (tuplePhase b h k p (fun i => n i % p)) := by
  sorry

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
  sorry

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
  sorry

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
