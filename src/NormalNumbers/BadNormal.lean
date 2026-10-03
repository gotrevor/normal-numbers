/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormalB
import NormalNumbers.CFCylinder
import NormalNumbers.ExplicitOmegaK

/-!
# A computable absolutely normal number with partial quotients in `{1, 2}`

Audit: `docs/BAD-NORMAL-AUDIT-2026-10-03.md` (sweep `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` §1).

**Target.**  Montgomery, *Ten Lectures on the Interface between Analytic Number Theory and
Harmonic Analysis* (1994), p. 203, asks for "a normal number whose continued fraction coefficients
are bounded".  Bugeaud, *Distribution modulo one and Diophantine approximation* (2012), §7.7:
"No explicit example of such a number has been exhibited yet."  Queffélec, *Old and new results on
normality* (IMS LN 48, 2006; arXiv math/0608249) §4: "no explicit normal numbers in BAD have been
constructed yet."  Existence is Kaufman 1980 (`N ≥ 3`) + R. C. Baker's remark, Queffélec–Ramaré
2003 (`N = 2`), Jordan–Sahlsten 2016, Hochman–Shmerkin 2015.

**Mechanism.**  Fair coins `ω ↦ cfCoin ω = [0; 1+ω₀, 1+ω₁, …]`; the law is the Bernoulli(1/2)
measure on `E_{1,2}`.  Its polynomial Fourier decay is cited (`Literature.SahlstenStevensBernoulli12`);
the CF cylinder endpoints `cfVal w`, `cfVal (bumpLast w)` give exact rational lower approximations
within `1/(q_D(q_D+q_{D-1})) ≤ 2^{-D}` (`Abad_bounds`); then the proved all-bases derandomizer
`ComputableNormalB.exists_computable_absNormal` gives a computable coin sequence.

**Known-false siblings** (the mechanism must refuse them, and does):
* an atom (a single CF, e.g. the periodic `[0; 1, 1, …] = 1/φ`, or any quadratic irrational):
  the decay hypothesis fails for every Dirac measure (`not_decay_const`, proved), so the engine
  cannot be fed one (`not_decay_cfCoin_fixed`, proved);
* CF-normality of `cfCoin e`: false (all digits `≤ 2`); nothing here claims it.

⚠️ "Computable", not "explicit" in Queffélec's sense: the derandomizer is primitive recursive and
astronomically slow.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.BadNormal

open Derandomize DecayAeNormal ExplicitOmegaK

/-! ## The coin-to-CF map -/

/-- Coin `false ↦` partial quotient `1`, `true ↦ 2`. -/
def dig (b : Bool) : ℕ := if b then 2 else 1

/-- The CF word of a coin prefix. -/
def bWord (p : List Bool) : List ℕ := p.map dig

/-- **`[0; 1+ω₀, 1+ω₁, …]`**: the limit of the convergents `cfVal (bWord (pre ω n))`. -/
noncomputable def cfCoin (ω : ℕ → Bool) : ℝ :=
  limUnder atTop fun n : ℕ => ((cfVal (bWord (pre ω n)) : ℚ) : ℝ)

theorem dig_pos (b : Bool) : 1 ≤ dig b := by cases b <;> simp [dig]

theorem bWord_pos (p : List Bool) : ∀ a ∈ bWord p, 1 ≤ a := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact dig_pos b

theorem cfVal_nonneg : ∀ l : List ℕ, 0 ≤ cfVal l
  | [] => by simp [cfVal]
  | a :: l => by
      have := cfVal_nonneg l
      simp only [cfVal]
      positivity

/-! ## Exact lower approximations for the engine -/

/-- Lower endpoint of the CF cylinder of the prefix `p`: the smaller of `[0; w]` and
`[0; w₁, …, w_D + 1]` (`w = bWord p`).  For `p = []` this is `min 0 1 = 0`. -/
noncomputable def Abad (p : List Bool) : ℝ :=
  min ((cfVal (bWord p) : ℚ) : ℝ) ((cfVal (bumpLast (bWord p)) : ℚ) : ℝ)

/-- Its base-`b` floors, read from the continuants (`cfVal w = cfP w / cfK w` for `w ≠ []`). -/
def PsiBad (b m : ℕ) (p : List Bool) : ℕ :=
  if p = [] then 0 else
    min (cfP (bWord p) * b ^ m / cfK (bWord p))
      (cfP (bumpLast (bWord p)) * b ^ m / cfK (bumpLast (bWord p)))

theorem Abad_nonneg (p : List Bool) : 0 ≤ Abad p := by
  unfold Abad
  exact le_min (by exact_mod_cast cfVal_nonneg _) (by exact_mod_cast cfVal_nonneg _)

/-- **Leaf: the floors are exact.**

Confidence 90%.  Proof: for `p = []`, `Abad [] = min 0 1 = 0`.  Otherwise `w = bWord p ≠ []` and
`bumpLast w ≠ []` have positive digits, so `cfVal_eq_div` writes both endpoints as `P/K` with
`K = cfK ≥ 1` (`fib_le_cfK`); `⌊(P/K)·bᵐ⌋₊ = P·bᵐ / K` (`Nat.floor_div_eq_div`), and the floor of a
minimum is the minimum of the floors (monotone). -/
theorem PsiBad_eq (b m : ℕ) (p : List Bool) : PsiBad b m p = ⌊Abad p * (b : ℝ) ^ m⌋₊ := by
  sorry

/-- **Leaf: the floors are primitive recursive.**

Confidence 85%.  Proof: `bWord` is a `List.map`; `bumpLast` is `dropLast ++ [getLastD + 1]`; `cfK`
is a two-step list recursion, primitive recursive via the pair `(cfK l, cfK (l.drop 1))` computed by
`List.foldr` (`cfK (a :: l) = a·cfK l + cfK (l.drop 1)`); then `nat_mul`, `primrec_pow`, `nat_div`,
`min`, and the `p = []` test. -/
theorem primrec_PsiBad : Primrec fun x : ℕ × ℕ × List Bool => PsiBad x.1 x.2.1 x.2.2 := by
  sorry

/-- **Leaf: the coin map is measurable.**

Confidence 92%.  Proof: each convergent `ω ↦ cfVal (bWord (pre ω n))` depends on finitely many
coordinates, hence is measurable (`measurable_of_countable` on the finite prefix).  The limit exists
at every `ω` (the convergents are Cauchy: consecutive ones differ by `1/(q_n q_{n+1})`, and
`q_n ≥ F_{n+1}` by `fib_le_cfK`), so `cfCoin` is the pointwise limit and
`measurable_of_tendsto_metrizable` applies. -/
theorem measurable_cfCoin : Measurable cfCoin := by
  sorry

/-- **Leaf: the approximation sandwich `A(pre ω D) ≤ cfCoin ω ≤ A(pre ω D) + 2^{-D}`.**

Confidence 85%.  Proof: `w = bWord (pre ω D)`.  Every later convergent `[0; w, u]` (`u` a word of
`1`s and `2`s) lies in the closed interval between `cfVal w` and `cfVal (bumpLast w)` (the CF
cylinder of `w` is contained in it, `cfCylinder_endpoints`; for `D = 0` the interval is `[0,1]`), so
the limit `cfCoin ω` does too.  The interval has length `1/(K(K+K'))` with `K = cfK w`,
`K' = cfK w.dropLast` (`abs_cfVal_sub_bumpLast`), and `K(K+K') ≥ F_{D+1}F_{D+2} ≥ 2^D`
(`fib_le_cfK`; `F_{D+1}F_{D+2}` is `1, 2, 6, 15, 40, …`, and the ratio exceeds `2` from `D = 1`). -/
theorem Abad_bounds (ω : ℕ → Bool) (D : ℕ) :
    Abad (pre ω D) ≤ cfCoin ω ∧ cfCoin ω ≤ Abad (pre ω D) + (1 / 2 : ℝ) ^ D := by
  sorry

/-- **Leaf (content locator): the partial quotients of `cfCoin ω` are exactly `dig (ω n)`.**

Confidence 85%.  Proof: `cfCoin ω` lies in the open interior of the CF cylinder of
`bWord (pre ω D)` for every `D` (it lies in the closed one by `Abad_bounds`; an endpoint is
rational, while `cfCoin ω` is irrational because it lies in nested cylinders whose lengths
`→ 0` and whose rational points are eventually excluded, as in `exists_irrational_mem_iInter_cfCylinder`).
Interior points of `cfCylinder w` have first `|w|` digits `w` (`cfCylinder_endpoints`, third
clause); take `D = n + 1`. -/
theorem cfDigit_cfCoin (ω : ℕ → Bool) (n : ℕ) : cfDigit (cfCoin ω) n = dig (ω n) := by
  sorry

/-! ## The cited decay input -/

namespace Literature

/-- **Cited input: polynomial Fourier decay of the Bernoulli(1/2) measure on `E_{1,2}`.**

**Primary source.**  T. Sahlsten, C. Stevens, *Fourier transform and expanding maps on Cantor
sets*, Amer. J. Math. **146** (2024), no. 4, 945–982 (arXiv 2009.01703), **Theorem 1.1(2)**
(`thm:nonlinear`): if `T : ⋃ I_a → [0,1]` is a totally non-linear uniformly expanding Markov map of
bounded distortions, conjugate to the full shift, with the `I_a` **disjoint** and the inverse
branches `f_a` **analytic**, and `μ` is a non-atomic equilibrium state of a potential with
exponentially vanishing variations, then `|μ̂(ξ)| = O(|ξ|^{-α})` for some `α > 0`
(their `μ̂(ξ) = ∫ e^{-2πiξx} dμ`, `ξ ∈ ℝ`, same modulus as `ee`).

**Hypothesis check** (instance: `f₁ t = 1/(1+t)`, `f₂ t = 1/(2+t)` on `J = [1/3, 3/4]`, conjugated
to `[0,1]` by the affine `J → [0,1]`, which changes `μ̂` by a phase and a rescaling of `ξ`):
* `f₁ J = [4/7, 3/4]`, `f₂ J = [4/11, 3/7]`: both inside `J` and disjoint (`3/7 < 4/7`);
  `T` maps each onto `J` (Markov, full shift); `E_{1,2} ⊂ [0.366, 0.733] ⊂ J`.
* Uniform expansion: `|f_a'| = (a+t)^{-2} ≤ 9/16` on `J`.  Distortion `T''/T' = -2/t`, bounded on `J`.
  Analytic: Möbius maps.
* Total non-linearity: a `C¹` coboundary relation `τ = ψ₀ + g∘T − g` makes periodic-orbit sums of
  `τ = log|T'|` additive in the letters.  The fixed points give `τ = 2 log φ` (word `1`) and
  `2 log(1+√2)` (word `2`); the period-2 orbit of `12` gives `S₂τ = 2 log(2+√3)`, the spectral
  radius of `[[0,1],[1,1]]·[[0,1],[1,2]] = [[1,2],[1,3]]` (trace 4).  `φ(1+√2) ≈ 3.906 ≠ 3.732 ≈ 2+√3`.
* `μ` = law of `cfCoin` = the uniform Bernoulli measure on the full shift `{1,2}^ℕ`: the
  equilibrium state of the constant potential `−log 2` (variations `0`), i.e. the measure of maximal
  entropy; non-atomic.
* `O(|ξ|^{-α})` as `|ξ| → ∞` plus `|μ̂| ≤ 1` gives the all-`ξ ≠ 0` form below (enlarge `C`).

**Independent cross-check.**  T. Jordan, T. Sahlsten, *Fourier transforms of Gibbs measures for the
Gauss map*, Math. Ann. **364** (2016), 983–1023 (arXiv 1312.3619), **Theorem 1.3(2)** in arXiv
numbering (`thm:main`): any Gibbs measure for the Gauss map restricted to `B(𝒜)`, `𝒜` finite, with
`dim μ > 1/2`, has polynomial decay; Bernoulli measures are Gibbs (their Remark `rmk:examples`(1)).
Here `dim μ = log 2 / λ`, `λ = 2·𝔼 log(a + x) ≈ 1.34602` (depth-20 exact cylinder average,
`probes/bad_bernoulli12_dimension.py`), so `dim μ ≈ 0.51496 > 1/2`: covered, with little margin.

**Faithful-or-weaker:** the statement below is the specialisation to `μ` = law of `cfCoin` under
`coins`.  Referee pass pending. -/
def SahlstenStevensBernoulli12 : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * cfCoin ω) ∂coins‖ ≤ C * |ξ| ^ (-δ)

end Literature

/-! ## Headline -/

/-- **A computable absolutely normal number all of whose partial quotients lie in `{1, 2}`**:
a computable answer to Montgomery's question (Bugeaud 2012 §7.7, Queffélec 2006 §4: none
exhibited).  Since `cfDigit` returns the junk value `0` on rationals, "every digit is `1` or `2`"
also certifies that `cfCoin e` is irrational and badly approximable.

Wired from the cited decay, the proved engine, and the leaves above. -/
theorem exists_computable_absNormal_bad (h : Literature.SahlstenStevensBernoulli12) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (cfCoin e) ∧
      ∀ n, cfDigit (cfCoin e) n ∈ ({1, 2} : Finset ℕ) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := h
  obtain ⟨e, hce, hn⟩ := ComputableNormalB.exists_computable_absNormal PsiBad primrec_PsiBad Abad
    PsiBad_eq Abad_nonneg cfCoin measurable_cfCoin Abad_bounds hC hδ hdec
  refine ⟨e, hce, hn, fun n => ?_⟩
  rw [cfDigit_cfCoin]
  cases e n <;> simp [dig]

/-! ## Known-false siblings -/

/-- **Guard: no Dirac measure has polynomial Fourier decay.**  So the engine's decay hypothesis
can never be met by an atom (a single CF, e.g. a periodic one), and the derandomizer cannot
"certify" normality of a fixed quadratic irrational. -/
theorem not_decay_const (c : ℝ) :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ _ω, ee (ξ * c) ∂coins‖ ≤ C * |ξ| ^ (-δ) := by
  rintro ⟨C, δ, hC, hδ, h⟩
  have : IsProbabilityMeasure coins := by unfold coins; infer_instance
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  set ξ : ℝ := (C + 1) ^ (1 / δ) with hξdef
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hC1 _
  have h1 := h ξ hξ.ne'
  rw [integral_const, probReal_univ, one_smul, norm_ee, abs_of_pos hξ, hξdef,
    ← Real.rpow_mul hC1.le, show 1 / δ * -δ = (-1 : ℝ) by field_simp, Real.rpow_neg_one] at h1
  have h2 : C * (C + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hC1]; linarith
  linarith

/-- **Guard, the one-letter and periodic siblings**: for any fixed coin sequence `ω₀` (constant,
periodic, …), the law of the constant map `ω ↦ cfCoin ω₀` is a Dirac and fails the decay
hypothesis.  The content of `Literature.SahlstenStevensBernoulli12` is the spread of `ω`. -/
theorem not_decay_cfCoin_fixed (ω₀ : ℕ → Bool) :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ _ω, ee (ξ * cfCoin ω₀) ∂coins‖ ≤ C * |ξ| ^ (-δ) :=
  not_decay_const _

/-- **Non-vacuity anchor for `cfCoin`**: the all-`false` sequence is `[0; 1, 1, …] = (√5 − 1)/2`,
the golden-ratio conjugate (a quadratic irrational, where `not_decay_cfCoin_fixed` bites).

Confidence 85%.  Proof: `cfVal` of `n` ones is `F_n/F_{n+1}` (`cfVal_eq_div`, continuants of ones
are Fibonacci), which tends to `1/φ = (√5 − 1)/2`; `limUnder` of a convergent sequence is its
limit (`Tendsto.limUnder_eq`). -/
theorem cfCoin_const_false : cfCoin (fun _ => false) = (Real.sqrt 5 - 1) / 2 := by
  sorry

end NormalNumbers.BadNormal
