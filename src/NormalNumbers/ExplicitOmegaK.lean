/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.OmegaKCalculus
import NormalNumbers.SqrtCantorAbs
import NormalNumbers.DigitCantor

/-!
# Manai's algebraic normality degree: explicit points of `Ω_k`

Audit verdict: `docs/EXPLICIT-OMEGA-K-AUDIT-2026-10-02.md`.

**Target.**  Manai, *Transcendence Meets Normality* (arXiv 2508.09319v4, 2026-09-22),
Definition `def:deg` and the Problem after it:

> `deg_an(x) := inf {k ∈ ℕ | ∃ p ∈ ℤ[X] with deg p = k s.t. p(x) is not normal}`, `= ∞` if
> the set is empty; `Ω_k := {x : deg_an(x) = k}`.  "Show that the sets `Ω_k` are of Hausdorff
> dimension 1 (or at least of positive Hausdorff dimension).  Construct an explicit number
> `x ∈ Ω_k` for all (some) `k ∈ ℕ`."  Manai adds: "It is not even known whether `Ω_k ≠ ∅` for
> `2 ≤ k ∈ ℕ`."

**Transcription choices** (all forced by the paper):
* "normal" is **absolutely normal** (§2: "`x` is an (absolutely) normal number if `x` is
  `b`-normal with respect to every integer base `b ≥ 2`"; abstract: "(absolutely) normal").
  So base-2 normality (the ExplicitSquare theorem) does **not** suffice for `Ω₂`.
* `ℕ = {1, 2, …}`: with `0 ∈ ℕ` every `x` would have `deg_an x = 0` (the constant polynomial `0`
  is not normal), contradicting "t-normal iff `deg_an = ∞`".  For `k ≥ 1`, `deg p = k` is
  `natDegree p = k`.
* `p(x)` normal for **every** `p` with `1 ≤ deg p < k` is what `deg_an x = k` requires
  (`mem_Omega_coe_iff`).

## Route

`x_k := y^{1/k}`, `y = cantorReal e` on the quarter-Cantor set of `ExplicitSquareNonNormal`.
`x_k^k = y` misses the block `11`, so it is not normal (free).  For `1 ≤ deg p < k`,
`p(x_k) = G_p(y)` with `G_p(t) = p(t^{1/k}) = Σ_j a_j t^{j/k}`, which is analytic on `t > 0`
and **never affine**: `t² G_p''(t) = Σ_{1 ≤ j ≤ deg p} (j/k)(j/k − 1) a_j s^j`, `s = t^{1/k}`,
a nonzero polynomial in `s` because `(j/k)(j/k−1) ≠ 0` for `1 ≤ j < k`.
* **`k = 2`**: `G_p = a√t + b`, `G_p'' ≠ 0` everywhere, so today's single-map Fourier decay is
  all that is needed, plus an all-bases derandomization.
* **`k ≥ 3`**: the inflection points of the `G_p` are dense in `[1/2, 1]` (`k = 3`:
  `s = −c₁a₁/(c₂a₂)` ranges over a dense set), so no cylinder avoids all of them.  Two fixes,
  both from Baker–Banaji (arXiv 2401.01241v2 = Math. Ann. 392 (2025)):
  - **a.e. (non-explicit)**: BB Corollary `c:analyticnormal` gives `μ`-a.e. absolute normality of
    `F(y)` for **analytic non-affine** `F` directly (their proof localises to cylinders where
    `F'' ≠ 0`).  Countably many `p` then intersect for free: `ae_mem_Omega`, so `Ω_k ≠ ∅`.
  - **explicit**: BB Cor 1.5 (`t:self-similar`) main clause has **explicit** dependence of the
    constant on `max|F'|, max|F''|, min|F''|`; cutting `μ` at depth `m` and discarding the
    cylinders within `r` of an inflection point gives global polynomial decay of `(G_p)_*μ`
    with constants computable from `p` (`polyDecay_Gk`), which the derandomization needs
    uniformly in `p` (`exists_computable_isAbsNormal_Gk`).
* **Hausdorff dimension 1** (`dimH_Omega_eq_one`): run the a.e. argument on self-similar
  measures `ν_L` (base-`2^L` digits avoiding the top digit, `dim → 1`) and use the mass
  distribution principle.

Cited inputs are faithful-or-weaker transcriptions (each docstring says why):
`BakerBanajiAnalyticQuarterCantor`, `BakerBanajiUniformQuarterCantor`, `BakerBanajiAnalytic`;
today's `ExplicitSquare.BakerBanajiQuarterCantor` is reused for `k = 2`.
-/

open MeasureTheory Filter Topology Polynomial

namespace NormalNumbers.ExplicitOmegaK

open ExplicitSquare

/-! ## Manai's definitions -/

/-- Absolutely normal: normal in every integer base `b ≥ 2` (Manai 2508.09319 §2).  Same
statement as `NormalNumbers.IsAbsolutelyNormal` (`Headline.lean`), restated to avoid importing
the continued-fraction stack. -/
def IsAbsNormal (x : ℝ) : Prop := ∀ b : ℕ, 2 ≤ b → IsNormal b x

/-- The right-hand side of Manai's Definition `def:deg`, with `ℕ = {1, 2, …}`. -/
def degAnSet (x : ℝ) : Set ℕ :=
  {k | 1 ≤ k ∧ ∃ p : ℤ[X], p.natDegree = k ∧ ¬ IsAbsNormal (aeval x p)}

/-- **Algebraic normality degree** `deg_an x` (Manai 2508.09319v4, Def. `def:deg`): the least
`k ≥ 1` such that some integer polynomial of degree `k` sends `x` to a non-normal number, and
`∞` if there is none. -/
noncomputable def degAn (x : ℝ) : ℕ∞ := by
  classical
  exact if (degAnSet x).Nonempty then ((sInf (degAnSet x) : ℕ) : ℕ∞) else ⊤

/-- `Ω_k := {x : deg_an x = k}`, `k ∈ ℕ ∪ {∞}`. -/
def Omega (k : ℕ∞) : Set ℝ := {x | degAn x = k}

theorem mem_Omega_coe_iff {x : ℝ} {k : ℕ} :
    x ∈ Omega k ↔ k ∈ degAnSet x ∧ ∀ j ∈ degAnSet x, k ≤ j := by
  classical
  unfold Omega degAn
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hne : (degAnSet x).Nonempty
    · rw [if_pos hne] at h
      have hk : sInf (degAnSet x) = k := by exact_mod_cast h
      exact ⟨hk ▸ Nat.sInf_mem hne, fun j hj => hk ▸ Nat.sInf_le hj⟩
    · rw [if_neg hne] at h
      exact absurd h (ENat.top_ne_natCast k)
  · rintro ⟨hk, hmin⟩
    have hne : (degAnSet x).Nonempty := ⟨k, hk⟩
    rw [if_pos hne]
    exact_mod_cast le_antisymm (Nat.sInf_le hk) (le_csInf hne hmin)

/-- The working criterion for `x ∈ Ω_k`: every `p` with `1 ≤ deg p < k` gives a normal `p(x)`,
and some `p` of degree `k` gives a non-normal one. -/
theorem mem_Omega_of {x : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hlow : ∀ p : ℤ[X], 1 ≤ p.natDegree → p.natDegree < k → IsAbsNormal (aeval x p))
    (htop : ∃ p : ℤ[X], p.natDegree = k ∧ ¬ IsAbsNormal (aeval x p)) : x ∈ Omega k := by
  refine mem_Omega_coe_iff.2 ⟨⟨hk, htop⟩, ?_⟩
  rintro j ⟨hj1, p, hpd, hpn⟩
  by_contra hjk
  exact hpn (hlow p (hpd ▸ hj1) (hpd ▸ (not_le.1 hjk)))

/-- Failure in base `2` is failure of absolute normality. -/
theorem not_isAbsNormal_of_not_isNormal_two {x : ℝ} (hx : ¬ IsNormal 2 x) : ¬ IsAbsNormal x :=
  fun h => hx (h 2 le_rfl)

/-! ## Degree one: Wall in every base -/

/-- A degree-1 integer polynomial sends an absolutely normal number to an absolutely normal
number (Wall's rational affine invariance, `isNormal_rat_mul_add`, in each base). -/
theorem isAbsNormal_aeval_of_natDegree_eq_one {x : ℝ} (hx : IsAbsNormal x) (p : ℤ[X])
    (hp : p.natDegree = 1) : IsAbsNormal (aeval x p) := by
  intro b hb
  have hpe := eq_X_add_C_of_natDegree_le_one hp.le
  have hc : p.coeff 1 ≠ 0 := by
    have hp0 : p ≠ 0 := by rintro rfl; simp at hp
    have := leadingCoeff_ne_zero.2 hp0
    rwa [leadingCoeff, hp] at this
  have hq : ((p.coeff 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc
  have := isNormal_rat_mul_add b hb x (p.coeff 1) (p.coeff 0) hq (hx b hb)
  rw [hpe]
  simpa using this

/-! ## `Ω₂`: the cheap corollary of the ExplicitSquare theorem -/

theorem not_isAbsNormal_cantorReal (e : ℕ → Bool) : ¬ IsAbsNormal (cantorReal e) :=
  not_isAbsNormal_of_not_isNormal_two (not_isNormal_cantorReal e)

/-- **`√y ∈ Ω₂`** as soon as `√y` is absolutely normal and `y ≥ 0` is not. -/
theorem sqrt_mem_Omega_two {y : ℝ} (hy0 : 0 ≤ y) (hx : IsAbsNormal (Real.sqrt y))
    (hy : ¬ IsAbsNormal y) : Real.sqrt y ∈ Omega 2 := by
  have h := mem_Omega_of (x := Real.sqrt y) (k := 2) (by norm_num)
    (fun p h1 h2 => isAbsNormal_aeval_of_natDegree_eq_one hx p (by omega))
    ⟨X ^ 2, by simp, by simpa [Real.sq_sqrt hy0] using hy⟩
  simpa using h

/-- **All-bases derandomization of the `√` map** (the base-2 case is the proved
`ExplicitSquare.exists_computable_isNormal_sqrt_of_polyDecay`).

Confidence 80%.  English proof: Manai 2609.24665 `lem:decaynormal` is base-free: for base `b`,
`∫|A_N(h)|² ≤ 1/N + 2C|h|^{-δ}N⁻²Σ_{m<n}(bⁿ − bᵐ)^{-δ} ≤ C_b/N`, so `ComputableNormal.level_bound`'s
proof gives level-`n` mass `≤ 2c_b/n²` with `c_b` explicit in `C, δ, b`.  Interleave bases
`2 ≤ b ≤ ⌊log₂ n⌋` at level `n` (mass `≤ 2c n^{-2} log n`, summable with a computable tail).
New engineering only: for `b` not a power of `2`, `⌊√y·bᵐ⌋` is not a function of a finite coin
prefix, so the exact test `fails` becomes a sandwich test (count visits of the computable
`2^{-K}`-approximation to blocks shrunk/enlarged by `2^{-K+1}`, `Sandwich.lean`), which only
changes the constants.  Then `Derandomize.exists_primrec_avoid` as in
`ComputableNormal.exists_computable_normal_of_digits`, and `normal_of_good` in each base. -/
theorem exists_computable_isAbsNormal_sqrt_of_polyDecay (hd : PolyDecay Real.sqrt) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (Real.sqrt (cantorReal e)) :=
  SqrtCantorAbs.exists_computable_absNormal_sqrt hd

/-- **Manai's problem for `k = 2`: an explicit point of `Ω₂`.**  `x = √y`, `y = cantorReal e`,
`e` computable; conditional on the cited, refereed `BakerBanajiQuarterCantor`.  Wiring proved
from `exists_computable_isAbsNormal_sqrt_of_polyDecay` and `sqrt_mem_Omega_two`. -/
theorem exists_computable_mem_Omega_two (hBB : BakerBanajiQuarterCantor) :
    ∃ e : ℕ → Bool, Computable e ∧ Real.sqrt (cantorReal e) ∈ Omega 2 := by
  obtain ⟨U, hU, hsub, hC2, hF''⟩ := sqrt_bakerBanaji_hyp
  obtain ⟨e, hc, hn⟩ :=
    exists_computable_isAbsNormal_sqrt_of_polyDecay (hBB _ U hU hsub hC2 hF'')
  exact ⟨e, hc, sqrt_mem_Omega_two (cantorReal_mem_Ico e).1 hn (not_isAbsNormal_cantorReal e)⟩

/-! ## General `k`: `x_k = y^{1/k}` -/

/-- The candidate point of `Ω_k`: `x_k(e) = (cantorReal e)^{1/k}`. -/
noncomputable def rootK (k : ℕ) (e : ℕ → Bool) : ℝ := cantorReal e ^ ((k : ℝ)⁻¹)

/-- `G_p(t) = p(t^{1/k})`, so `p(x_k(e)) = G_p(cantorReal e)` by definition. -/
noncomputable def Gk (k : ℕ) (p : ℤ[X]) (t : ℝ) : ℝ := aeval (t ^ ((k : ℝ)⁻¹)) p

theorem aeval_rootK (k : ℕ) (p : ℤ[X]) (e : ℕ → Bool) :
    aeval (rootK k e) p = Gk k p (cantorReal e) := rfl

theorem rootK_pow (k : ℕ) (hk : k ≠ 0) (e : ℕ → Bool) : rootK k e ^ k = cantorReal e :=
  Real.rpow_inv_natCast_pow (cantorReal_mem_Ico e).1 hk

/-- `X^k` sends `x_k` to the non-normal `y`: the degree-`k` witness. -/
theorem top_witness (k : ℕ) (hk : k ≠ 0) (e : ℕ → Bool) :
    ∃ p : ℤ[X], p.natDegree = k ∧ ¬ IsAbsNormal (aeval (rootK k e) p) :=
  ⟨X ^ k, by simp, by simpa [rootK_pow k hk e] using not_isAbsNormal_cantorReal e⟩

/-- `G_p` is real-analytic on `t > 0`.

Confidence 98%.  Proof: `t ↦ t^{1/k}` is analytic on `(0, ∞)` (`exp (log t / k)`), and `aeval`
of a polynomial is a finite sum of products. -/
theorem analyticOnNhd_Gk (k : ℕ) (p : ℤ[X]) : AnalyticOnNhd ℝ (Gk k p) (Set.Ioi 0) :=
  OmegaKCalculus.analyticOnNhd_gk k p

/-- **`G_p` is never affine on `[1/2, 1]` when `1 ≤ deg p < k`** (the difficulty-check lemma).

Confidence 96%.  Proof: with `s = t^{1/k}` and `p = Σ_{j ≤ d} a_j X^j`,
`t² G_p''(t) = Σ_{1 ≤ j ≤ d} (j/k)(j/k − 1) a_j s^j`.  For `1 ≤ j < k` the factor
`(j/k)(j/k − 1)` is nonzero, and `a_d ≠ 0`, so the right side is a nonzero polynomial in `s` of
degree `d`, with at most `d` roots; `s` ranges over the infinite interval `[2^{-1/k}, 1]`.
Fails exactly when `d = k` and `p = a X^k + b` (`G_p` affine): the affine sibling. -/
theorem exists_deriv2_Gk_ne_zero (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree)
    (hk : p.natDegree < k) : ∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv (Gk k p)) t ≠ 0 :=
  OmegaKCalculus.exists_deriv2_gk_ne_zero k p h1 hk

/-- **Sibling control**: for `p = X^k`, `G_p` is the identity, and no point of the
quarter-Cantor set is normal.  So any mechanism proving `p(x_k)` normal must use `deg p < k`
(through `exists_deriv2_Gk_ne_zero`), and the identity map is where it must fail. -/
theorem Gk_X_pow (k : ℕ) (hk : k ≠ 0) {t : ℝ} (ht : 0 ≤ t) : Gk k (X ^ k) t = t := by
  simp [Gk, Real.rpow_inv_natCast_pow ht hk]

/-- **Closed route: no single cylinder works for `k ≥ 3`.**  For `p = nX² − mX` (`1 ≤ deg p < 3`),
`G_p(t) = n t^{2/3} − m t^{1/3}` has an inflection point at `t = (m/n)³`, and these are dense in
`[1/2, 1]`.  So a Baker–Banaji application with `F'' ≠ 0` on one fixed cylinder (the `k = 2`
mechanism of `ExplicitSquare`) cannot handle all `p` at once; the a.e. route localises per `p`
(`ae_mem_Omega`) and the explicit route needs decay across the inflection points
(`polyDecay_Gk`).

Confidence 97%.  Proof: `t² G_p''(t) = (2/3)(−1/3) n s² − (1/3)(−2/3) m s = (2/9) s (m − n s)`,
`s = t^{1/3}`, which vanishes at `s = m/n`. -/
theorem deriv2_Gk_three_eq_zero (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    deriv (deriv (Gk 3 (C (n : ℤ) * X ^ 2 - C (m : ℤ) * X))) (((m : ℝ) / n) ^ 3) = 0 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (0 : ℝ) < ((m : ℝ) / n) ^ 3 := by positivity
  have hdeg : (C (n : ℤ) * X ^ 2 - C (m : ℤ) * X).natDegree = 2 := by
    compute_degree!
    exact_mod_cast hn.ne'
  show deriv (deriv (OmegaKCalculus.gk 3 _)) _ = 0
  rw [OmegaKCalculus.deriv2_gk_eq_qPoly 3 (by norm_num) _ ht, OmegaKCalculus.qPoly, hdeg,
    show ((((m : ℝ) / n) ^ 3) ^ (((3 : ℕ) : ℝ)⁻¹)) = (m : ℝ) / n from
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  simp [Finset.sum_range_succ, coeff_X]
  left
  field_simp
  ring

/-! ### Non-explicit: `Ω_k ≠ ∅` from Baker–Banaji's analytic corollary -/

/-- **Cited input: Baker–Banaji, arXiv 2401.01241v2 (Math. Ann. 392 (2025)), Corollary
`c:analyticnormal`**, specialised to the law of `cantorReal`: for an analytic non-affine `F`,
`F_*μ` has Property (A), i.e. `(q_n F(y))` is equidistributed mod 1 for `μ`-a.e. `y` whenever
`inf (q_{n+1} − q_n) > 0`.

**Faithful-or-weaker.**  `q_n = bⁿ` gives base-`b` normality a.e. (`isNormal_iff_equidistributed_orbit`),
and a countable intersection over `b` gives absolute normality.  The law of `cantorReal` is the
stationary measure of the non-trivial IFS `ψ_b(s) = s/4 + b/4` on `[0,1]` after `s = 2t − 1`
(`docs/BAKER-BANAJI-REFEREE-2026-10-02.md`); `F ∘ (s ↦ 1/2 + s/2)` is analytic on a
neighbourhood of `[0,1]`, and it is non-affine there because `F'' ≠ 0` at some point of `[1/2,1]`.
BB's proof is itself a localisation: it decomposes `μ` into cylinders on which `F'' ≠ 0` and
applies Thm 1.4 to each, which is exactly the mechanism the inflection points of `G_p` require. -/
def BakerBanajiAnalyticQuarterCantor : Prop :=
  ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → AnalyticOnNhd ℝ F U →
    (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t ≠ 0) →
    ∀ᵐ ω ∂coinMeasure, IsAbsNormal (F (cantorReal ω))

/-- `ℤ[X]` is countable (it embeds in `ℕ →₀ ℤ`). -/
instance : Countable ℤ[X] :=
  Function.Injective.countable (β := ℕ →₀ ℤ) (f := fun p => p.toFinsupp.coeff)
    fun p q h => Polynomial.toFinsupp_injective (by
      rw [← AddMonoidAlgebra.ofCoeff_coeff p.toFinsupp, ← AddMonoidAlgebra.ofCoeff_coeff q.toFinsupp]
      exact congrArg _ h)

/-- `Ioi 0` is an open neighbourhood of the window. -/
theorem window_sub_Ioi : Set.Icc (1 / 2 : ℝ) 1 ⊆ Set.Ioi 0 :=
  fun t ht => lt_of_lt_of_le (by norm_num) ht.1

/-- **Almost every quarter-Cantor `y` has `y^{1/k} ∈ Ω_k`.**  Wiring proved: BB's analytic
corollary for each `G_p`, then a countable intersection over `p ∈ ℤ[X]`. -/
theorem ae_mem_Omega (hBB : BakerBanajiAnalyticQuarterCantor) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᵐ ω ∂coinMeasure, rootK k ω ∈ Omega k := by
  have hp : ∀ p : ℤ[X], ∀ᵐ ω ∂coinMeasure,
      1 ≤ p.natDegree → p.natDegree < k → IsAbsNormal (Gk k p (cantorReal ω)) := by
    intro p
    by_cases hlow : 1 ≤ p.natDegree ∧ p.natDegree < k
    · filter_upwards [hBB (Gk k p) (Set.Ioi 0) isOpen_Ioi window_sub_Ioi (analyticOnNhd_Gk k p)
        (exists_deriv2_Gk_ne_zero k p hlow.1 hlow.2)] with ω hω
      exact fun _ _ => hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hlow
  filter_upwards [ae_all_iff.2 hp] with ω hω
  exact mem_Omega_of (by omega) (fun p h1 h2 => hω p h1 h2) (top_witness k (by omega) ω)

/-- **`Ω_k ≠ ∅` for every `k ≥ 2`** (Manai: "It is not even known whether `Ω_k ≠ ∅`"),
conditional only on the published Baker–Banaji analytic corollary. -/
theorem Omega_nonempty (hBB : BakerBanajiAnalyticQuarterCantor) (k : ℕ) (hk : 2 ≤ k) :
    (Omega k).Nonempty := by
  obtain ⟨ω, hω⟩ := (ae_mem_Omega hBB k hk).exists
  exact ⟨_, hω⟩

/-! ### Explicit: uniform Baker–Banaji + derandomization over all `p` and all bases -/

/-- **Cited input: Baker–Banaji, arXiv 2401.01241v2, Corollary 1.5 (`t:self-similar`), main
clause with its explicit constant**, specialised to the law of `cantorReal`: there are
`η, κ, C > 0` depending only on `μ` such that for every `C²` `F` with `F'' ≠ 0` on the window,
`|\hat{F_*μ}(ξ)| ≤ C(1 + max|F'| + (max|F'|)^{-κ} + max|F''|)(1 + (min|F''|)^{-κ})|ξ|^{-η}`.

**Faithful-or-weaker.**  We quantify over bounds `A₁ ≥ max|F'|`, `a₁ ≤ max|F'|`,
`A₂ ≥ max|F''|`, `a₂ ≤ min|F''|`; each substitution can only enlarge BB's right side.  The window
change `A(s) = 1/2 + s/2` scales `F'` by `1/2` and `F''` by `1/4`, which costs a factor
`2^κ 4^κ`, absorbed into `C`.  `a₂ > 0` gives BB's `F'' ≠ 0` on `[0,1]`.  The IFS check is the
one refereed for `ExplicitSquare.BakerBanajiQuarterCantor`.  BB's `C, η, κ` need not be
effective.  ⚠️ Corrected 2026-10-02 (`docs/BAKER-BANAJI-ANALYTIC-REFEREE-2026-10-02.md`): the bound
is not monotone in `κ` (for `a > 1`) or `η` (for `|ξ| < 1`), so hard-coding rationals needs
`x^{-κ} ≤ 1 + x^{-κ'}` for `κ' ≥ κ` (so `C' ≥ 4C`) and `C' ≥ 1` to cover `|ξ| < 1`. -/
def BakerBanajiUniformQuarterCantor : Prop :=
  ∃ C η κ : ℝ, 0 < C ∧ 0 < η ∧ 0 < κ ∧
    ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
    ∀ A₁ a₁ A₂ a₂ : ℝ, 0 < a₁ → 0 < a₂ →
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A₁) →
    (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, a₁ ≤ |deriv F t|) →
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A₂) →
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a₂ ≤ |deriv (deriv F) t|) →
    ∀ ξ : ℝ, ξ ≠ 0 →
      ‖pushFourier F ξ‖ ≤ C * (1 + A₁ + a₁ ^ (-κ) + A₂) * (1 + a₂ ^ (-κ)) * |ξ| ^ (-η)

/-- The uniform form implies today's per-map form.

Confidence 97%.  Proof: `F'`, `F''` are continuous on the compact window (`ContDiffOn` on the
open `U ⊇ [1/2,1]`), so take `A₁, A₂` their maxima, `a₂` the minimum of `|F''|` (positive), and
`a₁ = |F'(t₀)|` if some `F'(t₀) ≠ 0`; if `F' ≡ 0` on the window then `F'' ≡ 0` there,
contradicting `F'' ≠ 0`. -/
theorem bakerBanajiQuarterCantor_of_uniform (h : BakerBanajiUniformQuarterCantor) :
    BakerBanajiQuarterCantor := by
  obtain ⟨C, η, κ, hC, hη, hκ, hB⟩ := h
  intro F U hU hsub hF hF''
  obtain ⟨A₁, a₁, A₂, a₂, ha₁, ha₂, h1, h2, h3, h4⟩ :=
    OmegaKCalculus.exists_window_bounds F U hU hsub hF hF''
  have hA₁ : 0 ≤ A₁ := (abs_nonneg _).trans (h1 1 ⟨by norm_num, le_rfl⟩)
  have hA₂ : 0 ≤ A₂ := (abs_nonneg _).trans (h3 1 ⟨by norm_num, le_rfl⟩)
  refine ⟨C * (1 + A₁ + a₁ ^ (-κ) + A₂) * (1 + a₂ ^ (-κ)), η, ?_, hη, fun ξ hξ =>
    hB F U hU hsub hF A₁ a₁ A₂ a₂ ha₁ ha₂ h1 h2 h3 h4 ξ hξ⟩
  have := Real.rpow_pos_of_pos ha₁ (-κ)
  have := Real.rpow_pos_of_pos ha₂ (-κ)
  positivity

/-- **Global polynomial decay for every `G_p`, `1 ≤ deg p < k`, despite inflection points.**

Confidence 85%.  English proof: `G_p''` has finitely many zeros `z₁ … z_d` (`d < k`) in
`[1/2, 1]`, each of finite order `≤ k − 2` (`exists_deriv2_Gk_ne_zero`'s polynomial in `s`), so
`|G_p''(t)| ≥ c_p · dist(t, Z)^{k−2}`.  Split `μ` into its `2^m` depth-`m` cylinders
`μ = 2^{-m} Σ_w (φ_w)_* μ`, `φ_w` affine of ratio `4^{-m}` (self-similarity).  Bad cylinders (hull
within `r` of `Z`) carry mass `≤ d(2·4^m r + 2)2^{-m}`.  On a good cylinder apply the uniform
bound to `F = G_p ∘ φ_w` (after the window rescaling): `max|F'| ≍ 4^{-m}`,
`min|F''| ≥ 16^{-m} c_p r^{k−2}`, so its transform is `≤ C_p 4^{mκ}(16^m r^{-(k−2)})^{κ}|ξ|^{-η}`.
Take `m = ⌊ε log₄|ξ|⌋`, `r = |ξ|^{-ε}` with `ε = ε(η, κ, k)` small: the total is `≤ C'_p|ξ|^{-δ}`,
`δ = δ(η, κ, k) > 0`.  All constants are computable from the coefficients of `p` (root
isolation for `c_p`). -/
theorem polyDecay_Gk (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ) (p : ℤ[X])
    (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) : PolyDecay (Gk k p) := by
  sorry

/-- **Simultaneous derandomization: one computable `e` making every `G_p(y)`, `1 ≤ deg p < k`,
normal in every base.**  The hardest step.

Confidence 70%.  English proof: enumerate `ℤ[X]` by coefficient lists `a ∈ List ℤ` (Primcodable).
`polyDecay_Gk` holds with **computable** rational constants `C(a), δ(a)` (BB's `C, η, κ`
hard-coded as rationals; the dependence on `p` is through computable bounds on `max|G_p'|`,
`max|G_p''|`, the root separation of `t²G_p''`).  Bad events `B(a, b, n)` (base `b`, level `n`,
as in `ComputableNormal.badT` with the sandwich test of
`exists_computable_isAbsNormal_sqrt_of_polyDecay`) are decided from a computable coin prefix
because `G_p(y)` is computable to precision `2^{-K}` from `y` to precision `2^{-K-c(a)}`.  Admit
`(a, b)` at level `n` only when `code a + b ≤ log₂ n`; the total mass is
`Σ_n 2c n^{-2} log² n · max C(a)` over admitted `a`, which needs admission thresholds `n(a)`
growing with `C(a)`, still computable; the tail modulus is computable.  Then
`Derandomize.exists_primrec_avoid`.  Every `(a, b)` is admitted from some level on, so each
`G_p(y)` is `b`-normal (`normal_of_good`). -/
theorem exists_computable_isAbsNormal_Gk (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ p : ℤ[X], 1 ≤ p.natDegree → p.natDegree < k →
      IsAbsNormal (Gk k p (cantorReal e)) := by
  sorry

/-- **Manai's problem, explicit part: a computable point of `Ω_k` for every `k ≥ 2`.**
`x_k = y^{1/k}`, `y = cantorReal e`, `e` computable.  Wiring proved from
`exists_computable_isAbsNormal_Gk` and `top_witness`. -/
theorem exists_computable_mem_Omega (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ)
    (hk : 2 ≤ k) : ∃ e : ℕ → Bool, Computable e ∧ rootK k e ∈ Omega k := by
  obtain ⟨e, hc, he⟩ := exists_computable_isAbsNormal_Gk hBB k
  exact ⟨e, hc, mem_Omega_of (by omega) (fun p h1 h2 => he p h1 h2) (top_witness k (by omega) e)⟩

/-! ### Hausdorff dimension -/

/-- A Borel probability measure on `ℝ` stationary for a **non-trivial** (no common fixed point)
finite IFS of similarities `t ↦ r_a t + c_a`, `0 < |r_a| < 1`, mapping `[1/2, 1]` into itself,
with positive weights summing to `1` (the class of Baker–Banaji Cor. 2.10 of arXiv v2, label
`c:analyticnormal`, after the window change).  With `IsProbabilityMeasure ν` this pins `ν` to the
unique stationary Borel probability on `ℝ`; the distinct-fixed-points clause excludes Dirac masses
(`docs/BAKER-BANAJI-GENERAL-REFEREE-2026-10-02.md`). -/
def IsSelfSimilarOnWindow (ν : Measure ℝ) : Prop :=
  ∃ (n : ℕ) (r c : Fin n → ℝ) (w : Fin n → ENNReal),
    (∀ a, r a ≠ 0 ∧ |r a| < 1) ∧ (∀ a, 0 < w a) ∧ ∑ a, w a = 1 ∧
    (∀ a, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, r a * t + c a ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
    (∃ a b, c a / (1 - r a) ≠ c b / (1 - r b)) ∧
    ν = ∑ a, w a • ν.map (fun t => r a * t + c a)

/-- **Cited input: Baker–Banaji, arXiv 2401.01241v2, Corollary 2.10 (`c:analyticnormal`)**, general
self-similar form: Property (A) for `F_*ν`, `F` analytic non-affine, `ν` self-similar.

**Faithful-or-weaker**: as for `BakerBanajiAnalyticQuarterCantor` (`q_n = bⁿ`, countably many
bases); the window change `s ↦ 1/2 + s/2` conjugates the IFS to one on `[0,1]` with the same
weights and ratios, still non-trivial; finite IFS makes BB's `Σ p_a|r_a|^{-τ} < ∞` automatic. -/
def BakerBanajiAnalytic : Prop :=
  ∀ ν : Measure ℝ, IsProbabilityMeasure ν → IsSelfSimilarOnWindow ν →
    ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → AnalyticOnNhd ℝ F U →
    (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t ≠ 0) → ∀ᵐ t ∂ν, IsAbsNormal (F t)

/-- The general form implies the quarter-Cantor form.  Confidence 95%: the law of
`cantorReal` is stationary for `t ↦ 1/2 + (t − 1/2)/4 + b/8`, `b ∈ {0,1}`, weights `1/2`, fixed
points `1/2 ≠ 2/3` (`docs/BAKER-BANAJI-REFEREE-2026-10-02.md`); transfer `∀ᵐ` along the map. -/
theorem bakerBanajiAnalyticQuarterCantor_of_general (h : BakerBanajiAnalytic) :
    BakerBanajiAnalyticQuarterCantor := by
  have hBB := h
  intro F U hU hsub hF hF''
  have hmc := CantorSelfSimilar.measurable_cantorReal
  have hss : IsSelfSimilarOnWindow (coinMeasure.map cantorReal) := by
    refine ⟨2, fun _ => 1 / 4, fun a => 3 / 8 + (if a = 1 then 1 / 8 else 0),
      fun _ => 2⁻¹, ?_, ?_, ?_, ?_, ⟨0, 1, by norm_num⟩, ?_⟩
    · intro _; norm_num [abs_of_pos]
    · intro _; simp
    · simp only [Fin.sum_univ_two, ENNReal.inv_two_add_inv_two]
    · intro a t ht
      obtain ⟨h1, h2⟩ := ht
      dsimp only
      split_ifs <;> constructor <;> linarith
    · ext A hA
      have hps : ∀ c, Measurable (CantorSelfSimilar.psi c) := fun c => by
        unfold CantorSelfSimilar.psi; fun_prop
      have hm : ∀ (a : Fin 2) (c : Bool), (c = true ↔ a = 1) →
          (coinMeasure.map cantorReal).map (fun t => 1 / 4 * t + (3 / 8 +
            (if a = 1 then 1 / 8 else 0))) A =
          (coinMeasure.map (CantorSelfSimilar.consB c)) (cantorReal ⁻¹' A) := by
        intro a c hc
        have hfm : Measurable (fun t : ℝ => 1 / 4 * t + (3 / 8 +
            (if a = 1 then (1 : ℝ) / 8 else 0))) := by fun_prop
        rw [Measure.map_apply hfm hA, Measure.map_apply hmc (hfm hA),
          Measure.map_apply (CantorSelfSimilar.measurable_consB c) (hmc hA)]
        congr 1; ext ω
        simp only [Set.mem_preimage, CantorSelfSimilar.cantorReal_consB,
          CantorSelfSimilar.psi]
        have he : (1 / 2 + if c = true then (1 : ℝ) / 8 else 0) + (cantorReal ω - 1 / 2) / 4 =
            1 / 4 * cantorReal ω + (3 / 8 + if a = 1 then 1 / 8 else 0) := by
          by_cases h : a = 1 <;> simp [h, hc] <;> ring
        rw [he]
      rw [Measure.finsetSum_apply, Fin.sum_univ_two, Measure.smul_apply, Measure.smul_apply,
        smul_eq_mul, smul_eq_mul, hm 0 false (by decide), hm 1 true (by decide),
        Measure.map_apply hmc hA]
      conv_lhs => rw [CantorSelfSimilar.coinMeasure_eq]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      ring
  have h := hBB (coinMeasure.map cantorReal) (Measure.isProbabilityMeasure_map hmc.aemeasurable)
    hss F U hU hsub hF hF''
  exact ae_of_ae_map hmc.aemeasurable h

/-- The missing-digit measure `DigitCantor.nu m` (base `m + 2`, digits `{0, …, m}`) is
self-similar on the window: maps `f_a t = t/(m+2) + 1/2 + (a − 1)/(2(m+2))`, weights `1/(m+1)`,
fixed points of `f_0, f_1` distinct. -/
theorem isSelfSimilarOnWindow_nu (m : ℕ) (hm : 1 ≤ m) :
    IsSelfSimilarOnWindow (DigitCantor.nu m) := by
  have hB : (0 : ℝ) < m + 2 := by positivity
  refine ⟨m + 1, fun _ => 1 / (m + 2 : ℝ), fun a => 1 / 2 + ((a : ℕ) - 1 : ℝ) / (2 * (m + 2)),
    fun _ => ((m + 1 : ℕ) : ENNReal)⁻¹, ?_, ?_, DigitCantor.card_inv_sum, ?_, ?_,
    DigitCantor.nu_eq_sum_map⟩
  · intro _
    refine ⟨by positivity, ?_⟩
    rw [abs_of_pos (by positivity), div_lt_one hB]
    linarith
  · intro _; simp
  · intro a t ht
    have ha : ((a : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 a.isLt
    have hkey : 1 / (m + 2 : ℝ) * t + (1 / 2 + ((a : ℕ) - 1 : ℝ) / (2 * (m + 2))) =
        1 / 2 + (2 * t + (a : ℕ) - 1) / (2 * (m + 2)) := by
      field_simp; ring
    rw [hkey]
    obtain ⟨ht1, ht2⟩ := ht
    have hn : 0 ≤ (2 * t + (a : ℕ) - 1) / (2 * (m + 2)) :=
      div_nonneg (by linarith [((a : ℕ).cast_nonneg : (0 : ℝ) ≤ (a : ℕ))]) (by positivity)
    have hu : (2 * t + (a : ℕ) - 1) / (2 * (m + 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    constructor <;> linarith
  · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    have hr : (1 : ℝ) - 1 / (m + 2) ≠ 0 := by
      have : 1 / (m + 2 : ℝ) < 1 := by rw [div_lt_one hB]; linarith
      intro h; linarith
    intro h
    rw [div_left_inj' hr] at h
    simp at h
    linarith

/-- `ν_m`-a.e. `y` has `y^{1/k} ∈ Ω_k` (the `ae_mem_Omega` argument, on `ν_m`). -/
theorem ae_digit_mem_Omega (hBB : BakerBanajiAnalytic) (k : ℕ) (hk : 2 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) :
    ∀ᵐ ω ∂DigitCantor.digitMeasure m, DigitCantor.yReal m ω ^ ((k : ℝ)⁻¹) ∈ Omega k := by
  have hp : ∀ p : ℤ[X], ∀ᵐ ω ∂DigitCantor.digitMeasure m,
      1 ≤ p.natDegree → p.natDegree < k → IsAbsNormal (Gk k p (DigitCantor.yReal m ω)) := by
    intro p
    by_cases hlow : 1 ≤ p.natDegree ∧ p.natDegree < k
    · have h := hBB (DigitCantor.nu m) inferInstance (isSelfSimilarOnWindow_nu m hm) (Gk k p)
        (Set.Ioi 0) isOpen_Ioi window_sub_Ioi (analyticOnNhd_Gk k p)
        (exists_deriv2_Gk_ne_zero k p hlow.1 hlow.2)
      filter_upwards [ae_of_ae_map DigitCantor.measurable_yReal.aemeasurable h] with ω hω
      exact fun _ _ => hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hlow
  filter_upwards [ae_all_iff.2 hp] with ω hω
  have hy0 : 0 ≤ DigitCantor.yReal m ω := by
    linarith [(DigitCantor.yReal_mem_Icc ω).1]
  refine mem_Omega_of (by omega) (fun p h1 h2 => hω p h1 h2) ⟨X ^ k, by simp, ?_⟩
  rw [show aeval (DigitCantor.yReal m ω ^ ((k : ℝ)⁻¹)) (X ^ k : ℤ[X]) = DigitCantor.yReal m ω by
    simp [Real.rpow_inv_natCast_pow hy0 (by omega : k ≠ 0)]]
  exact fun h => DigitCantor.not_isNormal_yReal ω (h (m + 2) (by omega))

/-- `x ↦ x^k` is `k`-Lipschitz on `[0, 1]`. -/
theorem lipschitzOnWith_pow (k : ℕ) :
    LipschitzOnWith (k : NNReal) (fun x : ℝ => x ^ k) (Set.Icc 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, Real.dist_eq]
  refine (abs_pow_sub_pow_le x y k).trans ?_
  have hmx : max |x| |y| ≤ 1 := max_le (by rw [abs_of_nonneg hx.1]; exact hx.2)
    (by rw [abs_of_nonneg hy.1]; exact hy.2)
  have : max |x| |y| ^ (k - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hmx
  simp only [NNReal.coe_natCast]
  calc |x - y| * k * max |x| |y| ^ (k - 1) ≤ |x - y| * k * 1 := by gcongr
    _ = k * |x - y| := by ring

/-- **`dim_H Ω_k ≥ d`** for every `d ≤ 1` with `(m+2)^d ≤ m + 1`: mass distribution on `ν_m`,
then the bi-Lipschitz root map. -/
theorem le_dimH_Omega (hBB : BakerBanajiAnalytic) (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hm : 1 ≤ m)
    (d : NNReal) (hd1 : d ≤ 1) (hd : ((m + 2 : ℕ) : ℝ) ^ (d : ℝ) ≤ m + 1) :
    (d : ENNReal) ≤ dimH (Omega k) := by
  set G := {ω | DigitCantor.yReal m ω ^ ((k : ℝ)⁻¹) ∈ Omega k}
  set E := DigitCantor.yReal m '' G
  have hE : 1 ≤ DigitCantor.nu m E := by
    have hGc : DigitCantor.digitMeasure m Gᶜ = 0 := ae_iff.1 (ae_digit_mem_Omega hBB k hk m hm)
    calc (1 : ENNReal) = DigitCantor.digitMeasure m Set.univ := measure_univ.symm
      _ ≤ DigitCantor.digitMeasure m G + DigitCantor.digitMeasure m Gᶜ := by
          rw [← Set.union_compl_self G]; exact measure_union_le _ _
      _ = DigitCantor.digitMeasure m G := by rw [hGc, add_zero]
      _ ≤ DigitCantor.digitMeasure m (DigitCantor.yReal m ⁻¹' E) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ ≤ DigitCantor.nu m E := Measure.le_map_apply DigitCantor.measurable_yReal.aemeasurable E
  have h1 := DigitCantor.le_dimH_of_one_le_nu d hd1 hd E hE
  set R := (fun t : ℝ => t ^ ((k : ℝ)⁻¹)) '' E
  have hk0 : k ≠ 0 := by omega
  have hRsub : R ⊆ Set.Icc 0 1 := by
    rintro _ ⟨_, ⟨ω, -, rfl⟩, rfl⟩
    have hy := DigitCantor.yReal_mem_Icc ω
    exact ⟨Real.rpow_nonneg (by linarith [hy.1]) _,
      Real.rpow_le_one (by linarith [hy.1]) hy.2 (by positivity)⟩
  have hRΩ : R ⊆ Omega k := by
    rintro _ ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
    exact hω
  have hER : E ⊆ (fun x : ℝ => x ^ k) '' R := by
    rintro _ ⟨ω, hω, rfl⟩
    refine ⟨_, ⟨_, ⟨ω, hω, rfl⟩, rfl⟩, ?_⟩
    exact Real.rpow_inv_natCast_pow (by linarith [(DigitCantor.yReal_mem_Icc ω).1]) hk0
  calc (d : ENNReal) ≤ dimH E := h1
    _ ≤ dimH ((fun x : ℝ => x ^ k) '' R) := dimH_mono hER
    _ ≤ dimH R := ((lipschitzOnWith_pow k).mono hRsub).dimH_image_le
    _ ≤ dimH (Omega k) := dimH_mono hRΩ

/-- `(2^L)^{(L−1)/L} = 2^{L−1} ≤ 2^L − 1`: the exponent `s_L = (L−1)/L` is admissible for
`ν_{2^L − 2}`. -/
theorem rpow_le_of_two_pow (L : ℕ) (hL : 1 ≤ L) :
    (((2 ^ L - 2 + 2 : ℕ) : ℝ)) ^ (((L : ℝ) - 1) / L) ≤ ((2 ^ L - 2 : ℕ) : ℝ) + 1 := by
  have h2L : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hc : ((2 ^ L - 2 + 2 : ℕ) : ℝ) = (2 : ℝ) ^ L := by
    rw [Nat.sub_add_cancel h2L]; push_cast; ring
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show (L : ℝ) * (((L : ℝ) - 1) / L) = ((L - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hL]; field_simp; push_cast; ring,
    Real.rpow_natCast]
  have hm : ((2 ^ L - 2 : ℕ) : ℝ) + 1 = ((2 ^ L - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h2L, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hm]
  have : 2 ^ (L - 1) ≤ 2 ^ L - 1 := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show L - 1 + 1 = L by omega).le
    have : 2 ^ L = 2 * 2 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  exact_mod_cast this

/-- **Manai's problem, dimension part: `dim_H Ω_k = 1` for every `k ≥ 2`.**

Proved from `BakerBanajiAnalytic`.  For a base `b = m + 2 ≥ 3`, `DigitCantor.nu m` is the law of
`y = 1/2 + z/2`, `z` with i.i.d. uniform base-`b` digits in `{0, …, b − 2}`: self-similar on the
window, so `BakerBanajiAnalytic` applies to every `G_p`; every `y` is non-normal in base `b`, so
`ν`-a.e. `y^{1/k} ∈ Ω_k`.  Frostman bound + mass distribution principle
(`DigitCantor.le_dimH_of_one_le_nu`) and bi-Lipschitz `t ↦ t^{1/k}` give
`dim_H Ω_k ≥ log(b−1)/log b → 1`; `≤ 1` since `Ω_k ⊆ ℝ`. -/
theorem dimH_Omega_eq_one (hBB : BakerBanajiAnalytic) (k : ℕ) (hk : 2 ≤ k) :
    dimH (Omega k) = 1 := by
  refine le_antisymm ((dimH_mono (Set.subset_univ _)).trans Real.dimH_univ.le) ?_
  by_contra hlt
  push Not at hlt
  have hDtop : dimH (Omega k) ≠ ⊤ := ne_top_of_lt hlt
  set D := (dimH (Omega k)).toReal
  have hD1 : D < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
    simpa using this
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / (1 - D))
  have hpos : 0 < 1 - D := by linarith
  have hL1 : (1 : ℝ) < L := by
    have : 1 ≤ 1 / (1 - D) := by
      rw [le_div_iff₀ hpos]; linarith [ENNReal.toReal_nonneg (a := dimH (Omega k))]
    linarith
  have hL1n : 2 ≤ L := by exact_mod_cast hL1
  have hLr : (0 : ℝ) < L := by linarith
  set d : NNReal := ⟨((L : ℝ) - 1) / L, div_nonneg (by linarith) hLr.le⟩
  have hd1 : d ≤ 1 := by
    rw [← NNReal.coe_le_coe]; show ((L : ℝ) - 1) / L ≤ 1
    rw [div_le_one hLr]; linarith
  have hm : 1 ≤ 2 ^ L - 2 := by
    have : 4 ≤ 2 ^ L := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1n
    omega
  have h := le_dimH_Omega hBB k hk (2 ^ L - 2) hm d hd1 (rpow_le_of_two_pow L (by omega))
  have h' := ENNReal.toReal_mono hDtop h
  simp only [ENNReal.coe_toReal] at h'
  change ((L : ℝ) - 1) / L ≤ D at h'
  rw [div_le_iff₀ hLr] at h'
  rw [div_lt_iff₀ hpos] at hL
  nlinarith

end NormalNumbers.ExplicitOmegaK
