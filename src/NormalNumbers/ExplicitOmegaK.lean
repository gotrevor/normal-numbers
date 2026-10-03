/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.OmegaKCalculus
import NormalNumbers.SqrtCantorAbs
import NormalNumbers.DigitCantor
import NormalNumbers.CantorCylinders

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

/-! ### Explicit decay across inflection points: the cylinder cut

This is Baker–Banaji's own proof of their Theorem 1.1 (arXiv 2401.01241v2, §`s:analyticthm`),
made effective.  Split `μ` into depth-`m` cylinders (`pushFourier_split`).  Discard the few
cylinders near the zeros of `G_p''` (`card_near_cylinders_le`).  Apply Cor 1.5's explicit
constant on the rest (`pushFourier_le_of_deriv2_ge`).  The zero set enters only through its
**size** and a lower bound `|G_p''(t)| ≥ c · Π_{z ∈ Z} |t − z|` (`deriv2_Gk_lower`), never through
where the zeros are.  So every constant is explicit in `k` and the coefficient height `hgt p`,
which is what the derandomization over all `p` needs (`decay_Gfam`).

**Sibling control.**  An affine map (`G_{X^k}` is the identity, `Gk_X_pow`) cannot meet the
cut's hypothesis (`not_deriv2_lower_of_deriv2_eq_zero`), consistent with `not_polyDecay_rat_affine`.
So the cut cannot "prove" decay for the one map where decay is false. -/

/-- Coefficient height `Σ_j |a_j|` of an integer polynomial. -/
noncomputable def hgt (p : ℤ[X]) : ℕ := ∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j).natAbs

theorem one_le_hgt {p : ℤ[X]} (hp : p ≠ 0) : 1 ≤ hgt p := by
  have hlc : (p.coeff p.natDegree).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact leadingCoeff_ne_zero.2 hp
  calc 1 ≤ (p.coeff p.natDegree).natAbs := Nat.one_le_iff_ne_zero.2 hlc
    _ ≤ hgt p := Finset.single_le_sum (f := fun j => (p.coeff j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (Nat.lt_succ_self _))

theorem hgt_cast (p : ℤ[X]) : (hgt p : ℝ) =
    ∑ j ∈ Finset.range (p.natDegree + 1), |(p.coeff j : ℝ)| := by
  simp [hgt, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

/-- The clamp `τ(σ)` of the `deriv2_Gk_lower` proof. -/
noncomputable def tauK (k : ℕ) (σ : ℝ) : ℝ := if σ < 0 then 1 / 2 else if σ ≤ 1 then σ ^ k else 1

theorem abs_pow_sub_pow_le_unit {a b : ℝ} (k : ℕ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hb1 : b ≤ 1) : |a ^ k - b ^ k| ≤ k * |a - b| := by
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := k)
  have hm : max |a| |b| ^ (k - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact max_le ha1 hb1
  calc _ ≤ _ := h
    _ ≤ |a - b| * k * 1 := by gcongr
    _ = _ := by ring

theorem abs_sub_tauK_le (k : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) (σ : ℝ) :
    |s ^ k - tauK k σ| ≤ k * |s - σ| := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold tauK
  split_ifs with h0 h1
  · have : 0 ≤ s ^ k := by positivity
    have : s ^ k ≤ 1 := pow_le_one₀ (by linarith) hs1
    rw [abs_sub_le_iff, abs_of_pos (by linarith : 0 < s - σ)]
    constructor <;> nlinarith
  · exact abs_pow_sub_pow_le_unit k (by linarith) hs1 (not_lt.1 h0) h1
  · have := abs_pow_sub_pow_le_unit k (by linarith) hs1 zero_le_one le_rfl
    rw [one_pow] at this
    calc _ ≤ _ := this
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith

/-- **Lower bound for `G_p''` by a product of distances.**

Confidence 90%.  English proof: with `s = t^{1/k} ∈ [2^{-1/k}, 1]` and `d = deg p`,
`k² t² G_p''(t) = Σ_{1 ≤ j ≤ d} j(j−k) a_j s^j = s R(s)` with `R ∈ ℤ[s]` of degree `d − 1` and
leading coefficient `d(d−k)a_d`, so `|lead R| ≥ 1`.  Over `ℂ`, `|R(s)| = |lead| Π|s − ρ_i| ≥
Π|s − Re ρ_i|` for real `s`.  For each real `σ` pick `τ(σ) = σ^k` if `0 ≤ σ ≤ 1`, `τ = 1` if
`σ > 1`, `τ = 1/2` if `σ < 0`; then `|s − σ| ≥ |t − τ(σ)|/k` (mean value theorem for `s ↦ s^k` on
`[0,1]`, resp. `1 − s^k ≤ k(1 − s)`, resp. `|t − 1/2| ≤ 1/2 ≤ s`).  With `t ≤ 1` and `s ≥ 1/2`:
`|G_p''(t)| ≥ |Q(s)| ≥ (1/2)k^{-2}k^{-(d−1)} Π|t − τ_i| ≥ (2k^{k+1})^{-1} Π|t − τ_i|`, and
`Z = {τ_i}` has `d − 1 ≤ k − 2` points (with multiplicity).  For `d = 1` the product is empty. -/
theorem deriv2_Gk_lower (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) :
    ∃ Z : Multiset ℝ, Z.card ≤ k - 2 ∧ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      ((2 : ℝ) * (k : ℝ) ^ (k + 1))⁻¹ * (Z.map fun z => |t - z|).prod ≤
        |deriv (deriv (Gk k p)) t| := by
  set d := p.natDegree with hd
  have hk0 : k ≠ 0 := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set Q := OmegaKCalculus.qPoly k p with hQ
  set R := Q.divX with hR
  have hQ0 : Q.coeff 0 = 0 := by
    rw [hQ, OmegaKCalculus.qPoly_coeff k p 0 (Nat.zero_le _)]; simp
  have hQR : ∀ s, Q.eval s = s * R.eval s := by
    intro s
    conv_lhs => rw [← divX_mul_X_add Q, hQ0]
    simp [mul_comm, hR]
  have hlc : 1 / (k : ℝ) ^ 2 ≤ |Q.coeff d| := by
    rw [hQ, OmegaKCalculus.qPoly_coeff k p d le_rfl]
    have hp0 : p ≠ 0 := by rintro rfl; simp [hd] at h1
    have ha : (1 : ℝ) ≤ |(p.coeff d : ℝ)| := by
      have : p.coeff d ≠ 0 := leadingCoeff_ne_zero.2 hp0
      have : (1 : ℤ) ≤ |p.coeff d| := Int.one_le_abs this
      exact_mod_cast this
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h1
    have hdk : (d : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hlt : (d : ℝ) / k - 1 < 0 := by rw [sub_neg, div_lt_one hkpos]; linarith
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < d / k by positivity), abs_of_neg hlt]
    have e1 : 1 / (k : ℝ) ≤ d / k := by gcongr
    have e2 : 1 / (k : ℝ) ≤ -(d / k - 1) := by
      rw [neg_sub, one_sub_div hkpos.ne']; gcongr; linarith
    calc 1 / (k : ℝ) ^ 2 = 1 * (1 / k) * (1 / k) := by ring
      _ ≤ _ := by gcongr
  have hQd : Q.natDegree = d := by
    apply le_antisymm
    · rw [hQ, OmegaKCalculus.qPoly]
      exact natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · apply le_natDegree_of_ne_zero
      intro h0; rw [h0, abs_zero] at hlc; have : 0 < 1 / (k : ℝ) ^ 2 := by positivity
      linarith
  have hRd : R.natDegree = d - 1 := by rw [hR, natDegree_divX_eq_natDegree_tsub_one, hQd]
  have hRlc : R.leadingCoeff = Q.coeff d := by
    rw [leadingCoeff, hRd, hR, coeff_divX]; congr 1; omega
  set P := R.map (algebraMap ℝ ℂ) with hP
  have hPd : P.natDegree = d - 1 := by rw [hP, natDegree_map, hRd]
  have hPlc : P.leadingCoeff = (Q.coeff d : ℂ) := by
    rw [hP, leadingCoeff_map, hRlc]; rfl
  refine ⟨P.roots.map fun ρ => tauK k ρ.re, ?_, fun t ht => ?_⟩
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hPd]; omega
  have ht0 : 0 < t := by linarith [ht.1]
  set s := t ^ ((k : ℝ)⁻¹) with hs
  have hsk : s ^ k = t := Real.rpow_inv_natCast_pow ht0.le hk0
  have hs1 : s ≤ 1 := Real.rpow_le_one ht0.le ht.2 (by positivity)
  have hst : t ≤ s := by
    rw [← hsk]; exact pow_le_of_le_one (by positivity) hs1 hk0
  have hs2 : 1 / 2 ≤ s := by linarith [ht.1]
  have hG : |deriv (deriv (Gk k p)) t| = |s * R.eval s| * t ^ (-2 : ℝ) := by
    rw [show Gk k p = OmegaKCalculus.gk k p from rfl,
      OmegaKCalculus.deriv2_gk_eq_qPoly k hk0 p ht0, abs_mul, ← hQ, hQR,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have ht2 : 1 ≤ t ^ (-2 : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht.2 (by norm_num)
  have hRe : ((R.eval s : ℝ) : ℂ) = (Q.coeff d : ℂ) * (P.roots.map fun ρ => (s : ℂ) - ρ).prod := by
    have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := P))
    have : ((R.eval s : ℝ) : ℂ) = P.eval (s : ℂ) := by
      rw [hP, eval_map_algebraMap, show (s : ℂ) = algebraMap ℝ ℂ s from rfl,
        aeval_algebraMap_apply, coe_aeval_eq_eval]; rfl
    rw [this]
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, hPlc, Multiset.map_map]
    simp
  have hRabs : |R.eval s| = |Q.coeff d| * (P.roots.map fun ρ => ‖(s : ℂ) - ρ‖).prod := by
    have := congrArg (fun z : ℂ => ‖z‖) hRe
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul] at this
    rw [this]; congr 1
    have := map_multiset_prod (normHom (α := ℂ)) (P.roots.map fun ρ => (s : ℂ) - ρ)
    simpa [Multiset.map_map, Function.comp_def] using this
  have hfac : ∀ ρ ∈ P.roots, (1 / (k : ℝ)) * |t - tauK k ρ.re| ≤ ‖(s : ℂ) - ρ‖ := by
    intro ρ _
    have h := abs_sub_tauK_le k (by omega) hs2 hs1 ρ.re
    rw [hsk] at h
    have hre : |s - ρ.re| ≤ ‖(s : ℂ) - ρ‖ := by
      have := Complex.abs_re_le_norm ((s : ℂ) - ρ); simpa using this
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hkpos]; nlinarith
  have hprod := Multiset.prod_map_le_prod_map₀ _ _ (fun ρ _ => by positivity) hfac
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate] at hprod
  have hn : P.roots.card ≤ k - 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hPd]; omega
  set PP := (P.roots.map fun ρ => |t - tauK k ρ.re|).prod with hPP
  have hPP0 : 0 ≤ PP := Multiset.prod_nonneg fun x hx => by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hx; exact abs_nonneg _
  rw [Multiset.map_map]
  change _ * PP ≤ _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hcmp : ((2 : ℝ) * (k : ℝ) ^ (k + 1))⁻¹ ≤ 1 / 2 * (1 / (k : ℝ) ^ 2) * (1 / k) ^ P.roots.card := by
    rw [div_pow, one_pow, show (1 / 2 : ℝ) * (1 / (k : ℝ) ^ 2) * (1 / (k : ℝ) ^ P.roots.card) =
      ((2 : ℝ) * (k : ℝ) ^ (2 + P.roots.card))⁻¹ by rw [pow_add]; field_simp]
    exact inv_anti₀ (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk1 (by omega)) (by norm_num))
  have hRpos : 0 ≤ (P.roots.map fun ρ => ‖(s : ℂ) - ρ‖).prod := Multiset.prod_nonneg fun x hx => by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg _
  rw [hG, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s), hRabs]
  calc ((2 : ℝ) * (k : ℝ) ^ (k + 1))⁻¹ * PP
      ≤ 1 / 2 * (1 / (k : ℝ) ^ 2) * ((1 / k) ^ P.roots.card * PP) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcmp hPP0
    _ ≤ s * (|Q.coeff d| * (P.roots.map fun ρ => ‖(s : ℂ) - ρ‖).prod) := by
        rw [← mul_assoc s]
        apply mul_le_mul (mul_le_mul hs2 hlc (by positivity) (by linarith)) hprod
          (by positivity) (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) ht2

/-- **Upper bounds for `G_p'` and `G_p''` on the window by the height.**

Confidence 95%.  English proof: on `t ∈ [1/2, 1]`, `G_p'(t) = Σ_j a_j (j/k) t^{j/k − 1}` and
`G_p''(t) = Σ_j a_j (j/k)(j/k − 1) t^{j/k − 2}` (`OmegaKCalculus.deriv2_gk`).  For `j ≤ d < k`:
`|j/k| < 1`, `t^{j/k − 1} ≤ 2`, `|(j/k)(j/k − 1)| ≤ 1/4`, `t^{j/k − 2} ≤ 4`. -/
theorem deriv_Gk_le (k : ℕ) (p : ℤ[X]) (hk : p.natDegree < k) :
    ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (Gk k p) t| ≤ 4 * (hgt p : ℝ) ∧
      |deriv (deriv (Gk k p)) t| ≤ 4 * (hgt p : ℝ) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hr : ∀ i ∈ Finset.range (p.natDegree + 1), 0 ≤ (i : ℝ) / k ∧ (i : ℝ) / k ≤ 1 := by
    intro i hi
    have hik : (i : ℝ) ≤ k := by
      have := Finset.mem_range.1 hi; exact_mod_cast (show i ≤ k by omega)
    exact ⟨by positivity, (div_le_one hkpos).2 hik⟩
  have hpow : ∀ e : ℝ, -2 ≤ e → e ≤ 0 → t ^ e ≤ 4 := by
    intro e he1 he2
    calc t ^ e ≤ t ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 he1
      _ = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht0.le]; norm_cast
      _ ≤ 4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith [ht.1]
  rw [hgt_cast, Finset.mul_sum]
  constructor
  · rw [show Gk k p = OmegaKCalculus.gk k p from rfl,
      (OmegaKCalculus.deriv_gk_eventually k p ht0).eq_of_nhds]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    obtain ⟨h0, h1⟩ := hr i hi
    rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have := hpow ((i : ℝ) / k - 1) (by linarith) (by linarith)
    have ha := abs_nonneg (p.coeff i : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, Real.rpow_pos_of_pos ht0 ((i : ℝ) / k - 1)]
  · rw [show Gk k p = OmegaKCalculus.gk k p from rfl, OmegaKCalculus.deriv2_gk k p ht0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    obtain ⟨h0, h1⟩ := hr i hi
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0,
      abs_of_nonpos (show (i : ℝ) / k - 1 ≤ 0 by linarith),
      abs_of_pos (Real.rpow_pos_of_pos ht0 ((i : ℝ) / k - 2))]
    have := hpow ((i : ℝ) / k - 2) (by linarith) (by linarith)
    have ha := abs_nonneg (p.coeff i : ℝ)
    have hq : (i : ℝ) / k * -((i : ℝ) / k - 1) ≤ 1 := by nlinarith
    have hq0 : 0 ≤ (i : ℝ) / k * -((i : ℝ) / k - 1) := by nlinarith
    calc |(p.coeff i : ℝ)| * ((i : ℝ) / k) * -((i : ℝ) / k - 1) * t ^ ((i : ℝ) / k - 2)
        = |(p.coeff i : ℝ)| * ((i : ℝ) / k * -((i : ℝ) / k - 1)) * t ^ ((i : ℝ) / k - 2) := by ring
      _ ≤ |(p.coeff i : ℝ)| * 1 * 4 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hq ha) this (Real.rpow_pos_of_pos ht0 _).le
            (by positivity)
      _ = 4 * |(p.coeff i : ℝ)| := by ring

/-- **Sibling control: the cut's hypothesis excludes maps with `F'' ≡ 0` on the window.**  A
finite `Z` misses some point of the window, where the product is positive. -/
theorem not_deriv2_lower_of_deriv2_eq_zero (F : ℝ → ℝ)
    (hF : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t = 0) {c : ℝ} (hc : 0 < c)
    (Z : Multiset ℝ) :
    ¬ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤ |deriv (deriv F) t| := by
  classical
  intro h
  obtain ⟨t, ht, htZ⟩ := (Set.Icc_infinite (show (1 / 2 : ℝ) < 1 by norm_num)).exists_notMem_finset
    Z.toFinset
  have hpos : 0 < (Z.map fun z => |t - z|).prod := by
    refine Multiset.prod_pos fun a ha => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 ha
    refine abs_pos.2 (sub_ne_zero.2 fun hzt => htZ ?_)
    rw [hzt]; exact Multiset.mem_toFinset.2 hz
  have := h t ht
  rw [hF t ht, abs_zero] at this
  linarith [mul_pos hc hpos]

/-- The identity map `G_{X^k}` fails the cut's hypothesis (the affine sibling). -/
theorem not_deriv2_lower_Gk_X_pow (k : ℕ) (hk : k ≠ 0) {c : ℝ} (hc : 0 < c) (Z : Multiset ℝ) :
    ¬ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤
      |deriv (deriv (Gk k (X ^ k))) t| := by
  refine not_deriv2_lower_of_deriv2_eq_zero _ (fun t ht => ?_) hc Z
  have hev : Gk k (X ^ k) =ᶠ[𝓝 t] id := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < t by linarith [ht.1])] with u hu
    exact Gk_X_pow k hk hu.le
  have hd : deriv (Gk k (X ^ k)) =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < t by linarith [ht.1])] with u hu
    have hev' : Gk k (X ^ k) =ᶠ[𝓝 u] id := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact Gk_X_pow k hk hv.le
    rw [hev'.deriv_eq, deriv_id]
  rw [hd.deriv_eq, deriv_const]

/-- Depth-`m` cylinder map: `psiL [w₀, …, w_{m−1}] = ψ_{w₀} ∘ ⋯ ∘ ψ_{w_{m−1}}`, affine of ratio
`4^{-m}`, mapping the window into itself. -/
noncomputable def psiL (w : List Bool) : ℝ → ℝ :=
  w.foldr (fun c f => CantorSelfSimilar.psi c ∘ f) id

theorem measurable_psi (c : Bool) : Measurable (CantorSelfSimilar.psi c) := by
  unfold CantorSelfSimilar.psi; fun_prop

theorem list_sum_flatMap_pair {β : Type*} (l : List (List Bool)) (g : List Bool → β)
    [AddCommMonoid β] :
    ((l.flatMap fun s => [false :: s, true :: s]).map g).sum =
      (l.map fun s => g (true :: s)).sum + (l.map fun s => g (false :: s)).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil, add_zero]
    abel

/-- **Depth-`m` self-similarity of `pushFourier`** (`pushFourier_self_similar` iterated):
`\hat{F_*μ}(ξ) = 2^{-m} Σ_{|w| = m} \hat{(F∘ψ_w)_*μ}(ξ)`. -/
theorem pushFourier_split (m : ℕ) : ∀ F : ℝ → ℝ, Measurable F → ∀ ξ : ℝ,
    pushFourier F ξ = ((2 : ℂ) ^ m)⁻¹ *
      ((Derandomize.allStrings m).map fun w => pushFourier (F ∘ psiL w) ξ).sum := by
  induction m with
  | zero => intro F _ ξ; simp [Derandomize.allStrings, psiL]
  | succ m ih =>
    intro F hF ξ
    rw [CantorSelfSimilar.pushFourier_self_similar F hF ξ, ih _ (hF.comp (measurable_psi true)) ξ,
      ih _ (hF.comp (measurable_psi false)) ξ, Derandomize.allStrings,
      list_sum_flatMap_pair (Derandomize.allStrings m) (fun w => pushFourier (F ∘ psiL w) ξ)]
    simp only [psiL, List.foldr_cons]
    rw [pow_succ]
    ring_nf
    rfl

open CantorCylinders in
theorem psiL_eq_phi : ∀ w : List Bool, psiL w = phi w
  | [] => by funext t; simp [psiL, phi, offs]
  | c :: w => by
    rw [← psi_comp_phi, ← psiL_eq_phi w]; rfl

open Classical CantorCylinders in
/-- **Few depth-`m` cylinders come within `r` of a point.**

Confidence 92%.  English proof: `psiL w t = L_w + (t − 1/2)4^{-m}` with
`L_w = 1/2 + Σ_{i<m} [w_i] 4^{-i}/8`; distinct `w` of length `m` give left ends `L_w` at mutual
distance `≥ 4^{-m}/2` (base-4 digits in `{0,1}`), and the image of the window has length
`4^{-m}/2`.  A cylinder meeting `(z − r, z + r)` has `L_w ∈ (z − r − 4^{-m}/2, z + r)`, an
interval of length `2r + 4^{-m}/2`, which holds at most `4·4^m r + 2` such points. -/
theorem card_near_cylinders_le (m : ℕ) (z r : ℝ) (hr : 0 < r) :
    (((Derandomize.allStrings m).filter fun w =>
      decide (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, |psiL w t - z| < r)).length : ℝ) ≤
        4 * 4 ^ m * r + 2 := by
  set δ : ℝ := 1 / 4 ^ m / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  set a : ℝ := z - r - 1 / 4 ^ m with ha
  set L : ℝ := 4 * 4 ^ m * r + 1 with hL
  set l := (Derandomize.allStrings m).filter fun w =>
      decide (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, |psiL w t - z| < r)
  have hnd : l.Nodup := (Derandomize.nodup_allStrings m).filter _
  have hlen : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have hmem : ∀ w ∈ l.toFinset, w.length = m ∧ 0 < (offs w - a) / δ ∧ (offs w - a) / δ < L := by
    intro w hw
    rw [List.mem_toFinset, List.mem_filter, Derandomize.mem_allStrings] at hw
    obtain ⟨hwl, hw⟩ := hw
    obtain ⟨t, ht, hlt⟩ := of_decide_eq_true hw
    rw [psiL_eq_phi, phi, hwl, abs_lt] at hlt
    have e1 : (1 / 2) / 4 ^ m ≤ t / 4 ^ m := by gcongr; exact ht.1
    have e2 : t / 4 ^ m ≤ 1 / 4 ^ m := by gcongr; exact ht.2
    refine ⟨hwl, div_pos (by linarith) hδ0, ?_⟩
    rw [div_lt_iff₀ hδ0, hL, hδ]
    have : (4 * 4 ^ m * r + 1) * (1 / 4 ^ m / 2) = 2 * r + 1 / 4 ^ m / 2 := by
      field_simp; ring
    rw [this]
    have : 1 / 2 / (4 : ℝ) ^ m = 1 / 4 ^ m / 2 := by ring
    linarith
  let f : List Bool → ℕ := fun w => ⌊(offs w - a) / δ⌋₊
  have hinj : Set.InjOn f l.toFinset := by
    intro w hw w' hw' hf
    by_contra hne
    obtain ⟨hl1, hp1, -⟩ := hmem w hw
    obtain ⟨hl2, hp2, -⟩ := hmem w' hw'
    have hs := offs_sep w w' (hl1.trans hl2.symm) hne
    rw [hl1] at hs
    have h1 := Nat.floor_le hp1.le
    have h2 := Nat.lt_floor_add_one ((offs w - a) / δ)
    have h3 := Nat.floor_le hp2.le
    have h4 := Nat.lt_floor_add_one ((offs w' - a) / δ)
    simp only [f] at hf
    rw [hf] at h1 h2
    have : |(offs w - a) / δ - (offs w' - a) / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ0, div_lt_one hδ0] at this
    rw [show offs w - a - (offs w' - a) = offs w - offs w' by ring] at this
    linarith
  have hmaps : Set.MapsTo f l.toFinset (Finset.range ⌈L⌉₊) := by
    intro w hw
    obtain ⟨-, hp, hL'⟩ := hmem w hw
    simp only [Finset.coe_range, Set.mem_Iio, f]
    rw [Nat.floor_lt hp.le]
    exact hL'.trans_le (Nat.le_ceil L)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hcard
  rw [hlen]
  have hL0 : 0 ≤ L := by positivity
  calc (l.toFinset.card : ℝ) ≤ ⌈L⌉₊ := by exact_mod_cast hcard
    _ ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
    _ = _ := by rw [hL]; ring

/-- **BB's uniform bound with the `max|F'|` lower bound discharged.**  Proved: from `hBB` with `A₁ = A₂ = A`, `a₂ = a`, `a₁ = a/4`.  The
missing hypothesis `∃ t, a/4 ≤ |F'(t)|`: by the mean value theorem for `F'` on `[1/2, 1]`
(`F` is `C²` on the open `U ⊇ [1/2,1]`), `|F'(1) − F'(1/2)| = |F''(c)|/2 ≥ a/2`, so one of the two
endpoints has `|F'| ≥ a/4`.  BB's factor `1 + A₁ + a₁^{-κ} + A₂` is `1 + 2A + (a/4)^{-κ}`. -/
theorem pushFourier_le_of_deriv2_ge (hBB : BakerBanajiUniformQuarterCantor) :
    ∃ C η κ : ℝ, 0 < C ∧ 0 < η ∧ 0 < κ ∧
      ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
      ∀ A a : ℝ, 0 < a →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a ≤ |deriv (deriv F) t|) →
      ∀ ξ : ℝ, ξ ≠ 0 →
        ‖pushFourier F ξ‖ ≤ C * (1 + 2 * A + (a / 4) ^ (-κ)) * (1 + a ^ (-κ)) * |ξ| ^ (-η) := by
  obtain ⟨C, η, κ, hC, hη, hκ, hB⟩ := hBB
  refine ⟨C, η, κ, hC, hη, hκ, fun F U hU hsub hF A a ha hA1 hA2 hlow ξ hξ => ?_⟩
  have hW : Set.Icc (1 / 2 : ℝ) 1 ⊆ U := hsub
  have hcont : ContinuousOn (deriv F) (Set.Icc (1 / 2 : ℝ) 1) :=
    (hF.continuousOn_deriv_of_isOpen hU (by norm_num)).mono hW
  have hdiff : DifferentiableOn ℝ (deriv F) (Set.Ioo (1 / 2 : ℝ) 1) :=
    ((hF.deriv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)).mono
      (Set.Ioo_subset_Icc_self.trans hW)
  obtain ⟨t, ht, hteq⟩ := exists_deriv_eq_slope (deriv F) (by norm_num : (1 / 2 : ℝ) < 1)
    hcont hdiff
  have hat := hlow t (Set.Ioo_subset_Icc_self ht)
  rw [hteq] at hat
  have key : ∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, a / 4 ≤ |deriv F t| := by
    by_contra hno
    push Not at hno
    have h1 := hno 1 ⟨by norm_num, le_rfl⟩
    have h2 := hno (1 / 2) ⟨le_rfl, by norm_num⟩
    have : |deriv F 1 - deriv F (1 / 2)| < a / 2 :=
      (abs_sub _ _).trans_lt (by linarith)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      le_div_iff₀ (by norm_num)] at hat
    linarith
  have := hB F U hU hsub hF A (a / 4) A a (by positivity) ha hA1 key hA2 hlow ξ hξ
  convert this using 3
  ring

/-! #### Cylinder-cut helpers -/

theorem cantorReal_mem_window (ω : ℕ → Bool) : cantorReal ω ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  refine ⟨?_, (cantorReal_mem_Ico ω).2.le⟩
  have hsum : Summable fun i => (cantorDigits ω i : ℝ) / ((2 : ℕ) : ℝ) ^ (i + 1) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_two).mul_left (1 / 2))
    have : (cantorDigits ω i : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (cantorDigits_lt ω i)
    rw [Nat.cast_ofNat, pow_succ]
    calc (cantorDigits ω i : ℝ) / (2 ^ i * 2) ≤ 1 / (2 ^ i * 2) := by gcongr
      _ = 1 / 2 * (1 / 2) ^ i := by rw [div_pow, one_pow]; field_simp
  have := hsum.le_tsum 0 (fun j _ => by positivity)
  unfold cantorReal realOfDigits
  simpa [cantorDigits] using this

theorem pushFourier_congr_window {F G : ℝ → ℝ} (h : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, F t = G t)
    (ξ : ℝ) : pushFourier F ξ = pushFourier G ξ := by
  unfold pushFourier
  congr 1; funext ω
  rw [h _ (cantorReal_mem_window ω)]

theorem norm_pushFourier_le_one (F : ℝ → ℝ) (ξ : ℝ) : ‖pushFourier F ξ‖ ≤ 1 := by
  unfold pushFourier
  refine (norm_integral_le_integral_norm _).trans ?_
  have : ∀ ω : ℕ → Bool, ‖Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (cantorReal ω) : ℝ) : ℂ))‖ = 1 := by
    intro ω
    rw [show 2 * Real.pi * Complex.I * ((ξ * F (cantorReal ω) : ℝ) : ℂ) =
      ((2 * Real.pi * (ξ * F (cantorReal ω)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [integral_congr_ae (Eventually.of_forall this)]
  simp

theorem deriv_comp_affine (F : ℝ → ℝ) (o s : ℝ) :
    deriv (fun t => F (o + s * t)) = fun t => s * deriv F (o + s * t) := by
  funext t
  have := deriv_comp_mul_left (f := fun u => F (o + u)) (c := s) (x := t)
  simp only [smul_eq_mul] at this
  rw [this, deriv_comp_const_add]

theorem psiL_affine (w : List Bool) : psiL w = fun t =>
    CantorCylinders.offs w + (1 / 4 ^ w.length) * t := by
  rw [psiL_eq_phi]; funext t; simp [CantorCylinders.phi]; ring

theorem length_allStrings (m : ℕ) : (Derandomize.allStrings m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Derandomize.allStrings, List.length_flatMap, List.length_cons, List.length_nil]
    simp [ih, pow_succ]

theorem length_filter_exists_le {α β : Type*} [DecidableEq β] (l : List α) (s : Finset β)
    (q : β → α → Bool) :
    (l.filter fun w => decide (∃ z ∈ s, q z w = true)).length ≤
      ∑ z ∈ s, (l.filter (q z)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    have hsplit : ∑ z ∈ s, ((if q z a = true then a :: l.filter (q z) else l.filter (q z))).length
        = ∑ z ∈ s, ((if q z a = true then 1 else 0) + (l.filter (q z)).length) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp [add_comm]
    rw [hsplit, Finset.sum_add_distrib]
    split_ifs with h
    · obtain ⟨z, hz, hqz⟩ := of_decide_eq_true h
      have : 1 ≤ ∑ z ∈ s, (if q z a = true then 1 else 0) :=
        le_trans (by simp [hqz]) (Finset.single_le_sum (f := fun z => if q z a = true then 1 else 0)
          (fun _ _ => Nat.zero_le _) hz)
      simp only [List.length_cons]; omega
    · omega

theorem list_sum_le_bad {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ w ∈ l, f w ≤ 1) (h2 : ∀ w ∈ l, p w = false → f w ≤ B) :
    (l.map f).sum ≤ (l.filter p).length + l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih := ih (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
      (fun w hw => h2 w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.sum_cons, List.filter_cons, List.length_cons]
    cases hp : p a
    · have := h2 a List.mem_cons_self hp; simp; linarith
    · have := h1 a List.mem_cons_self; simp; linarith

/-- **One good cylinder**: Baker–Banaji's explicit bound for `F ∘ psiL w` when the window image
stays `≥ s = 4^{-m}` from every point of `Z`. -/
theorem good_cylinder_bound {C η κ : ℝ}
    (hB : ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
      ∀ A a : ℝ, 0 < a →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a ≤ |deriv (deriv F) t|) →
      ∀ ξ : ℝ, ξ ≠ 0 →
        ‖pushFourier F ξ‖ ≤ C * (1 + 2 * A + (a / 4) ^ (-κ)) * (1 + a ^ (-κ)) * |ξ| ^ (-η))
    (N : ℕ) (F : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆ U)
    (hF : ContDiffOn ℝ 2 F U) (c A : ℝ) (hc : 0 < c)
    (hA1 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A)
    (hA2 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A)
    (Z : Multiset ℝ) (hZ : Z.card ≤ N)
    (hlow : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤ |deriv (deriv F) t|)
    (w : List Bool)
    (hfar : ∀ z ∈ Z, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, 1 / 4 ^ w.length ≤ |psiL w t - z|)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖pushFourier (F ∘ psiL w) ξ‖ ≤
      C * (1 + 2 * A + (c * (1 / 4 ^ w.length) ^ (N + 2) / 4) ^ (-κ)) *
        (1 + (c * (1 / 4 ^ w.length) ^ (N + 2)) ^ (-κ)) * |ξ| ^ (-η) := by
  set s : ℝ := 1 / 4 ^ w.length with hs
  set o := CantorCylinders.offs w
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  have hφ : psiL w = fun t => o + s * t := psiL_affine w
  have hwin : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, psiL w t ∈ Set.Icc (1 / 2 : ℝ) 1 := fun t ht => by
    rw [psiL_eq_phi]; exact CantorCylinders.phi_mem_window w ht
  have hcomp : F ∘ psiL w = fun t => F (o + s * t) := by rw [hφ]; rfl
  have hd1 : deriv (F ∘ psiL w) = fun t => s * deriv F (o + s * t) := by
    rw [hcomp, deriv_comp_affine]
  have hd2 : deriv (deriv (F ∘ psiL w)) = fun t => s * (s * deriv (deriv F) (o + s * t)) := by
    rw [hd1, deriv_const_mul_field', deriv_comp_affine]
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA1 1 ⟨by norm_num, le_rfl⟩)
  have hcont : Continuous (psiL w) := by rw [hφ]; fun_prop
  have hcd : ContDiffOn ℝ 2 (psiL w) (psiL w ⁻¹' U) := by
    rw [hφ]; exact (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  refine hB (F ∘ psiL w) (psiL w ⁻¹' U) (hU.preimage hcont) (fun t ht => hsub (hwin t ht))
    (hF.comp hcd (fun t ht => ht)) A _ (by positivity) ?_ ?_ ?_ ξ hξ
  · intro t ht
    have := hA1 _ (hwin t ht)
    rw [hd1]; simp only [hφ] at this ⊢
    rw [abs_mul, abs_of_pos hs0]; nlinarith [abs_nonneg (deriv F (o + s * t))]
  · intro t ht
    have := hA2 _ (hwin t ht)
    rw [hd2]; simp only [hφ] at this ⊢
    rw [abs_mul, abs_mul, abs_of_pos hs0]
    have h0 := abs_nonneg (deriv (deriv F) (o + s * t))
    have : s * |deriv (deriv F) (o + s * t)| ≤ A := by nlinarith
    nlinarith
  · intro t ht
    have hl := hlow _ (hwin t ht)
    have hprod : s ^ N ≤ (Z.map fun z => |psiL w t - z|).prod := by
      have := Multiset.prod_map_le_prod_map₀ (s := Z) (fun _ => s) (fun z => |psiL w t - z|)
        (fun _ _ => hs0.le) (fun z hz => hfar z hz t ht)
      rw [Multiset.map_const', Multiset.prod_replicate] at this
      exact (pow_le_pow_of_le_one hs0.le hs1 hZ).trans this
    rw [hd2]; simp only [hφ] at hl hprod ⊢
    rw [abs_mul, abs_mul, abs_of_pos hs0]
    have hcs : c * s ^ N ≤ |deriv (deriv F) (o + s * t)| :=
      (mul_le_mul_of_nonneg_left hprod hc.le).trans hl
    calc c * s ^ (N + 2) = s * (s * (c * s ^ N)) := by ring
      _ ≤ _ := by gcongr
theorem norm_list_map_sum_le {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map fun a => ‖f a‖).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact (norm_add_le _ _).trans (by linarith)

/-- **The cut at depth `m`**: bad cylinders cost `≤ 6N·2^{-m}`, good ones BB's bound. -/
theorem pushFourier_cut_split {C η κ : ℝ}
    (hB : ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
      ∀ A a : ℝ, 0 < a →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a ≤ |deriv (deriv F) t|) →
      ∀ ξ : ℝ, ξ ≠ 0 →
        ‖pushFourier F ξ‖ ≤ C * (1 + 2 * A + (a / 4) ^ (-κ)) * (1 + a ^ (-κ)) * |ξ| ^ (-η))
    (hC : 0 < C)
    (N : ℕ) (F : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆ U)
    (hF : ContDiffOn ℝ 2 F U) (c A : ℝ) (hc : 0 < c)
    (hA1 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A)
    (hA2 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A)
    (Z : Multiset ℝ) (hZ : Z.card ≤ N)
    (hlow : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤ |deriv (deriv F) t|)
    (m : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖pushFourier F ξ‖ ≤ 6 * N / 2 ^ m +
      C * (1 + 2 * A + (c * (1 / 4 ^ m) ^ (N + 2) / 4) ^ (-κ)) *
        (1 + (c * (1 / 4 ^ m) ^ (N + 2)) ^ (-κ)) * |ξ| ^ (-η) := by
  classical
  set B := C * (1 + 2 * A + (c * (1 / 4 ^ m) ^ (N + 2) / 4) ^ (-κ)) *
        (1 + (c * (1 / 4 ^ m) ^ (N + 2)) ^ (-κ)) * |ξ| ^ (-η) with hBdef
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA1 1 ⟨by norm_num, le_rfl⟩)
  have hB0 : 0 ≤ B := by
    have h1 := Real.rpow_nonneg (show 0 ≤ c * (1 / 4 ^ m) ^ (N + 2) / 4 by positivity) (-κ)
    have h2 := Real.rpow_nonneg (show 0 ≤ c * (1 / 4 ^ m) ^ (N + 2) by positivity) (-κ)
    have h3 := Real.rpow_nonneg (abs_nonneg ξ) (-η)
    positivity
  set r : ℝ := 1 / 4 ^ m with hr
  have hr0 : 0 < r := by positivity
  set G := U.piecewise F 0
  have hGm : Measurable G :=
    ContinuousOn.measurable_piecewise (hF.continuousOn) continuousOn_const hU.measurableSet
  have hwin : ∀ (w : List Bool), ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, psiL w t ∈ Set.Icc (1 / 2 : ℝ) 1 :=
    fun w t ht => by rw [psiL_eq_phi]; exact CantorCylinders.phi_mem_window w ht
  have hFG : pushFourier F ξ = pushFourier G ξ :=
    pushFourier_congr_window (fun t ht => (Set.piecewise_eq_of_mem _ _ _ (hsub ht)).symm) ξ
  have hterm : ∀ w : List Bool, pushFourier (G ∘ psiL w) ξ = pushFourier (F ∘ psiL w) ξ :=
    fun w => pushFourier_congr_window (fun t ht =>
      Set.piecewise_eq_of_mem _ _ _ (hsub (hwin w t ht))) ξ
  rw [hFG, pushFourier_split m G hGm ξ]
  simp only [hterm]
  set l := Derandomize.allStrings m
  let near : ℝ → List Bool → Bool := fun z w =>
    decide (∃ t ∈ Set.Icc (1 / 2 : ℝ) 1, |psiL w t - z| < r)
  let p : List Bool → Bool := fun w => decide (∃ z ∈ Z.toFinset, near z w = true)
  have hsum := list_sum_le_bad l p (fun w => ‖pushFourier (F ∘ psiL w) ξ‖) hB0
    (fun w _ => norm_pushFourier_le_one _ _) (fun w hw hpw => by
      have hwl : w.length = m := (Derandomize.mem_allStrings m w).1 hw
      refine good_cylinder_bound hB N F U hU hsub hF c A hc hA1 hA2 Z hZ hlow w ?_ ξ hξ |>.trans
        (by rw [hwl])
      intro z hz t ht
      by_contra hlt
      push Not at hlt
      have : p w = true := by
        refine decide_eq_true ⟨z, Multiset.mem_toFinset.2 hz, decide_eq_true ⟨t, ht, ?_⟩⟩
        rw [hwl] at hlt; exact hlt
      rw [this] at hpw; exact Bool.noConfusion hpw)
  have hcount : ((l.filter p).length : ℝ) ≤ 6 * N := by
    have h1 := length_filter_exists_le l Z.toFinset near
    have h2 : ∀ z ∈ Z.toFinset, ((l.filter (near z)).length : ℝ) ≤ 6 := by
      intro z _
      have := card_near_cylinders_le m z r hr0
      have e : (4 : ℝ) * 4 ^ m * r = 4 := by rw [hr]; field_simp
      rw [e] at this
      exact this.trans (by norm_num)
    calc ((l.filter p).length : ℝ) ≤ ∑ z ∈ Z.toFinset, ((l.filter (near z)).length : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ z ∈ Z.toFinset, (6 : ℝ) := Finset.sum_le_sum h2
      _ = Z.toFinset.card * 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * 6 := by
          gcongr; exact_mod_cast (Multiset.toFinset_card_le Z).trans hZ
      _ = 6 * N := by ring
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  have hlen : (l.length : ℝ) = 2 ^ m := by rw [length_allStrings]; push_cast; ring
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  calc (2 ^ m : ℝ)⁻¹ * ‖(l.map fun w => pushFourier (F ∘ psiL w) ξ).sum‖
      ≤ (2 ^ m : ℝ)⁻¹ * ((l.filter p).length + l.length * B) := by
        gcongr
        exact (norm_list_map_sum_le _ _).trans hsum
    _ ≤ (2 ^ m : ℝ)⁻¹ * (6 * N + 2 ^ m * B) := by rw [hlen]; gcongr
    _ = 6 * N / 2 ^ m + B := by field_simp
/-- `4^m ≤ X^ε < 4^{m+1}` for `m = ⌊ε log₄ X⌋₊`. -/
theorem exists_pow4_bracket {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) :
    ∃ m : ℕ, (4 : ℝ) ^ m ≤ X ^ ε ∧ X ^ ε < 4 * 4 ^ m := by
  set L := Real.logb 4 (X ^ ε)
  have hXe : 1 ≤ X ^ ε := Real.one_le_rpow hX hε.le
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) hXe
  have h4L : (4 : ℝ) ^ L = X ^ ε := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  refine ⟨⌊L⌋₊, ?_, ?_⟩
  · rw [← h4L, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL)
  · rw [← h4L, ← pow_succ', ← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by push_cast; exact Nat.lt_floor_add_one L)

/-- Bad-cylinder weight: `2^{-m} < 2 X^{-ε/2}`. -/
theorem inv_two_pow_le {X ε : ℝ} (hX : 1 ≤ X) (m : ℕ) (h : X ^ ε < 4 * 4 ^ m) :
    1 / (2 : ℝ) ^ m ≤ 2 * X ^ (-(ε / 2)) := by
  have hX0 : 0 < X := by linarith
  have hsq : (X ^ (ε / 2)) ^ 2 = X ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have h2 : (X ^ (ε / 2)) ^ 2 < (2 * 2 ^ m) ^ 2 := by
    rw [hsq, mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num; linarith
  have h3 : X ^ (ε / 2) < 2 * 2 ^ m :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hp : 0 < X ^ (ε / 2) := Real.rpow_pos_of_pos hX0 _
  rw [Real.rpow_neg hX0.le, div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = (X ^ (ε / 2))⁻¹ * X ^ (ε / 2) := by field_simp
    _ ≤ (X ^ (ε / 2))⁻¹ * (2 * 2 ^ m) := by gcongr
    _ = _ := by ring

/-- Good-cylinder lower bound: `a^{-κ} ≤ (1+c⁻¹)^{⌈κ⌉} X^{η/4}` for `a = c 4^{-m(N+2)}`. -/
theorem a_rpow_neg_le {X ε κ η c : ℝ} (hX : 1 ≤ X) (hκ : 0 < κ) (hc : 0 < c)
    (N m : ℕ) (hm : (4 : ℝ) ^ m ≤ X ^ ε) (hεκ : ε * (N + 2) * κ = η / 4) :
    (c * (1 / 4 ^ m) ^ (N + 2)) ^ (-κ) ≤ (1 + c⁻¹) ^ ⌈κ⌉₊ * X ^ (η / 4) := by
  have hX0 : 0 < X := by linarith
  have hM : (0 : ℝ) < 4 ^ m := by positivity
  rw [Real.mul_rpow hc.le (by positivity)]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · rw [Real.rpow_neg hc.le, ← Real.inv_rpow hc.le]
    calc c⁻¹ ^ κ ≤ (1 + c⁻¹) ^ κ := Real.rpow_le_rpow (by positivity) (by linarith) hκ.le
      _ ≤ (1 + c⁻¹) ^ (⌈κ⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [inv_pos.2 hc]) (Nat.le_ceil κ)
      _ = _ := Real.rpow_natCast _ _
  · rw [one_div, inv_pow, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv]
    calc (((4 : ℝ) ^ m) ^ (N + 2)) ^ κ ≤ ((X ^ ε) ^ (N + 2)) ^ κ := by gcongr
      _ = X ^ (η / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← hεκ]
          push_cast; ring_nf

set_option maxHeartbeats 1000000 in
/-- **The cylinder cut: explicit polynomial decay when `|F''| ≥ c · Π_{z ∈ Z}|t − z|`, `|Z| ≤ N`.**

Confidence 88%.  English proof (BB Thm 1.1's proof, effective).  Take `K ≥ 1` from the end.  For
`|ξ| < 1`, `‖pushFourier‖ ≤ 1 ≤ K·…`.  For `|ξ| ≥ 1` put `ε = η/(4κ(N+2))`,
`m = ⌊ε log₄|ξ|⌋` (so `4^m ≤ |ξ|^ε < 4^{m+1}`) and `r = |ξ|^{-ε} ≤ 4^{-m}`.  Replace `F` by
`U.piecewise F 0` (same values on the support) to get measurability and apply
`pushFourier_split m`.  **Bad** `w` (window image within `r` of some `z ∈ Z`): at most
`N(4·4^m r + 2) ≤ 6N` of them (`card_near_cylinders_le`), each term `≤ 1`, weight `2^{-m} <
2|ξ|^{-ε/2}`.  **Good** `w`: `F_w = F ∘ psiL w` is `C²` on `(psiL w)⁻¹ U ⊇ [1/2,1]`, with
`F_w' = 4^{-m}F'∘ψ_w`, `F_w'' = 16^{-m}F''∘ψ_w`, so `|F_w'|, |F_w''| ≤ A` and
`|F_w''| ≥ a := 16^{-m} c r^N` (each `|t − z| ≥ r`, `r ≤ 1`, `|Z| ≤ N`).  So
`a^{-1} ≤ (1 + c⁻¹)|ξ|^{(N+2)ε}`, and `pushFourier_le_of_deriv2_ge` bounds the term by
`C(1+2A+4^κ X)(1+X)|ξ|^{-η} ≤ C 4^{κ+2}(1+A)(1+c⁻¹)^{2⌈κ⌉}|ξ|^{2κ(N+2)ε − η}`,
`X = (1+c⁻¹)^{⌈κ⌉}|ξ|^{κ(N+2)ε}`, and `2κ(N+2)ε = η/2`.  Total: `δ = min(η/2, ε/2)` and
`K ≥ max(2⌈κ⌉, C 4^{κ+2} + 12N + 1)`. -/
theorem pushFourier_le_of_deriv2_lower (hBB : BakerBanajiUniformQuarterCantor) (N : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
      ∀ c A : ℝ, 0 < c →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv F t| ≤ A) →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, |deriv (deriv F) t| ≤ A) →
      ∀ Z : Multiset ℝ, Z.card ≤ N →
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, c * (Z.map fun z => |t - z|).prod ≤ |deriv (deriv F) t|) →
      ∀ ξ : ℝ, ξ ≠ 0 → ‖pushFourier F ξ‖ ≤ K * (1 + A) * (1 + c⁻¹) ^ K * |ξ| ^ (-δ) := by
  obtain ⟨C, η, κ, hC, hη, hκ, hB⟩ := pushFourier_le_of_deriv2_ge hBB
  set ε : ℝ := η / (4 * κ * (N + 2)) with hεdef
  have hε : 0 < ε := by positivity
  have hεκ : ε * (N + 2) * κ = η / 4 := by rw [hεdef]; field_simp
  set δ : ℝ := min ε η / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδε : δ ≤ ε / 2 := by rw [hδdef]; gcongr; exact min_le_left _ _
  have hδη : δ ≤ η / 2 := by rw [hδdef]; gcongr; exact min_le_right _ _
  set D : ℝ := 2 * C * (2 + 4 ^ κ) with hD
  set K : ℕ := 12 * N + ⌈D⌉₊ + 2 * ⌈κ⌉₊ + 1 with hK
  refine ⟨K, by omega, δ, hδ, fun F U hU hsub hF c A hc hA1 hA2 Z hZ hlow ξ hξ => ?_⟩
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA1 1 ⟨by norm_num, le_rfl⟩)
  set X := |ξ| with hXdef
  have hX0 : 0 < X := abs_pos.2 hξ
  have hb1 : (1 : ℝ) ≤ 1 + c⁻¹ := by linarith [inv_pos.2 hc]
  set P : ℝ := (1 + c⁻¹) ^ ⌈κ⌉₊ with hP
  set Q : ℝ := (1 + c⁻¹) ^ K with hQ
  have hP1 : 1 ≤ P := one_le_pow₀ hb1
  have hQ1 : 1 ≤ Q := one_le_pow₀ hb1
  have hPQ : P * P ≤ Q := by
    rw [hP, hQ, ← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
  have hKr : (12 * N + D + 1 : ℝ) ≤ K := by
    rw [hK]; push_cast; linarith [Nat.le_ceil D, (Nat.cast_nonneg ⌈κ⌉₊ : (0 : ℝ) ≤ _)]
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  rcases lt_or_ge X 1 with hX1 | hX1
  · have hu : 1 ≤ X ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hX0 hX1.le (by linarith)
    calc ‖pushFourier F ξ‖ ≤ 1 := norm_pushFourier_le_one F ξ
      _ ≤ (K : ℝ) * (1 + A) * Q * X ^ (-δ) := by
          have : (1 : ℝ) ≤ K := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
          have h1 : 1 ≤ (K : ℝ) * (1 + A) := by nlinarith
          have h2 : 1 ≤ (K : ℝ) * (1 + A) * Q := by nlinarith
          nlinarith
  obtain ⟨m, hm1, hm2⟩ := exists_pow4_bracket hX1 hε
  have hsplit := pushFourier_cut_split hB hC N F U hU hsub hF c A hc hA1 hA2 Z hZ hlow m ξ hξ
  set a : ℝ := c * (1 / 4 ^ m) ^ (N + 2) with ha
  have ha0 : 0 < a := by positivity
  set Y : ℝ := P * X ^ (η / 4) with hY
  have hXη4 : 1 ≤ X ^ (η / 4) := Real.one_le_rpow hX1 (by positivity)
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have haY : a ^ (-κ) ≤ Y := a_rpow_neg_le hX1 hκ hc N m hm1 hεκ
  have ha4 : (a / 4) ^ (-κ) = 4 ^ κ * a ^ (-κ) := by
    rw [Real.div_rpow ha0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    field_simp
  have h4κ : 0 < (4 : ℝ) ^ κ := by positivity
  have hbad := inv_two_pow_le hX1 m hm2
  have hu : X ^ (-(ε / 2)) ≤ X ^ (-δ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hw : X ^ (η / 4) * X ^ (η / 4) * X ^ (-η) ≤ X ^ (-δ) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXη : 0 < X ^ (-η) := Real.rpow_pos_of_pos hX0 _
  have hXδ : 0 < X ^ (-δ) := Real.rpow_pos_of_pos hX0 _
  -- bad part
  have hbad' : 6 * (N : ℝ) / 2 ^ m ≤ 12 * N * X ^ (-δ) := by
    rw [div_eq_mul_one_div]
    calc 6 * (N : ℝ) * (1 / 2 ^ m) ≤ 6 * N * (2 * X ^ (-(ε / 2))) := by gcongr
      _ ≤ 6 * N * (2 * X ^ (-δ)) := by gcongr
      _ = _ := by ring
  -- good part
  have hgood : C * (1 + 2 * A + (a / 4) ^ (-κ)) * (1 + a ^ (-κ)) * X ^ (-η) ≤
      D * (1 + A) * Q * X ^ (-δ) := by
    rw [ha4]
    have e1 : 1 + 2 * A + 4 ^ κ * a ^ (-κ) ≤ (2 + 4 ^ κ) * (1 + A) * Y := by
      have h1 : 4 ^ κ * a ^ (-κ) ≤ 4 ^ κ * Y := by gcongr
      have h2 : A ≤ A * Y := le_mul_of_one_le_right hA0 hY1
      have h3 : 0 ≤ 4 ^ κ * A * Y := by positivity
      have : (2 + 4 ^ κ) * (1 + A) * Y = 2 * Y + 2 * (A * Y) + 4 ^ κ * Y + 4 ^ κ * A * Y := by ring
      rw [this]; linarith
    have e2 : 1 + a ^ (-κ) ≤ 2 * Y := by linarith
    have hapos : 0 ≤ a ^ (-κ) := by positivity
    calc C * (1 + 2 * A + 4 ^ κ * a ^ (-κ)) * (1 + a ^ (-κ)) * X ^ (-η)
        ≤ C * ((2 + 4 ^ κ) * (1 + A) * Y) * (2 * Y) * X ^ (-η) := by gcongr
      _ = D * (1 + A) * (P * P) * (X ^ (η / 4) * X ^ (η / 4) * X ^ (-η)) := by
          rw [hD, hY]; ring
      _ ≤ D * (1 + A) * Q * X ^ (-δ) := by gcongr
  calc ‖pushFourier F ξ‖ ≤ _ := hsplit
    _ ≤ 12 * N * X ^ (-δ) + D * (1 + A) * Q * X ^ (-δ) := add_le_add hbad' hgood
    _ ≤ (12 * N + D + 1) * (1 + A) * Q * X ^ (-δ) := by
        have : 12 * (N : ℝ) * X ^ (-δ) ≤ 12 * N * ((1 + A) * Q) * X ^ (-δ) := by
          have : 1 ≤ (1 + A) * Q := by nlinarith
          have hN : (0 : ℝ) ≤ 12 * N := by positivity
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hN this) hXδ.le
        nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 1 + A) (by linarith : (0 : ℝ) < Q)) hXδ]
    _ ≤ K * (1 + A) * Q * X ^ (-δ) := by gcongr

/-- **Global polynomial decay for every `G_p`, `1 ≤ deg p < k`, despite inflection points.**
Wiring proved: the cylinder cut (`pushFourier_le_of_deriv2_lower`, `N = k − 2`) fed with
`deriv2_Gk_lower` and `deriv_Gk_le`.  (Non-effectively this is also BB Thm 1.1 for `G_p ∘ A`.) -/
theorem polyDecay_Gk (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ) (p : ℤ[X])
    (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) : PolyDecay (Gk k p) := by
  obtain ⟨K, hK, δ, hδ, hcut⟩ := pushFourier_le_of_deriv2_lower hBB (k - 2)
  obtain ⟨Z, hZ, hlow⟩ := deriv2_Gk_lower k p h1 hk
  have hb := deriv_Gk_le k p hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc : (0 : ℝ) < ((2 : ℝ) * (k : ℝ) ^ (k + 1))⁻¹ := inv_pos.2 (mul_pos two_pos (pow_pos hk0 _))
  refine ⟨K * (1 + 4 * (hgt p : ℝ)) * (1 + ((2 : ℝ) * (k : ℝ) ^ (k + 1))⁻¹⁻¹) ^ K, δ, ?_, hδ,
    fun ξ hξ => hcut (Gk k p) (Set.Ioi 0) isOpen_Ioi window_sub_Ioi
      ((analyticOnNhd_Gk k p).contDiffOn isOpen_Ioi.uniqueDiffOn) _ (4 * (hgt p : ℝ)) hc
      (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2) Z hZ hlow ξ hξ⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

/-! ### Explicit: one computable `e` for all `p` and all bases

Index the polynomials by `ℕ` (`polyOfCode`, through `Encodable (List ℤ)`), normalise each `G_p`
into `[0, 1]` by the rational affine map `x ↦ (x + H)/(2H)`, `H = hgt p` (`Gfam`), and run the
all-bases derandomization of `ComputableNormalB` over the whole family
(`exists_computable_absNormal_family`).  Wall's rational affine invariance
(`isNormal_rat_mul_add`) undoes the normalisation. -/

/-- Coefficient list → polynomial `Σ_j l_j X^j`. -/
noncomputable def polyOfList (l : List ℤ) : ℤ[X] :=
  ∑ j ∈ Finset.range l.length, C (l.getD j 0) * X ^ j

/-- Index `i` → the polynomial with coefficient list `decode i` when it has `1 ≤ deg < k`, and
`X` otherwise (so every index carries a map with polynomial decay when `k ≥ 2`). -/
noncomputable def polyOfCode (k i : ℕ) : ℤ[X] :=
  match (Encodable.decode i : Option (List ℤ)) with
  | some l => if 1 ≤ (polyOfList l).natDegree ∧ (polyOfList l).natDegree < k then polyOfList l
      else X
  | none => X

theorem polyOfList_coeffs (p : ℤ[X]) :
    polyOfList ((List.range (p.natDegree + 1)).map p.coeff) = p := by
  unfold polyOfList
  rw [List.length_map, List.length_range]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  simp [List.getD_eq_getElem?_getD, hj]

/-- Every `p` with `1 ≤ deg p < k` has an index. -/
theorem exists_polyOfCode_eq (k : ℕ) (p : ℤ[X]) (h1 : 1 ≤ p.natDegree) (hk : p.natDegree < k) :
    ∃ i, polyOfCode k i = p := by
  refine ⟨Encodable.encode ((List.range (p.natDegree + 1)).map p.coeff), ?_⟩
  simp only [polyOfCode, Encodable.encodek, polyOfList_coeffs, if_pos (And.intro h1 hk)]

theorem polyOfCode_ne_zero (k i : ℕ) : polyOfCode k i ≠ 0 := by
  unfold polyOfCode
  split
  · split_ifs with h
    · intro h0; rw [h0] at h; simp at h
    · exact X_ne_zero
  · exact X_ne_zero

/-- The normalised family: `Gfam k i ω = (G_p(y) + H)/(2H) ∈ [0, 1]`, `p = polyOfCode k i`,
`H = hgt p`, `y = cantorReal ω`. -/
noncomputable def Gfam (k i : ℕ) (ω : ℕ → Bool) : ℝ :=
  (Gk k (polyOfCode k i) (cantorReal ω) + hgt (polyOfCode k i)) / (2 * hgt (polyOfCode k i))

theorem measurable_Gfam (k i : ℕ) : Measurable (Gfam k i) := by
  unfold Gfam Gk
  have h1 : Measurable fun ω => cantorReal ω ^ ((k : ℝ)⁻¹) :=
    CantorSelfSimilar.measurable_cantorReal.pow_const _
  have h2 := (Polynomial.continuous_aeval (R := ℤ) (A := ℝ) (polyOfCode k i)).measurable.comp h1
  exact (h2.add_const _).div_const _

/-- **Generic family derandomization** (`ComputableNormalB.exists_computable_absNormal` for
countably many maps at once).

Confidence 85%.  English proof: as in `exists_computable_absNormal`, with level-`n` bad events
over pairs `(i, b)` admitted when `i ≤ n` and `n ≥ n(i)`.  `level_bound_b` gives the per-`i`
level mass `49344·√(1 + Kc (c i) δ)/n²`, and `Kc C δ = C·K_δ` is linear in `C`, so with `K_δ`
hard-coded as a natural number the per-`i` constant `c₁(i) ≤ 49344(1 + c i·⌈K_δ⌉)` is primitive
recursive.  Choose `n(i) = 8 + 4·2^{i+3}c₁(i)` so `Σ_i Σ_{n ≥ n(i)} c₁(i)/n² ≤ 1/8`; the
combined bad test is primitive recursive in `(n, prefix)` and its tail is computably summable,
so `Derandomize.exists_primrec_avoid` applies.  Every `(i, b)` is tested at every level
`n ≥ max(n(i), i, b)`, so `normal_of_good_b` gives `IsNormal b (G i e)`. -/
theorem exists_computable_absNormal_family (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2)
    (A : ℕ → List Bool → ℝ) (hΨ : ∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊)
    (hA0 : ∀ i p, 0 ≤ A i p) (G : ℕ → (ℕ → Bool) → ℝ) (hGm : ∀ i, Measurable (G i))
    (hAG : ∀ i ω D, A i (Derandomize.pre ω D) ≤ G i ω ∧
      G i ω ≤ A i (Derandomize.pre ω D) + (1 / 2 : ℝ) ^ D)
    (c : ℕ → ℕ) (hc : Primrec c) {δ : ℝ} (hδ : 0 < δ)
    (hdec : ∀ i, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ ω, DecayAeNormal.ee (ξ * G i ω) ∂Derandomize.coins‖ ≤ c i * |ξ| ^ (-δ)) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ i b, 2 ≤ b → IsNormal b (G i e) := by
  sorry

/-- **Uniform, primitive recursive decay constants for the normalised family.**

Confidence 85%.  English proof: from `polyDecay_Gk`'s proof (the cut with `N = k − 2`,
`c = (2k^{k+1})^{-1}`, `A = 4H`): `‖pushFourier (Gk k p) ξ‖ ≤ K(1 + 4H)(1 + 2k^{k+1})^K|ξ|^{-δ}`
with `K, δ` depending only on `k`.  Normalising, `∫ e(ξ Gfam) = e(ξ/2)·pushFourier (Gk k p)
(ξ/(2H))` (`coins = coinMeasure`, same `e`), so with `δ' = min δ 1` the bound is
`≤ K(1 + 4H)(1 + 2k^{k+1})^K (2H) |ξ|^{-δ'}` for `|ξ| ≥ 1` and `≤ 1` otherwise.  `H` is bounded by
`1 + Σ |l_j|` over the decoded list (or `1` for the default `X`), primitive recursive in `i`
(`Primcodable (List ℤ)`), so `c i := K(1 + 4B_i)(1 + 2k^{k+1})^K·2B_i + 1` works. -/
theorem decay_Gfam (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℕ → ℕ, Primrec c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ ω, DecayAeNormal.ee (ξ * Gfam k i ω) ∂Derandomize.coins‖ ≤ c i * |ξ| ^ (-δ) := by
  sorry

/-- **Computable lower approximations of the normalised family with exact primitive recursive
floors.**

Confidence 85%.  English proof: a length-`D` prefix fixes `y = cantorReal ω` up to an unknown
tail in `[0, 4^{-D}/6]`; `|Gfam'| ≤ 4H/(2H) = 2` on the window (`deriv_Gk_le`), so `Gfam`
varies by `≤ 4^{-D}/3` over the cylinder.  Compute a rational `R` with
`|R − Gfam(y_lo)| ≤ 2^{-D}/6`: each `y_lo^{j/k}` is `⌊(Y^j 2^{kM})^{1/k}⌋/2^M` up to `2^{-M}`
(integer `k`-th root by bounded search, primitive recursive), `M = D + ⌈log₂ H⌉ + 3`.  Put
`A = max 0 (R − 2^{-D}/2)` (a rational, so `⌊A bᵐ⌋` is primitive recursive); since
`0 ≤ Gfam`, both `A ≤ Gfam ω` and `Gfam ω ≤ A + 2^{-D}` hold for every `ω` extending the prefix. -/
theorem approx_Gfam (k : ℕ) (hk : 2 ≤ k) :
    ∃ (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ) (A : ℕ → List Bool → ℝ),
      (Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
      (∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊) ∧ (∀ i p, 0 ≤ A i p) ∧
      ∀ i ω D, A i (Derandomize.pre ω D) ≤ Gfam k i ω ∧
        Gfam k i ω ≤ A i (Derandomize.pre ω D) + (1 / 2 : ℝ) ^ D := by
  sorry

/-- **Simultaneous derandomization: one computable `e` making every `G_p(y)`, `1 ≤ deg p < k`,
normal in every base.**  Wiring proved: `exists_computable_absNormal_family` on the normalised
family (`approx_Gfam`, `decay_Gfam`, `measurable_Gfam`), then every `p` has an index
(`exists_polyOfCode_eq`) and Wall's rational affine invariance undoes the normalisation.  For
`k ≤ 1` the conclusion is vacuous. -/
theorem exists_computable_isAbsNormal_Gk (hBB : BakerBanajiUniformQuarterCantor) (k : ℕ) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ p : ℤ[X], 1 ≤ p.natDegree → p.natDegree < k →
      IsAbsNormal (Gk k p (cantorReal e)) := by
  by_cases hk : 2 ≤ k
  swap
  · exact ⟨fun _ => false, Computable.const _, fun p h1 h2 => absurd (h1.trans_lt h2) (by omega)⟩
  obtain ⟨Ψ, A, hΨp, hΨ, hA0, hAG⟩ := approx_Gfam k hk
  obtain ⟨c, hc, δ, hδ, hdec⟩ := decay_Gfam hBB k hk
  obtain ⟨e, hce, hn⟩ := exists_computable_absNormal_family Ψ hΨp A hΨ hA0 (Gfam k)
    (measurable_Gfam k) hAG c hc hδ hdec
  refine ⟨e, hce, fun p h1 h2 b hb => ?_⟩
  obtain ⟨i, hi⟩ := exists_polyOfCode_eq k p h1 h2
  have hH : (1 : ℝ) ≤ hgt p := by exact_mod_cast one_le_hgt (hi ▸ polyOfCode_ne_zero k i)
  have hq : ((2 * hgt p : ℕ) : ℚ) ≠ 0 := by
    have : 1 ≤ hgt p := by exact_mod_cast hH
    exact_mod_cast (show 2 * hgt p ≠ 0 by omega)
  have h := isNormal_rat_mul_add b hb _ ((2 * hgt p : ℕ) : ℚ) (-(hgt p : ℚ)) hq (hn i b hb)
  convert h using 1
  simp only [Gfam, hi]
  push_cast
  field_simp
  ring

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
