/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.WallRational
import NormalNumbers.Bridge
import NormalNumbers.OccurrenceCountEquiv
import NormalNumbers.DecayAeNormal
import NormalNumbers.SqrtFloor
import Mathlib.Computability.Partrec
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

/-!
# An explicit normal `x` with `x²` not normal; deterministic `y` with `1/y` normal

Audit of open-problem sweep rows 3 and 5 (`docs/OPEN-PROBLEMS-SWEEP-2026-10-02.md`); verdict in
`docs/EXPLICIT-SQUARE-NONNORMAL-AUDIT-2026-10-02.md`.

* **Row 3** (Manai 2506.15422v5 §1; Manai 2508.09319v4, open problem after Def. `def:deg`):
  explicitly determine a normal `x` with `x²` not normal.  Existence is Manai 2609.24665v1
  `thm:2` (measure-theoretic).
* **Row 5** (Bergelson–Downarowicz 2506.12929v1, "Some natural open problems" items 2, 3):
  is `1/y` deterministic for deterministic `y`?  Is there a normal number with deterministic
  reciprocal?

## The simplification that makes row 3 tractable

Row 3 asks only that `x² = y` be **non-normal**, not deterministic.  So `y` may range over a
**positive-dimension** self-similar set, where Baker–Banaji polynomial Fourier decay of `C²`
images is literature.  We use the quarter-Cantor set: binary digit `0` is `1`, even digits
`2k+2` are free, odd digits are `0`.  Every point of it misses the block `11`, so it is
non-normal **structurally** (`not_isNormal_cantorReal`, proved) and no frequency defect has to
survive the derandomization.  `x := √y`; then `x² = y` (`sq_sqrt_cantorReal`).

Explicitness is the Lean condition `Computable e` on the coin sequence `e : ℕ → Bool` coding
`y = cantorReal e`, the Becher–Figueira / Becher–Lew Deveali (2607.06773 `thm:3`) standard.

## Row 5 does not share the easy lemma

A deterministic number has Hausdorff-dimension-zero orbit statistics, so row 5 is forced onto a
dimension-zero support, where polynomial Fourier decay is impossible
(`not_polyDecay_sparse_of_densityZero`) and even logarithmic decay needs `#S ∩ [0,n) ≳ log n`
(`not_logDecay_sparse_of_littleLog`).  Its hard lemma `inv_logDecay_squares` is genuinely open.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.ExplicitSquare

/-! ## The quarter-Cantor digits -/

/-- Binary digits (digit `i` weighs `2^{-(i+1)}`) of the quarter-Cantor point coded by `e`:
digit `0` is `1` (so the point lies in `[1/2, 2/3]`), digit `2k+2` is `e k`, odd digits are
`0`. -/
def cantorDigits (e : ℕ → Bool) (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i % 2 = 0 then (if e (i / 2 - 1) then 1 else 0) else 0

/-- The quarter-Cantor point coded by `e`. -/
noncomputable def cantorReal (e : ℕ → Bool) : ℝ := realOfDigits 2 (cantorDigits e)

/-- Non-vacuity anchor: the all-ones code puts `1` at digit `2` and `0` at digit `3`. -/
theorem cantorDigits_anchor :
    cantorDigits (fun _ => true) 2 = 1 ∧ cantorDigits (fun _ => true) 3 = 0 := by
  decide

theorem cantorDigits_lt (e : ℕ → Bool) (i : ℕ) : cantorDigits e i < 2 := by
  unfold cantorDigits; split_ifs <;> norm_num

theorem cantorDigits_odd (e : ℕ → Bool) {i : ℕ} (hi : i % 2 = 1) : cantorDigits e i = 0 := by
  have h0 : i ≠ 0 := by omega
  simp [cantorDigits, h0, hi]

theorem cantorDigits_proper (e : ℕ → Bool) : ProperDigits 2 (cantorDigits e) := by
  intro N
  refine ⟨2 * N + 1, by omega, ?_⟩
  rw [cantorDigits_odd e (by omega)]
  norm_num

theorem digitOf_cantorReal (e : ℕ → Bool) : digitOf 2 (cantorReal e) = cantorDigits e :=
  digitOf_realOfDigits 2 le_rfl _ (cantorDigits_lt e) (cantorDigits_proper e)

theorem cantorReal_mem_Ico (e : ℕ → Bool) : cantorReal e ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico 2 le_rfl _ (cantorDigits_lt e) (cantorDigits_proper e)

/-- The block `11` never occurs: one of two adjacent positions is odd. -/
theorem count_one_one_eq_zero (e : ℕ → Bool) (n : ℕ) :
    countOccurrences [1, 1] ((List.range n).map (cantorDigits e)) = 0 := by
  rw [countOccurrences_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i - ⟨-, h⟩
  have h1 : cantorDigits e i = 1 ∧ cantorDigits e (i + 1) = 1 := by
    simp [List.range'] at h
    exact ⟨h.1.symm, h.2.symm⟩
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have := cantorDigits_odd e (i := i + 1) (by omega)
    omega
  · have := cantorDigits_odd e hi
    omega

/-- **Every quarter-Cantor point is non-normal in base 2** (structurally: no `11` block). -/
theorem not_isNormal_cantorReal (e : ℕ → Bool) : ¬ IsNormal 2 (cantorReal e) := by
  intro h
  have hmem := cantorReal_mem_Ico e
  rw [Set.mem_Ico] at hmem
  unfold IsNormal at h
  rw [Int.fract_eq_self.mpr hmem, digitOf_cantorReal] at h
  have ht := h [1, 1] (by simp) (by intro d hd; simp at hd; omega)
  simp only [count_one_one_eq_zero, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

theorem sq_sqrt_cantorReal (e : ℕ → Bool) : Real.sqrt (cantorReal e) ^ 2 = cantorReal e :=
  Real.sq_sqrt (cantorReal_mem_Ico e).1

/-- `x² = y` is non-normal for every `x = √y` with `y` in the quarter-Cantor set. -/
theorem not_isNormal_sq_sqrt_cantorReal (e : ℕ → Bool) :
    ¬ IsNormal 2 (Real.sqrt (cantorReal e) ^ 2) := by
  rw [sq_sqrt_cantorReal]; exact not_isNormal_cantorReal e

/-- **Affine sibling control** (Wall rational): no rational affine image of a quarter-Cantor
point is normal.  So any argument making `F(y)` normal for `y` in this set must use `F'' ≠ 0`;
the same mechanism run on `F(t) = q t + r` must fail, and does (`not_polyDecay_rat_affine`). -/
theorem not_isNormal_rat_affine_cantorReal (e : ℕ → Bool) (q r : ℚ) (hq : q ≠ 0) :
    ¬ IsNormal 2 ((q : ℝ) * cantorReal e + r) := by
  intro h
  have h' := isNormal_rat_mul_add 2 le_rfl _ q⁻¹ (-(r / q)) (inv_ne_zero hq) h
  apply not_isNormal_cantorReal e
  convert h' using 1
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp
  ring

/-! ## The coin measure and the pushforward Fourier transform -/

/-- Fair coins on the free digits. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure; infer_instance

/-- Fourier transform of `F_* μ`, `μ` the law of `cantorReal` under `coinMeasure`. -/
noncomputable def pushFourier (F : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ ω, Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (cantorReal ω) : ℝ) : ℂ)) ∂coinMeasure

/-- Polynomial Fourier decay of `F_* μ`. -/
def PolyDecay (F : ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖pushFourier F ξ‖ ≤ C * |ξ| ^ (-δ)

/-- **Cited input: Baker–Banaji, *Polynomial Fourier decay for fractal measures and their
pushforwards*, Corollary 1.5** (arXiv 2401.01241), in the form quoted as Manai 2609.24665v1
`thm:BB`: for a non-atomic self-similar probability measure `μ` on `[0,1]` and `F` that is `C²`
on a neighbourhood of `[0,1]` with `F'' ≠ 0` on `[0,1]`, `|∫ e(ξF) dμ| ≤ C|ξ|^{-δ}`.  The
homogeneous case (ours) is also Mosquera–Shmerkin 2018 (Ann. Acad. Sci. Fenn. 43).

**Faithful-or-weaker.**  This is the specialisation to the law of `cantorReal`, which is
self-similar (IFS `t ↦ 1/2 + (t − 1/2)/4`, `t ↦ 1/2 + (t − 1/2)/4 + 1/8`, weights `1/2`),
non-atomic, and supported in `[1/2, 2/3]`; the window `[1/2, 1]` is `[0,1]` after the rational
affine change `t ↦ 2t − 1`, which preserves self-similarity and the hypotheses on `F`. -/
def BakerBanajiQuarterCantor : Prop :=
  ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 F U →
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t ≠ 0) → PolyDecay F

/-- `√` meets the Baker–Banaji hypotheses on `[1/2, 1]`: smooth on `(0, ∞)`, and
`(√)'' t = −t^{−3/2}/4 ≠ 0`.

Confidence 99%.  Proof: `U = Set.Ioi 0`; `Real.contDiffOn_sqrt`-style smoothness off `0`;
`deriv √ =ᶠ fun s => 1/(2√s)` near `t > 0` (`Real.hasDerivAt_sqrt`), so
`deriv (deriv √) t = −1/(4 t √t) ≠ 0`. -/
theorem sqrt_bakerBanaji_hyp :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (1 / 2 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ 2 Real.sqrt U ∧
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv Real.sqrt) t ≠ 0 := by
  refine ⟨Set.Ioi 0, isOpen_Ioi, fun t ht => lt_of_lt_of_le (by norm_num) ht.1, ?_, ?_⟩
  · intro x hx
    exact (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hev : deriv Real.sqrt =ᶠ[nhds t] fun s => 1 / (2 * Real.sqrt s) := by
      filter_upwards [lt_mem_nhds ht0] with s hs
      exact (Real.hasDerivAt_sqrt (ne_of_gt hs)).deriv
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun s => 2 * Real.sqrt s) (2 * (1 / (2 * Real.sqrt t))) t :=
      (Real.hasDerivAt_sqrt (ne_of_gt ht0)).const_mul 2
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have h2 : HasDerivAt (fun s => (2 * Real.sqrt s)⁻¹) _ t := h1.inv (by positivity)
    have : (fun s => 1 / (2 * Real.sqrt s)) = fun s => (2 * Real.sqrt s)⁻¹ := by
      funext s; simp
    rw [this, h2.deriv]
    have : 0 < 2 * (1 / (2 * Real.sqrt t)) / (2 * Real.sqrt t) ^ 2 := by positivity
    rw [neg_div]; exact neg_ne_zero.2 this.ne'

/-! ## Step 1: decay ⇒ almost-sure normality (Manai 2609.24665 `lem:decaynormal`) -/

/-- **Polynomial decay ⇒ a.s. normality.**

Confidence 97%.  Proof (Manai 2609.24665 `lem:decaynormal`, base 2 only): for `h ≠ 0`,
`∫ |A_N(h)|² = N⁻² Σ_{m,n<N} \hat ν(h(2ⁿ − 2ᵐ)) ≤ 1/N + 2C|h|^{-δ}N⁻² Σ_{m<n} (2ⁿ−2ᵐ)^{-δ}
≤ C₀/N`, where `A_N(h; x) = fourierMean (orbit 2 x) h N`.  Chebyshev + Borel–Cantelli along
`N = j²`, then interpolation, gives `A_N(h) → 0` a.s.; intersect over `h`, then
`equidistributed_of_weyl` and `isNormal_iff_equidistributed_orbit`. -/
theorem ae_isNormal_of_polyDecay (F : ℝ → ℝ) (hF : Measurable F) (hd : PolyDecay F) :
    ∀ᵐ ω ∂coinMeasure, IsNormal 2 (F (cantorReal ω)) := by
  have hc : Measurable cantorReal := by
    unfold cantorReal realOfDigits
    refine Measurable.tsum fun i => Measurable.div_const ?_ _
    refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
    exact (measurable_of_countable (fun b : Bool =>
      if i = 0 then 1 else if i % 2 = 0 then (if b then 1 else 0) else 0)).comp
      (measurable_pi_apply (i / 2 - 1))
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  exact DecayAeNormal.ae_isNormal_two_of_decay coinMeasure _ (hF.comp hc) hC hδ hdec

/-- **The mechanism visibly fails on the affine sibling**: no rational affine `F` has
polynomial decay, because decay would make a.e. `F(y)` normal
(`ae_isNormal_of_polyDecay`), contradicting `not_isNormal_rat_affine_cantorReal`. -/
theorem not_polyDecay_rat_affine (q r : ℚ) (hq : q ≠ 0) :
    ¬ PolyDecay (fun t => (q : ℝ) * t + r) := by
  intro hd
  have hmeas : Measurable (fun t : ℝ => (q : ℝ) * t + r) := by fun_prop
  obtain ⟨ω, hω⟩ := (ae_isNormal_of_polyDecay _ hmeas hd).exists
  exact not_isNormal_rat_affine_cantorReal ω q r hq hω

/-- **Non-explicit existence** (a structural-non-normality proof of the `√` case of Manai
2609.24665 `thm:2`): some quarter-Cantor `y` has `√y` normal, while `(√y)² = y` is not. -/
theorem exists_sqrt_normal_sq_not_normal (hBB : BakerBanajiQuarterCantor) :
    ∃ e : ℕ → Bool, IsNormal 2 (Real.sqrt (cantorReal e)) ∧
      ¬ IsNormal 2 (Real.sqrt (cantorReal e) ^ 2) := by
  obtain ⟨U, hU, hsub, hC2, hF''⟩ := sqrt_bakerBanaji_hyp
  obtain ⟨e, he⟩ :=
    (ae_isNormal_of_polyDecay Real.sqrt Real.continuous_sqrt.measurable
      (hBB _ U hU hsub hC2 hF'')).exists
  exact ⟨e, he, not_isNormal_sq_sqrt_cantorReal e⟩

/-! ## Step 2: derandomization (the new piece) -/

/-- **Derandomization: decay ⇒ a computable witness.**  The hardest step of row 3.

Confidence 75%.  English proof (Becher–Figueira 2002 computable Sierpiński, as adapted in
Becher–Lew Deveali 2607.06773 Algorithm 1 / `lemma:positive`): fix rationals `C' ≥ C`,
`0 < δ' ≤ δ` (they exist, so the algorithm below is one fixed algorithm even if Baker–Banaji's
constants are ineffective).  Bad sets
`Λ_{h,j} = {ω : |A_{j²}(h; √(cantorReal ω))| > j^{-1/4}}`, `1 ≤ |h| ≤ log j`, have
`coinMeasure Λ_{h,j} ≤ C₀ j^{-3/2}` by Chebyshev and the Step-1 second moment, with `C₀`
explicit in `C', δ'`; the tails `u_t = Σ_{j ≥ t} …` are explicit and `→ 0`.  Each `Λ_{h,j}` is
approximated within `2^{-j}` in measure by a finite union of depth-`K_j` coin cylinders
(`K_j ≈ 2j² + log j + j`, since moving `ω` beyond depth `K` moves `y` by `≤ 4^{-K}` and
`A_N` by `≤ 2π|h|2^N 4^{-K}`), and cylinder masses are dyadic rationals; so the greedy
halving of BLD Algorithm 1 is a computable choice of `e k` keeping the invariant
`μ(I_i \ Δ) > 0`.  The limit point avoids every `Λ_{h,j}` for `j` large, hence
`A_{j²}(h) → 0`, hence `√y` is normal (Weyl, as in Step 1).  Unlike BLD, no Korobov residue
count is needed: Step 1's decay is uniform in the frequency. -/
theorem exists_computable_isNormal_sqrt_of_polyDecay (hd : PolyDecay Real.sqrt) :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (Real.sqrt (cantorReal e)) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  have hc : Measurable cantorReal := by
    unfold cantorReal realOfDigits
    refine Measurable.tsum fun i => Measurable.div_const ?_ _
    refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
    exact (measurable_of_countable (fun b : Bool =>
      if i = 0 then 1 else if i % 2 = 0 then (if b then 1 else 0) else 0)).comp
      (measurable_pi_apply (i / 2 - 1))
  refine ComputableNormal.exists_computable_normal_of_digits SqrtFloor.sqrtPhi
    (fun ω => Real.sqrt (cantorReal ω)) (Real.continuous_sqrt.measurable.comp hc)
    (fun ω => Real.sqrt_nonneg _) hC hδ (fun ξ hξ => hdec ξ hξ) SqrtFloor.primrec_sqrtPhi
    fun ω m => SqrtFloor.floor_sqrt_digits _ (cantorDigits_lt ω) (cantorDigits_proper ω) m _
      fun k hk => ?_
  unfold SqrtFloor.cdL cantorDigits Derandomize.pre
  split_ifs with h0 h2 h3 h3 <;> try rfl
  all_goals
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at *
    simp_all

/-! ## The row-3 target -/

/-- **Row 3 (target): an explicit normal `x` with `x²` not normal**, `x = √y`,
`y = cantorReal e` for a **computable** coin sequence `e`.  Wired from the cited
Baker–Banaji input and the two named steps. -/
theorem exists_computable_normal_sq_not_normal (hBB : BakerBanajiQuarterCantor) :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (Real.sqrt (cantorReal e)) ∧
      ¬ IsNormal 2 (Real.sqrt (cantorReal e) ^ 2) := by
  obtain ⟨U, hU, hsub, hC2, hF''⟩ := sqrt_bakerBanaji_hyp
  obtain ⟨e, hc, hn⟩ :=
    exists_computable_isNormal_sqrt_of_polyDecay (hBB _ U hU hsub hC2 hF'')
  exact ⟨e, hc, hn, not_isNormal_sq_sqrt_cantorReal e⟩

/-! ## Row 5: deterministic `y` with `1/y` normal -/

/-- Binary digits of the sparse-Cantor point: digit `0` is `1`, digit `i ∈ S` (`i ≥ 1`) is
`ω i`, all others `0` (Becher–Lew Deveali 2607.06773 Def. "Sparse Cantor set", with the
leading digit pinned so the point lies in `[1/2, 1)`). -/
noncomputable def sparseDigits (S : Set ℕ) (ω : ℕ → Bool) (i : ℕ) : ℕ := by
  classical exact if i = 0 then 1 else if i ∈ S ∧ ω i = true then 1 else 0

noncomputable def sparseReal (S : Set ℕ) (ω : ℕ → Bool) : ℝ := realOfDigits 2 (sparseDigits S ω)

/-- Fourier transform of `F_* μ_S`, `μ_S` the law of `sparseReal S` under fair coins. -/
noncomputable def sparseFourier (S : Set ℕ) (F : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ ω, Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (sparseReal S ω) : ℝ) : ℂ)) ∂coinMeasure

/-- `#(S ∩ [0, n))`. -/
noncomputable def sCount (S : Set ℕ) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter (· ∈ S)).card

/-- Base-2 frequency of the digit `1` is `0`.  **Sufficient for Bergelson–Downarowicz
determinism**: every quasi-generic measure of the digit sequence then gives the cylinder `[1]`
mass `0`, so it is the point mass on `0^∞`, of entropy `0`.  (Determinism itself — zero entropy
of all quasi-generic measures — is not formalized; this stronger property is what the target
asks for.) -/
def OneFreqZero (y : ℝ) : Prop :=
  Tendsto (fun n => (countOccurrences [1] ((List.range n).map (digitOf 2 (Int.fract y))) : ℝ) / n)
    atTop (𝓝 0)

/-- **Barrier 1: dimension zero kills polynomial decay.**  If `S` has density zero, no `C¹` map
with nonvanishing derivative on `[1/2, 1]` pushes `μ_S` to a measure with polynomial Fourier
decay.  So the Baker–Banaji route of row 3 is **closed** for row 5, whose `y` must be
deterministic and hence lives on a dimension-zero set.

Confidence 90%.  Proof: `|\hat ν(ξ)| ≤ C|ξ|^{-δ}` gives finite `s`-energy for `s < min(2δ, 1)`,
so (Frostman) `ν` gives mass `0` to every set of Hausdorff dimension `< s`; but `ν = F_*μ_S`
is carried by `F(C(S))`, and `F` is Lipschitz on `[1/2,1]`, so
`dim_H F(C(S)) ≤ dim_H C(S) = liminf sCount S n / n = 0`. -/
theorem not_polyDecay_sparse_of_densityZero (S : Set ℕ)
    (hS : Tendsto (fun n => (sCount S n : ℝ) / n) atTop (𝓝 0))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hF' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv F t ≠ 0) :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ξ : ℝ, ξ ≠ 0 → ‖sparseFourier S F ξ‖ ≤ C * |ξ| ^ (-δ) := by
  sorry

/-- **Barrier 2: a density threshold for logarithmic decay.**  If `sCount S n = o(log n)`
then no uniform decay `(log|ξ|)^{-η}`, `η > 0`, holds for any `C¹` `F` with `F' ≠ 0` on
`[1/2, 1]`.  So the Davenport–Erdős–LeVeque route needs `sCount S n ≳ log n`; powers of two
(`log₂ n`) sit on the edge and factorials (`log n / log log n`) are below it.

Confidence 80%.  Proof: with a Fejér kernel, `(2R)⁻¹∫_{|ξ|≤R} |\hat ν|² ≳ Σ_I ν(I)²` over
intervals of length `1/R`; at `R = 2ⁿ` the `2^{sCount S n}` equal-mass depth-`n` cylinders map
(`F` bi-Lipschitz) to intervals meeting `O(1)` of them, so the right side is
`≳ 2^{-sCount S n} ≥ n^{-ε}`, while uniform decay makes the left side
`≲ 2^{-n}R₀ + C²(n log 2 − 1)^{-2η}`; take `ε < 2η`. -/
theorem not_logDecay_sparse_of_littleLog (S : Set ℕ)
    (hS : ∀ ε > 0, ∀ᶠ n in atTop, (sCount S n : ℝ) ≤ ε * Real.logb 2 n)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hF' : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv F t ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    ¬ ∃ C : ℝ, 0 < C ∧
      ∀ ξ : ℝ, 2 ≤ |ξ| → ‖sparseFourier S F ξ‖ ≤ C * (Real.log |ξ|) ^ (-η) := by
  sorry

/-- **Davenport–Erdős–LeVeque step**: logarithmic decay at any positive rate suffices for
almost-sure normality.

Confidence 92%.  Proof: as `ae_isNormal_of_polyDecay`, but `\hat ν(h(2ⁿ−2ᵐ)) ≤ C((n−1)log 2)^{-η}`
gives `∫|A_N(h)|² ≤ 1/N + 2C' N⁻² Σ_{n<N} n^{1-η} = O(N^{-η})`, so
`Σ_N N⁻¹ ∫|A_N(h)|² < ∞` and the Davenport–Erdős–LeVeque theorem (LeVeque, *Fundamentals of
Number Theory*; used in BLD 2607.06773) gives `A_N(h) → 0` a.s. -/
theorem ae_isNormal_of_logDecay (S : Set ℕ) (F : ℝ → ℝ) (hF : Measurable F) {C η : ℝ}
    (hC : 0 < C) (hη : 0 < η)
    (hd : ∀ ξ : ℝ, 2 ≤ |ξ| → ‖sparseFourier S F ξ‖ ≤ C * (Real.log |ξ|) ^ (-η)) :
    ∀ᵐ ω ∂coinMeasure, IsNormal 2 (F (sparseReal S ω)) := by
  sorry

/-- The squares. -/
def squares : Set ℕ := {i | IsSquare i}

/-- Every point of the squares-Cantor set has digit-`1` frequency `0`
(`#squares ∩ [0,n) ≤ √n + 1`).  Confidence 98%; routine counting through
`digitOf_realOfDigits` (the digits are proper: non-squares are `0`). -/
theorem oneFreqZero_sparseReal_squares (ω : ℕ → Bool) : OneFreqZero (sparseReal squares ω) := by
  sorry

theorem sparseReal_pos (S : Set ℕ) (ω : ℕ → Bool) : 0 < sparseReal S ω := by
  sorry

/-- **The open row-5 lemma: curved logarithmic decay on a dimension-zero support.**
`1/y` pushes the squares-Cantor measure to one with `(log|ξ|)^{-η}` decay.

Confidence true 70%; provable by known methods 20%.  Heuristic: at frequency `2ⁿ`, writing
`y = a + 2^{-k}t`, `1/y ≈ 1/a − 2^{-k}t/a² + 2^{-2k}t²/a³`; the free digits in `[n/2, n]`
(about `0.3√n` squares, well above Barrier 2's `log n`) enter through the cylinder-dependent
coefficient `1/a²`, which the curvature spreads off the `2`-adic resonances that keep
`\hat μ_S(2ⁿ)` from decaying.  Manai 2606.08325 proves the forward analogue for `X^d`
(exact multilinear digit algebra) and says `√`/analytic maps are beyond current methods. -/
theorem inv_logDecay_squares : ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
    ∀ ξ : ℝ, 2 ≤ |ξ| → ‖sparseFourier squares (fun y => 1 / y) ξ‖ ≤ C * (Real.log |ξ|) ^ (-η) := by
  sorry

/-- **Row-5 wiring**: the open decay lemma gives a deterministic `y` with `1/y` normal. -/
theorem exists_inv_normal_of_logDecay
    (hd : ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ ξ : ℝ, 2 ≤ |ξ| →
      ‖sparseFourier squares (fun y => 1 / y) ξ‖ ≤ C * (Real.log |ξ|) ^ (-η)) :
    ∃ y : ℝ, 0 < y ∧ OneFreqZero y ∧ IsNormal 2 (1 / y) := by
  obtain ⟨C, η, hC, hη, hdec⟩ := hd
  have hmeas : Measurable (fun y : ℝ => 1 / y) := by fun_prop
  obtain ⟨ω, hω⟩ := (ae_isNormal_of_logDecay squares _ hmeas hC hη hdec).exists
  exact ⟨sparseReal squares ω, sparseReal_pos _ ω, oneFreqZero_sparseReal_squares ω, hω⟩

/-- **Row 5 (target)**: a deterministic (indeed digit-`1`-frequency-zero) `y > 0` whose
reciprocal is normal.  Answers Bergelson–Downarowicz Q2 (no) and Q3 (yes) at once.

Confidence true 85%; provable by known methods 15%.  Route: `exists_inv_normal_of_logDecay`
with `S = squares`; the open input is `inv_logDecay_squares`. -/
theorem exists_oneFreqZero_inv_normal : ∃ y : ℝ, 0 < y ∧ OneFreqZero y ∧ IsNormal 2 (1 / y) :=
  exists_inv_normal_of_logDecay inv_logDecay_squares

end NormalNumbers.ExplicitSquare
