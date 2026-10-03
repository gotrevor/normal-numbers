/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtCantorAbs
import NormalNumbers.CantorSelfSimilar
import NormalNumbers.ExplicitOmegaK

/-!
# Bugeaud Problems 10.17 / 10.18 (Rivoal): computable `ξ` normal with `1/ξ` not normal

Audit: `docs/BAD-NORMAL-AUDIT-2026-10-03.md` §B (sweep `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` §4).

**Target.**  Bugeaud, *Distribution modulo one and Diophantine approximation* (2012), Ch. 10:
"Problem 10.17.  Let `b ≥ 2` be an integer.  To give an explicit example of a positive real number
`ξ` which is simply normal (resp., normal) to base `b` and for which `1/ξ` is not simply normal
(resp., not normal) to base `b`.  Problem 10.18.  To give an explicit example of a positive real
number `ξ` which is absolutely normal and for which `1/ξ` does not share this property."
Also Bergelson–Downarowicz 2506.12929 §8.6 Q1 ("Is the reciprocal of a normal number always
normal?").  **Existence** (non-constructive): Manai 2609.24665 Thm 1.2 (`thm:2`), whose proof sends
a.e. point of a non-normal self-similar measure through a local inverse of a non-affine `C²` map.

**Mechanism** (the `ExplicitSquare` row-3 pipeline with `F = 1/t` in place of `√`): `F(t) = 1/t`
is `C²` on `(0, ∞)` with `F'' = 2/t³ ∈ [2, 16]` on `[1/2, 1]`, so Baker–Banaji gives polynomial
decay of the law of `1/cantorReal ω`; the all-bases derandomizer gives a computable `e` with
`ξ = 1/cantorReal e` absolutely normal, while `1/ξ = cantorReal e` never contains the block `11`.

* `exists_computable_absNormal_recip_not_normal`: 10.18, and 10.17 (normal version) for `b = 2`,
  on the refereed `BakerBanajiQuarterCantor` only.
* `exists_computable_absNormal_recip_not_simplyNormal`: 10.17 in both versions for **every**
  `b ≥ 2`, via the sparse base-`b` Cantor point `ySparse b e` (digit `0` has frequency `≥ 2/3`),
  on the cited `Literature.BakerBanajiSparse` (same Baker–Banaji corollary, another self-similar
  measure; referee pending).

⚠️ Same seam as `ExplicitSquare` / `ExplicitPQ`: corollary-sized, harvest it inside a note.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.ReciprocalNormal

open ExplicitSquare Derandomize SqrtCantorAbs ExplicitOmegaK

/-! ## `1/t` meets the Baker–Banaji hypotheses -/

/-- `t ↦ 1/t` is `C²` on `(0, ∞)` and has `(1/t)'' = 2/t³ ≠ 0` on `[1/2, 1]`.

Proved: `one_div` turns it into `Inv.inv`; `contDiffAt_inv` off `0`; `deriv_inv'` gives
`deriv (·⁻¹) = fun x => -(x²)⁻¹`, whose derivative at `t ≠ 0` is `2t/(t²)² ≠ 0`
(`HasDerivAt.inv` of `hasDerivAt_pow`, negated). -/
theorem inv_bakerBanaji_hyp :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (1 / 2 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ 2 (fun t : ℝ => 1 / t) U ∧
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv fun t : ℝ => 1 / t) t ≠ 0 := by
  have hf : (fun t : ℝ => 1 / t) = fun t => t⁻¹ := funext fun t => one_div t
  refine ⟨Set.Ioi 0, isOpen_Ioi, fun t ht => lt_of_lt_of_le (by norm_num) ht.1, ?_, ?_⟩
  · intro x hx
    rw [hf]
    exact (contDiffAt_inv ℝ (ne_of_gt (Set.mem_Ioi.1 hx))).contDiffWithinAt
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
    rw [hf, deriv_inv']
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun x : ℝ => -(x ^ 2)⁻¹) (-(-(2 * t) / (t ^ 2) ^ 2)) t :=
      (h1.inv (pow_ne_zero 2 ht0)).neg
    rw [h2.deriv]
    have : 0 < 2 * t / (t ^ 2) ^ 2 := by
      have htp : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      positivity
    simpa [neg_div, neg_neg] using this.ne'

/-- **Polynomial decay of the law of `1/cantorReal`**, from the refereed Baker–Banaji input. -/
theorem polyDecay_inv (hBB : BakerBanajiQuarterCantor) : PolyDecay fun t : ℝ => 1 / t := by
  obtain ⟨U, hU, hsub, hC2, hF''⟩ := inv_bakerBanaji_hyp
  exact hBB _ U hU hsub hC2 hF''

/-! ## Exact lower approximations of `1/cantorReal` -/

/-- Lower approximation of `1/y` from a prefix `p` of length `D`: `3/2` for `D ≤ 1`, else
`4^D/(Y + 1)` with `Y = ⌊y·4^D⌋` (`Yp`, read from `p`). -/
noncomputable def Ainv (p : List Bool) : ℝ :=
  if p.length ≤ 1 then 3 / 2 else (4 : ℝ) ^ p.length / ((Yp p : ℝ) + 1)

/-- Its base-`b` floors. -/
def PsiInv (b m : ℕ) (p : List Bool) : ℕ :=
  if p.length ≤ 1 then 3 * b ^ m / 2 else b ^ m * 4 ^ p.length / (Yp p + 1)

theorem Ainv_nonneg (p : List Bool) : 0 ≤ Ainv p := by
  unfold Ainv; split_ifs <;> positivity

/-- **Leaf: exact floors.**  Confidence 92%.  Proof: `⌊(3/2)·bᵐ⌋₊ = 3bᵐ/2` and
`⌊4^D bᵐ/(Y+1)⌋₊ = bᵐ4^D/(Y+1)` by `Nat.floor_div_eq_div` after `push_cast`. -/
theorem PsiInv_eq (b m : ℕ) (p : List Bool) : PsiInv b m p = ⌊Ainv p * (b : ℝ) ^ m⌋₊ := by
  sorry

/-- **Leaf: primitive recursive floors.**  Confidence 92%.  Proof: `primrec_Yp`, `primrec_pow`,
`nat_mul`, `nat_div`, `Primrec.ite` on `p.length ≤ 1` (as in `SqrtCantorAbs.primrec_Psi`). -/
theorem primrec_PsiInv : Primrec fun x : ℕ × ℕ × List Bool => PsiInv x.1 x.2.1 x.2.2 := by
  sorry

/-- **Leaf: the sandwich `Ainv (pre ω D) ≤ 1/y ≤ Ainv (pre ω D) + 2^{-D}`**, `y = cantorReal ω`.

Confidence 88%.  Proof: `y ∈ [1/2, 2/3]` (digit `0` is `1`; the free digits sum to at most
`Σ_k 2^{-(2k+3)} = 1/6`), so `1/y ∈ [3/2, 2]`, which settles `D ≤ 1` (`3/2 + 1/2 = 2`).  For
`D ≥ 2`, `Y/4^D ≤ y < (Y+1)/4^D` (`Yp_pre`), so `4^D/(Y+1) < 1/y` and
`1/y − 4^D/(Y+1) = ((Y+1)/4^D − y)/(y·(Y+1)/4^D) ≤ 4^{-D}/y² ≤ 4·4^{-D} ≤ 2^{-D}`. -/
theorem Ainv_bounds (ω : ℕ → Bool) (D : ℕ) :
    Ainv (pre ω D) ≤ 1 / cantorReal ω ∧ 1 / cantorReal ω ≤ Ainv (pre ω D) + (1 / 2 : ℝ) ^ D := by
  sorry

theorem measurable_inv_cantorReal : Measurable fun ω => 1 / cantorReal ω := by
  simp only [one_div]
  exact CantorSelfSimilar.measurable_cantorReal.inv

/-! ## Headline, `b = 2` and absolute (Problem 10.18) -/

/-- **Bugeaud 10.18, and 10.17 (normal version) for `b = 2`, computably**: a computable coin
sequence `e` with `ξ = 1/cantorReal e` absolutely normal while `1/ξ` is not normal to base `2`
(hence not absolutely normal).  Wired from the refereed Baker–Banaji input, the proved engine and
the approximation leaves. -/
theorem exists_computable_absNormal_recip_not_normal (hBB : BakerBanajiQuarterCantor) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (1 / cantorReal e) ∧
      ¬ IsNormal 2 (1 / (1 / cantorReal e)) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := polyDecay_inv hBB
  obtain ⟨e, hce, hn⟩ := ComputableNormalB.exists_computable_absNormal PsiInv primrec_PsiInv Ainv
    PsiInv_eq Ainv_nonneg (fun ω => 1 / cantorReal ω) measurable_inv_cantorReal Ainv_bounds hC hδ
    (fun ξ hξ => hdec ξ hξ)
  refine ⟨e, hce, hn, ?_⟩
  rw [one_div_one_div]
  exact not_isNormal_cantorReal e

/-! ## Every base `b`, simple normality (Problem 10.17 in full) -/

/-- Simple normality to base `b`: each digit has asymptotic frequency `1/b`. -/
def IsSimplyNormal (b : ℕ) (x : ℝ) : Prop :=
  ∀ d < b, Tendsto
    (fun n => (countOccurrences [d] ((List.range n).map (digitOf b (Int.fract x))) : ℝ) / n)
    atTop (nhds (b : ℝ)⁻¹)

theorem isSimplyNormal_of_isNormal {b : ℕ} {x : ℝ} (h : IsNormal b x) : IsSimplyNormal b x := by
  intro d hd
  have := h [d] (by simp) (by simpa using hd)
  simpa using this

/-- Base-`b` digits of the sparse Cantor point: digit `0` is `⌈b/2⌉ = (b+1)/2` (so the point lies
in `[1/2, 1)`), digit `3k+2` is the coin `e k`, all others `0`. -/
def sparseDigits (b : ℕ) (e : ℕ → Bool) (i : ℕ) : ℕ :=
  if i = 0 then (b + 1) / 2 else if i % 3 = 2 then (if e (i / 3) then 1 else 0) else 0

/-- The sparse base-`b` Cantor point coded by `e`. -/
noncomputable def ySparse (b : ℕ) (e : ℕ → Bool) : ℝ := realOfDigits b (sparseDigits b e)

/-- Pushforward Fourier transform of the law of `F (ySparse b ω)` under fair coins. -/
noncomputable def sparsePushFourier (b : ℕ) (F : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ ω, Complex.exp (2 * Real.pi * Complex.I * ((ξ * F (ySparse b ω) : ℝ) : ℂ)) ∂coinMeasure

namespace Literature

/-- **Cited input: Baker–Banaji, *Polynomial Fourier decay for fractal measures and their
pushforwards*, Math. Ann. 392 (2025) (arXiv 2401.01241v2), Corollary 1.5** (`t:self-similar`),
as quoted in Manai 2609.24665 `thm:BB`: for a non-atomic self-similar probability measure `μ`
supported in `[0,1]` and `F` `C²` on a neighbourhood of `[0,1]` with `F'' ≠ 0` on `[0,1]`,
`|∫ e(ξF) dμ| ≤ C|ξ|^{-δ}`.

**Hypothesis check** (instance `μ_b` = law of `ySparse b ω`, `b ≥ 2`):
* `ySparse b ω = ⌈b/2⌉/b + z`, `z = Σ_k ω_k b^{-(3k+3)}`; `z` is the self-similar measure of the
  IFS `{t ↦ t/b³, t ↦ (t+1)/b³}` with weights `1/2` (homogeneous ratio `b⁻³`; the images of the
  hull `[0, 1/(b³−1)]` are `[0, b⁻³/(b³−1)]` and `[b⁻³, b⁻³ + b⁻³/(b³−1)]`, disjoint since
  `b³ ≥ 8`), so non-atomic; a translate is again self-similar.
* Support: `ySparse b ω ∈ [⌈b/2⌉/b, ⌈b/2⌉/b + 1/(b³ − 1)] ⊆ [1/2, 1)`.
* Window: as in `ExplicitSquare.BakerBanajiQuarterCantor`, the rational affine change
  `t ↦ 2t − 1` maps `[1/2, 1]` to `[0, 1]`, preserves self-similarity, and turns `F` into
  `F((s+1)/2)`, `C²` near `[0,1]` with second derivative `F''/4 ≠ 0`.
* For `b = 2` this measure differs from the refereed quarter-Cantor law only in the gap pattern.

**Faithful-or-weaker:** specialisation of BB Cor 1.5 to the measures `μ_b`.  Referee pending. -/
def BakerBanajiSparse : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ F : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (1 / 2 : ℝ) 1 ⊆ U →
    ContDiffOn ℝ 2 F U → (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, deriv (deriv F) t ≠ 0) →
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖sparsePushFourier b F ξ‖ ≤ C * |ξ| ^ (-δ)

end Literature

/-- **Leaf: `ySparse b e` is never simply normal to base `b`** (digit `0` occupies positions
`3k` and `3k+1` for `k ≥ 1`, frequency `≥ 2/3 > 1/b`).

Confidence 90%.  Proof: `ySparse b e ∈ [1/2, 1)` so `Int.fract` is the identity; the digits are
proper (`ProperDigits`: infinitely many digits `< b − 1`, e.g. every `3k+1`), so
`digitOf b (ySparse b e) = sparseDigits b e` (as `digitOf_cantorReal`); among the first `n` digits
at least `2(n − 3)/3` are `0`, so the frequency of `0` has `liminf ≥ 2/3 > 1/2 ≥ 1/b`. -/
theorem not_isSimplyNormal_ySparse (b : ℕ) (hb : 2 ≤ b) (e : ℕ → Bool) :
    ¬ IsSimplyNormal b (ySparse b e) := by
  sorry

/-- **Leaf: engine inputs for `1/ySparse b`** (measurability and exact lower approximations).

Confidence 88%.  Proof: measurability as `CantorSelfSimilar.measurable_cantorReal` (each digit is a
measurable function of one coin), then `.inv`.  For the approximation, a prefix of `D` coins fixes
the base-`b` digits through position `3D + 1`; with `Y = ⌊y·b^{3D+2}⌋` (a primitive recursive sum
of those digits), `Y/b^{3D+2} ≤ y < (Y+1)/b^{3D+2}`, and since `y ≥ 1/2`,
`A p = b^{3D+2}/(Y+1)` satisfies `A ≤ 1/y ≤ A + 4·b^{-(3D+2)} ≤ A + 2^{-D}` for all `D`
(`4 b^{-(3D+2)} ≤ 4·2^{-(3D+2)} = 2^{-3D} ≤ 2^{-D}`); floors `⌊A·b'^m⌋₊ = b'^m b^{3D+2}/(Y+1)`. -/
theorem sparse_engine_inputs (b : ℕ) (hb : 2 ≤ b) :
    Measurable (fun ω => 1 / ySparse b ω) ∧
    ∃ (Ψ : ℕ → ℕ → List Bool → ℕ) (A : List Bool → ℝ),
      Primrec (fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2) ∧
      (∀ b' m p, Ψ b' m p = ⌊A p * (b' : ℝ) ^ m⌋₊) ∧ (∀ p, 0 ≤ A p) ∧
      ∀ ω D, A (pre ω D) ≤ 1 / ySparse b ω ∧ 1 / ySparse b ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D := by
  sorry

/-- **Bugeaud 10.17 for every base `b ≥ 2`, both versions, computably**: `ξ = 1/ySparse b e`
is absolutely normal (so normal and simply normal to base `b`) while `1/ξ` is not simply normal
(so not normal) to base `b`.  Conditional on the cited `Literature.BakerBanajiSparse`. -/
theorem exists_computable_absNormal_recip_not_simplyNormal (hBB : Literature.BakerBanajiSparse)
    (b : ℕ) (hb : 2 ≤ b) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (1 / ySparse b e) ∧
      ¬ IsSimplyNormal b (1 / (1 / ySparse b e)) := by
  obtain ⟨U, hU, hsub, hC2, hF''⟩ := inv_bakerBanaji_hyp
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hBB b hb _ U hU hsub hC2 hF''
  obtain ⟨hm, Ψ, A, hΨp, hΨ, hA0, hAG⟩ := sparse_engine_inputs b hb
  obtain ⟨e, hce, hn⟩ := ComputableNormalB.exists_computable_absNormal Ψ hΨp A hΨ hA0
    (fun ω => 1 / ySparse b ω) hm hAG hC hδ (fun ξ hξ => hdec ξ hξ)
  refine ⟨e, hce, hn, ?_⟩
  rw [one_div_one_div]
  exact not_isSimplyNormal_ySparse b hb e

end NormalNumbers.ReciprocalNormal
