import NormalNumbers.ElliottTwistBootstrap

/-!
# Input (c) as stated is FALSE — the frequency range is off by a `(log X)^{ε}`

`ElliottTwistBootstrap.ArchimedeanCorrelationBound A η` asserts

  `‖∑_{p≤X} p^{-iv}/p‖ ≤ (1-η)·∑_{p≤X} 1/p`   for `1 < |v| log X` and `|v| ≤ A²X`.

This file **refutes it**, for every level `A ≥ 1` and every `η > 0`, by an entirely elementary
computation at the single frequency `v = 2/log X`:

* that frequency satisfies the hypothesis `|v| log X = 2 > 1` exactly;
* but then `|v| log p ≤ 2` for *every* `p ≤ X`, so the phases never leave a bounded arc and
  `cos(v log p) ≥ 1 - (v log p)²/2`, whence

    `Re ∑_{p≤X} p^{-iv}/p ≥ M(X) - (v²/2)·∑_{p≤X}(log p)²/p ≥ M(X) - 2 - 2C`,

  where `C` is the constant in Mertens' first theorem `∑_{p≤X}(log p)/p ≤ log X + C`
  (`ElliottZetaOmegaPretentious.exists_mertensOne`), using `(log p)² ≤ (log X)(log p)`.

Since `M(X) → ∞`, `M(X) - 2 - 2C > (1-η)M(X)` for all large `X`, contradicting the bound.

**Consequence.**  `ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density` is
*vacuous* as it stands: one of its two hypotheses is false, so it proves nothing.  The defect is
the *frequency range*, not the estimate: `‖∑_{p≤X}p^{-iv}/p‖ ≈ log(1/|v|) + O(1)` for
`1/log X ≤ |v| ≤ 1`, so the honest threshold for a fixed loss `η` is `|v| ≥ (log X)^{-1+ε}`,
not `|v| ≥ 1/log X`.  The repair is recorded in `ROUTE-ESCALATION-2026-09-25-archimedean.md`.
-/

open Finset

namespace NormalNumbers.ElliottArchimedeanRefuted

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap

noncomputable section

/-- `Re(p^{iv}) = cos(v log p)`. -/
theorem re_archimedeanTwist {p : ℕ} (hp : 0 < p) (v : ℝ) :
    (archimedeanTwist v p).re = Real.cos (v * Real.log p) := by
  rw [archimedeanTwist_eq_exp hp]
  have h : Complex.I * (v : ℂ) * ((Real.log p : ℝ) : ℂ)
      = ((v * Real.log p : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- The real part of the Archimedean correlation is the cosine sum. -/
theorem re_archCorr (v : ℝ) (X : ℕ) :
    (archCorr v X).re = ∑ p ∈ primesUpTo X, Real.cos (v * Real.log p) / (p : ℝ) := by
  rw [archCorr, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp0 : 0 < p := (mem_primesUpTo.mp hp).1.pos
  have hcast : ((p : ℂ)) = ((p : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.div_ofReal_re, Complex.conj_re, re_archimedeanTwist hp0]

/-- `∑_{p≤X}(log p)²/p ≤ (log X)·∑_{p≤X}(log p)/p`, since `log p ≤ log X` on the window. -/
theorem sum_logSq_le (X : ℕ) :
    ∑ p ∈ primesUpTo X, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
      ≤ Real.log (X : ℝ) * ∑ p ∈ primesUpTo X, Real.log (p : ℝ) / (p : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro p hp
  obtain ⟨hpp, hpX⟩ := mem_primesUpTo.mp hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hle : Real.log (p : ℝ) ≤ Real.log (X : ℝ) := by
    refine Real.log_le_log hpR ?_
    exact_mod_cast hpX
  rw [pow_two, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- The pointwise quadratic lower bound, summed: the Archimedean correlation cannot lose more
than `(v²/2)∑(log p)²/p` of the full prime mass. -/
theorem re_archCorr_ge (v : ℝ) (X : ℕ) :
    primeMass X - v ^ 2 / 2 * ∑ p ∈ primesUpTo X, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
      ≤ (archCorr v X).re := by
  rw [re_archCorr, primeMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum ?_
  intro p hp
  have hpp := (mem_primesUpTo.mp hp).1
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hcos : 1 - (v * Real.log (p : ℝ)) ^ 2 / 2 ≤ Real.cos (v * Real.log (p : ℝ)) :=
    Real.one_sub_sq_div_two_le_cos
  have hsplit : (p : ℝ)⁻¹ - v ^ 2 / 2 * ((Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      = (1 - (v * Real.log (p : ℝ)) ^ 2 / 2) / (p : ℝ) := by
    field_simp
  rw [hsplit]
  gcongr

/-- **THE REFUTATION.**  For every level `A ≥ 1` and every `η > 0`, input (c) is false. -/
theorem not_archimedeanCorrelationBound {A : ℕ} (hA : 0 < A) {η : ℝ} (hη : 0 < η) :
    ¬ ArchimedeanCorrelationBound A η := by
  rintro ⟨X₀, hX₀2, hbd⟩
  obtain ⟨C, hC0, hC⟩ := exists_mertensOne
  obtain ⟨X₁, hX₁2, hX₁⟩ := exists_primeMass_ge ((2 + 2 * C) / η + 1)
  set X : ℕ := max (max X₀ X₁) 3 with hXdef
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hXX₁ : X₁ ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  have hX3 : 3 ≤ X := le_max_right _ _
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
  have hlogX : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hlogXpos : (0 : ℝ) < Real.log (X : ℝ) := by linarith
  set v : ℝ := 2 / Real.log (X : ℝ) with hvdef
  have hvpos : 0 < v := by rw [hvdef]; positivity
  have hvabs : |v| = v := abs_of_pos hvpos
  -- the frequency lies in the hypothesised range
  have hfreq : 1 < |v| * Real.log (X : ℝ) := by
    rw [hvabs, hvdef, div_mul_cancel₀ _ (ne_of_gt hlogXpos)]; norm_num
  have hvup : |v| ≤ (A : ℝ) * (A : ℝ) * X := by
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hv2 : v ≤ 2 := by
      rw [hvdef, div_le_iff₀ hlogXpos]; linarith
    have : (3 : ℝ) ≤ (A : ℝ) * (A : ℝ) * X := by nlinarith
    rw [hvabs]; linarith
  have hkey := hbd X hXX₀ v hfreq hvup
  -- the elementary lower bound
  have hmass : (2 + 2 * C) / η + 1 ≤ primeMass X := hX₁ X hXX₁
  have hMpos : 0 < primeMass X := by
    have : (0 : ℝ) ≤ (2 + 2 * C) / η := by positivity
    linarith
  have hlogsum : ∑ p ∈ primesUpTo X, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
      ≤ Real.log (X : ℝ) * (Real.log (X : ℝ) + C) := by
    refine le_trans (sum_logSq_le X) ?_
    exact mul_le_mul_of_nonneg_left (hC X) hlogXpos.le
  have hloss : v ^ 2 / 2 * ∑ p ∈ primesUpTo X, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
      ≤ 2 + 2 * C := by
    have hv2 : v ^ 2 / 2 = 2 / (Real.log (X : ℝ)) ^ 2 := by
      rw [hvdef, div_pow]; ring
    have hnn : (0 : ℝ) ≤ v ^ 2 / 2 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hlogsum hnn) ?_
    rw [hv2]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < (Real.log (X:ℝ))^2)]
    nlinarith [mul_nonneg (mul_nonneg hC0 hlogXpos.le) (sub_nonneg.mpr hlogX)]
  have hlower : primeMass X - (2 + 2 * C) ≤ (archCorr v X).re := by
    have := re_archCorr_ge v X
    linarith
  have hnorm : (archCorr v X).re ≤ ‖archCorr v X‖ := Complex.re_le_norm _
  -- contradiction
  have hne : η ≠ 0 := ne_of_gt hη
  have hexp : (1 - η) * primeMass X = primeMass X - η * primeMass X := by ring
  have hcontra : η * primeMass X ≤ 2 + 2 * C := by
    rw [hexp] at hkey; linarith
  have heq : η * ((2 + 2 * C) / η + 1) = 2 + 2 * C + η := by field_simp
  have h2 := mul_le_mul_of_nonneg_left hmass hη.le
  rw [heq] at h2
  linarith

end

end NormalNumbers.ElliottArchimedeanRefuted
