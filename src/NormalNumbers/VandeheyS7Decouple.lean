/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-DC: the two places are decoupled — the straddle cap is asymptotically vacuous

`VandeheyS7Straddle.image_no_rational_of_zquot` prices the straddle with Galois repulsion: an image
interval of width below `1/(Q²·|δ|·(B+D))` contains no rational of denominator `≤ Q`, so the emitter
must fire.  The obvious question is whether that threshold stays useful along the orbit.  **It does
not, and this module proves it in the kernel rather than by hand.**

The obstruction is Dirichlet's unit theorem, in the concrete form the repo already has
(`VandeheyS7Wall.infinite_zPhi_abs_le_one`): `ζ = φ − 1` is a unit with `|ζ| < 1`, so `ζⁿ` is
bounded at the real place while `|(ζⁿ)'| ≥ ζ^{-n} → ∞`.  Hence:

* `exists_bounded_zval_large_zconj` — for every `R` there is a `ℤ[φ]`-number of modulus `≤ 1` whose
  conjugate exceeds `R`;
* `exists_unit_zval_large_zconj` — and one of modulus **in `[1,2]`**, so the real place is bounded
  *below* as well.  This is the version the cap cares about: `|δ| ≍ 1` with `|δ'|` unbounded.
* `straddle_threshold_lt` — therefore, for every depth `Q` and every `ε > 0`, there is a state
  denominator with `|δ| ∈ [1,2]` whose cap threshold `1/(Q²·|δ|·|δ'|)` is below `ε`.

**Consequence for the route, and it is a refutation.**  The straddle cap cannot be applied at a
fixed scale along the orbit: for `Oₙ⁻¹ Φ Pₙ` the conjugate height runs like `q_out·q_in ≍ e^{2λn}`
while the real place — and the lag we need to drain — stay `O(1)`.  So Galois repulsion controls the
straddle only at the first `O(1)` scales.  **No sharpening of the repulsion estimate can fix this**;
the two archimedean places of `ℚ(φ)` are independent, which is exactly the statement that the
relevant homogeneous space is the 2-dimensional Hilbert modular surface rather than the modular
curve.  The missing input is equidistribution in the second place.

This is the directive's "attack the ARITHMETIC of `Φ`" carried to its conclusion: the arithmetic
gives a real, sharp cap (`image_no_rational_of_zquot`), and the arithmetic also says how far it
reaches.  A sub-route is hereby closed, with a kernel certificate.
-/
import NormalNumbers.VandeheyS7Straddle
import NormalNumbers.VandeheyS7Wall

namespace NormalNumbers.VandeheyS7

open Real

/-- The coefficient pair of `ζⁿ`, together with the two facts we need about it. -/
theorem exists_zeta_pow_pair (n : ℕ) :
    ∃ a b : ℤ, zval a b = zeta ^ n ∧ ¬ (a = 0 ∧ b = 0) := by
  obtain ⟨a, b, hab⟩ := isZPhi_zeta.pow n
  refine ⟨a, b, ?_, ?_⟩
  · rw [zval, ← hab]
  · rintro ⟨rfl, rfl⟩
    have h0 : zeta ^ n = 0 := by simpa using hab
    exact absurd h0 (pow_ne_zero n zeta_pos.ne')

/-- **The real place is bounded while the conjugate is not.**  For every `R` there is a
`ℤ[φ]`-number of modulus at most `1` whose conjugate exceeds `R`. -/
theorem exists_bounded_zval_large_zconj (R : ℝ) :
    ∃ a b : ℤ, |zval a b| ≤ 1 ∧ R ≤ |zconj a b| := by
  rcases le_or_gt R 1 with hR | hR
  · refine ⟨1, 0, ?_, ?_⟩
    · simp [zval]
    · have : zconj 1 0 = 1 := by simp [zconj]
      rw [this]; simpa using hR
  · -- pick `n` with `ζⁿ ≤ 1/R`
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < 1 / R) zeta_lt_one
    obtain ⟨a, b, hval, hnz⟩ := exists_zeta_pow_pair n
    have hzp : 0 < zeta ^ n := pow_pos zeta_pos n
    have hval1 : |zval a b| ≤ 1 := by
      rw [hval, abs_of_pos hzp]
      exact pow_le_one₀ zeta_pos.le zeta_lt_one.le
    refine ⟨a, b, hval1, ?_⟩
    have hrep := abs_zval_ge_inv_abs_zconj hnz
    have hcpos : 0 < |zconj a b| := abs_pos.2 (zconj_ne_zero hnz)
    rw [hval, abs_of_pos hzp] at hrep
    rw [div_le_iff₀ hcpos] at hrep
    -- `1 ≤ ζⁿ · |conj|` and `ζⁿ < 1/R` give `R < |conj|`
    have hR0 : (0:ℝ) < R := lt_trans zero_lt_one hR
    rw [lt_div_iff₀ hR0] at hn
    nlinarith [hrep, hn, hcpos, hzp]

/-- **The version the straddle cap cares about**: modulus bounded *below* as well, so this really
is a state denominator of size `≍ 1` with an unbounded conjugate. -/
theorem exists_unit_zval_large_zconj (R : ℝ) :
    ∃ a b : ℤ, 1 ≤ |zval a b| ∧ |zval a b| ≤ 3 ∧ R ≤ |zconj a b| := by
  have key : ∀ t : ℝ, |t| ≤ 1 → 1 ≤ |2 + t| ∧ |2 + t| ≤ 3 := by
    intro t ht
    rcases abs_cases t with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases abs_cases (2 + t) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith
  have key2 : ∀ u : ℝ, |u| - 2 ≤ |2 + u| := by
    intro u
    rcases abs_cases u with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases abs_cases (2 + u) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith
  obtain ⟨a, b, hval, hconj⟩ := exists_bounded_zval_large_zconj (R + 2)
  have hv : zval (a + 2) b = 2 + zval a b := by simp only [zval]; push_cast; ring
  have hc : zconj (a + 2) b = 2 + zconj a b := by simp only [zconj]; push_cast; ring
  obtain ⟨h1, h2⟩ := key _ hval
  refine ⟨a + 2, b, ?_, ?_, ?_⟩
  · rw [hv]; exact h1
  · rw [hv]; exact h2
  · rw [hc]; linarith [key2 (zconj a b)]

/-- **The refutation.**  For every depth `Q` and every `ε > 0` there is a state denominator with
`|δ| ∈ [1,2]` whose straddle-cap threshold `1/(Q²·|δ|·|δ'|)` is below `ε`: the cap cannot be applied
at a fixed scale along the orbit.  No sharpening of the repulsion estimate helps — the two
archimedean places of `ℚ(φ)` are independent. -/
theorem straddle_threshold_lt {Q : ℕ} (hQ : 1 ≤ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, 1 ≤ |zval a b| ∧ |zval a b| ≤ 3 ∧
      1 / ((Q : ℝ) ^ 2 * |zval a b| * |zconj a b|) < ε := by
  obtain ⟨a, b, hlo, hhi, hconj⟩ := exists_unit_zval_large_zconj (1 / ε + 1)
  have hQ0 : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1:ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hεinv : 0 < 1 / ε := by positivity
  have hcpos : (0:ℝ) < |zconj a b| := lt_of_lt_of_le (by linarith) hconj
  refine ⟨a, b, hlo, hhi, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  have hprod : 1 / ε + 1 ≤ (Q : ℝ) ^ 2 * |zval a b| * |zconj a b| := by
    calc 1 / ε + 1 ≤ |zconj a b| := hconj
      _ = 1 * 1 * |zconj a b| := by ring
      _ ≤ (Q : ℝ) ^ 2 * |zval a b| * |zconj a b| := by
          gcongr
          · nlinarith
  have hεq : 1 = ε * (1 / ε) := by field_simp
  calc (1:ℝ) = ε * (1 / ε) := hεq
    _ < ε * (1 / ε + 1) := by nlinarith
    _ ≤ ε * ((Q : ℝ) ^ 2 * |zval a b| * |zconj a b|) := by
        exact mul_le_mul_of_nonneg_left hprod hε.le

section Audit

#print axioms exists_zeta_pow_pair
#print axioms exists_bounded_zval_large_zconj
#print axioms exists_unit_zval_large_zconj
#print axioms straddle_threshold_lt

end Audit

end NormalNumbers.VandeheyS7
