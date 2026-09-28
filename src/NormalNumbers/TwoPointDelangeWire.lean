import NormalNumbers.TwoPointDelangeScale
import NormalNumbers.TwoPointKataiFree
import NormalNumbers.TwoPointGramDiagonal

/-!
# Cashing the `DelangeMean` discharge at the `ConjC1` headline

`delangeMean_of_norm_lt_one` (`TwoPointDelangeScale.lean`) proves `DelangeMean t` whenever
`‖phase t − 1‖ < 1`.  The `ConjC1` reductions take the Delange hypothesis in the form

    ∀ b ≥ 3, ∀ m ≠ 0 with b ∤ m,  DelangeMean (m/b),

so they cannot lose it outright: the range of `m/b` includes `1/2` (take `b` even, `m = b/2`),
where `‖phase t − 1‖ = 2` and the elementary method is provably out of reach — at `t = 1/2` the
Dirichlet series of `(−1)^{ω(n)}` is `ζ(s)·Π_p(1 − 2p^{-s}) ≈ 1/ζ(s)`, so the statement is of
Möbius/PNT strength.

What the discharge *does* buy is a strict narrowing of the cited hypothesis: it is needed only on
`‖phase (m/b) − 1‖ ≥ 1`, i.e. `‖m/b‖_{ℝ/ℤ} ≥ 1/6`.  This file
* records the exact modulus `‖phase t − 1‖ = 2|sin πt|` (so the regime is legible),
* proves `phase (m/b) ≠ 1` for `b ∤ m`,
* and re-derives the two sharpest `ConjC1` reductions with the narrowed hypothesis.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `Re e(x) = cos 2πx`. -/
lemma phase_re (x : ℝ) : (phase x).re = Real.cos (2 * Real.pi * x) := by
  have hx : phase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold phase; congr 1; push_cast; ring
  rw [hx, Complex.exp_ofReal_mul_I_re]

/-- **The exact modulus.**  `‖e(t) − 1‖ = 2|sin πt|`, so `‖e(t) − 1‖ < 1` is exactly
`‖t‖_{ℝ/ℤ} < 1/6`. -/
lemma norm_phase_sub_one_eq (t : ℝ) : ‖phase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have h : Real.cos (2 * (Real.pi * t)) = 2 * Real.cos (Real.pi * t) ^ 2 - 1 :=
      Real.cos_two_mul _
    have h2 : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    have h3 : (2 : ℝ) * Real.pi * t = 2 * (Real.pi * t) := by ring
    rw [h3, h]
    linarith
  have hsq : ‖phase t - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, phase_re, phase_im]
    have hpy : Real.sin (2 * Real.pi * t) ^ 2 + Real.cos (2 * Real.pi * t) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    rw [mul_pow, sq_abs]
    nlinarith [hcos, hpy]
  have h1 : (0 : ℝ) ≤ ‖phase t - 1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (Real.pi * t)| := by positivity
  have := Real.sqrt_le_sqrt hsq.le
  nlinarith [hsq, h1, h2]

/-- `e(m/b) ≠ 1` exactly when `b ∤ m`. -/
lemma phase_div_ne_one {b : ℕ} (hb : 0 < b) {m : ℤ} (hdvd : ¬ ((b : ℤ) ∣ m)) :
    phase (((m : ℤ) : ℝ) / b) ≠ 1 := by
  intro hcon
  rw [phase, Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have h2 : (((((m : ℤ) : ℝ) / b : ℝ)) : ℂ) = (n : ℂ) := by
    field_simp at hn
    linear_combination hn
  have ht : ((m : ℤ) : ℝ) / (b : ℝ) = (n : ℝ) := by exact_mod_cast h2
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hmz : ((m : ℤ) : ℝ) = (n : ℝ) * (b : ℝ) := by
    field_simp at ht
    linarith [ht]
  have hmi : m = n * (b : ℤ) := by exact_mod_cast hmz
  exact hdvd ⟨n, by rw [hmi]; ring⟩

/-- The discharge in legible form: `|sin πt| < 1/2`, i.e. `‖t‖_{ℝ/ℤ} < 1/6`. -/
theorem delangeMean_of_abs_sin_lt {t : ℝ} (htne : phase t ≠ 1)
    (ht : |Real.sin (Real.pi * t)| < 1 / 2) : DelangeMean t := by
  refine delangeMean_of_norm_lt_one t htne ?_
  rw [norm_phase_sub_one_eq]
  linarith

/-- **THE NARROWING.**  The cited Delange hypothesis of the `ConjC1` reductions is needed only on
`‖phase (m/b) − 1‖ ≥ 1`; below that it is a theorem of this repo. -/
theorem delangeMean_all_of_large
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      1 ≤ ‖phase (((m : ℤ) : ℝ) / b) - 1‖ → DelangeMean (((m : ℤ) : ℝ) / b)) :
    ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd
  rcases lt_or_ge ‖phase (((m : ℤ) : ℝ) / b) - 1‖ 1 with h | h
  · exact delangeMean_of_norm_lt_one _ (phase_div_ne_one (by omega) hdvd) h
  · exact hD b hb m hm hdvd h

/-- **`ConjC1` from the NARROWED Delange hypothesis plus `MultiElliott`.**  Strictly sharper than
`conjC1_of_delange_multiElliott`: the Delange input is now assumed only on `‖m/b‖_{ℝ/ℤ} ≥ 1/6`. -/
theorem conjC1_of_delangeLarge_multiElliott
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      1 ≤ ‖phase (((m : ℤ) : ℝ) / b) - 1‖ → DelangeMean (((m : ℤ) : ℝ) / b))
    (hME : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliott b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_multiElliott (delangeMean_all_of_large hD) hME

/-- **`ConjC1` from the NARROWED Delange hypothesis plus `PairDecorr`.** -/
theorem conjC1_of_delangeLarge_pairDecorr
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      1 ≤ ‖phase (((m : ℤ) : ℝ) / b) - 1‖ → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      PairDecorr b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_pairDecorr (delangeMean_all_of_large hD) hP


/-! ### Concrete, hypothesis-free instances (the audit anchors) -/

/-- **`DelangeMean t` for `0 < t < 1/6`, with NO hypotheses.**  `‖e(t)−1‖ = 2 sin πt < 2 sin(π/6) = 1`. -/
theorem delangeMean_of_lt_one_sixth {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 6) : DelangeMean t := by
  have hpi := Real.pi_pos
  have hne : phase t ≠ 1 := phase_ne_one ht0.ne' (by rw [abs_of_pos ht0]; linarith)
  refine delangeMean_of_abs_sin_lt hne ?_
  have hlt : Real.sin (Real.pi * t) < Real.sin (Real.pi / 6) := by
    refine Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith) (by nlinarith) ?_
    nlinarith
  have hpos : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  rw [abs_of_pos hpos, Real.sin_pi_div_six] at *
  linarith

/-- **`DelangeMean (1/b)` for every `b ≥ 7`, unconditionally.**  A hypothesis-free instance of
Delange's 1969 theorem in this repo's kernel. -/
theorem delangeMean_one_div {b : ℕ} (hb : 7 ≤ b) : DelangeMean (1 / (b : ℝ)) := by
  have hbR : (7 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  exact delangeMean_of_lt_one_sixth (by positivity) (by rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith)

/-- `|sin y| < 1/2` for `|y| < π/6`. -/
lemma abs_sin_lt_half {y : ℝ} (hy : |y| < Real.pi / 6) : |Real.sin y| < 1 / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨hy1, hy2⟩ := abs_lt.1 hy
  have hu : Real.sin y < 1 / 2 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ y by nlinarith) (show Real.pi / 6 ≤ Real.pi / 2 by nlinarith) hy2
    rwa [Real.sin_pi_div_six] at h
  have hl : -(1 / 2 : ℝ) < Real.sin y := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ -(Real.pi / 6) by nlinarith) (show y ≤ Real.pi / 2 by nlinarith) hy1
    rw [Real.sin_neg, Real.sin_pi_div_six] at h
    linarith
  exact abs_lt.2 ⟨hl, hu⟩

/-- The same, in the `m/b` shape the `ConjC1` reductions consume: every residue `m` with
`|m| < b/6` is now covered without any citation. -/
theorem delangeMean_div_of_abs_lt {b : ℕ} {m : ℤ} (hb : 0 < b) (hm : m ≠ 0)
    (hdvd : ¬ ((b : ℤ) ∣ m)) (hsmall : |((m : ℤ) : ℝ)| < (b : ℝ) / 6) :
    DelangeMean (((m : ℤ) : ℝ) / b) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hpi := Real.pi_pos
  refine delangeMean_of_norm_lt_one _ (phase_div_ne_one hb hdvd) ?_
  rw [norm_phase_sub_one_eq]
  have habs : |((m : ℤ) : ℝ) / (b : ℝ)| < 1 / 6 := by
    rw [abs_div, abs_of_pos hbR, div_lt_div_iff₀ hbR (by norm_num)]
    linarith
  have h1 : |Real.pi * (((m : ℤ) : ℝ) / b)| < Real.pi / 6 := by
    rw [abs_mul, abs_of_pos hpi]
    calc Real.pi * |((m : ℤ) : ℝ) / (b : ℝ)| < Real.pi * (1 / 6) :=
          mul_lt_mul_of_pos_left habs hpi
      _ = Real.pi / 6 := by ring
  have := abs_sin_lt_half h1
  linarith

end NormalNumbers.CastingOut
