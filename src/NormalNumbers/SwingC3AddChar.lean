/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3ContGlue

/-!
# `H` in additive characters: the literature-standard form

`SwingC3ContGlue.conjC3_of_weylHypothesis` reduces `ConjC3` to

`H : ∀ P Q r θ h,  (1/N) ∑_{n<N} (1_{n ≡ r (Q)} − 1/Q) · e(h·(θ + tailLarge P b n)) → 0`.

Two cosmetic obstructions stand between `H` and something a number theorist recognises: the
rotation `θ` (which is a unimodular constant and factors straight out) and the class indicator
(which is a *finite Fourier* object).  This file removes both.  Expanding

`1_{n ≡ r (Q)} − 1/Q = (1/Q) ∑_{j=1}^{Q−1} e(j(n−r)/Q)`

turns `H` into: for every `j ≢ 0 (mod Q)` and every `h`,

`(1/N) ∑_{n<N} e(jn/Q) · e(h·tailLarge P b n) → 0`  —  `AddCharTail`.

That is a multiplicative function twisted by an additive character; splitting `n` into its
`P`-smooth and `P`-rough parts and expanding `e(jst/Q)` in Dirichlet characters mod `Q` puts it
in Selberg–Delange-with-characters form (`L(s,χ)^z`, `z = e(h/b)`), which is exactly the
`(log N)^{−1}`-per-character gain the B4 probe measured.
-/

open Filter Topology Finset Complex

namespace NormalNumbers

/-- `e(x) = exp(2πi x)`. -/
noncomputable def ee (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, mul_add, Complex.exp_add]

lemma norm_ee_real (x : ℝ) : ‖ee (x : ℂ)‖ = 1 := by
  rw [ee, show (2 : ℂ) * Real.pi * Complex.I * (x : ℂ)
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma ee_int (m : ℤ) : ee (m : ℂ) = 1 := by
  rw [ee, show (2 : ℂ) * Real.pi * Complex.I * (m : ℂ)
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

lemma ee_eq_one_iff_int {x : ℝ} : ee (x : ℂ) = 1 ↔ ∃ m : ℤ, x = m := by
  rw [ee, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hx : ((x : ℂ)) = (m : ℂ) := by
      apply mul_left_cancel₀ h2
      linear_combination hm
    exact_mod_cast hx
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-- **Orthogonality of the additive characters mod `Q`.** -/
theorem sum_ee_div (Q : ℕ) (hQ : 0 < Q) (m : ℤ) :
    (∑ j ∈ range Q, ee (((j : ℝ) * m / Q : ℝ) : ℂ))
      = if ((Q : ℤ) ∣ m) then (Q : ℂ) else 0 := by
  classical
  set z : ℂ := ee (((m : ℝ) / Q : ℝ) : ℂ) with hz
  have hpow : ∀ j : ℕ, z ^ j = ee (((j : ℝ) * m / Q : ℝ) : ℂ) := by
    intro j
    rw [hz, ee, ee, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzone : z = 1 ↔ ((Q : ℤ) ∣ m) := by
    rw [hz, ee_eq_one_iff_int]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hQR : (Q : ℝ) ≠ 0 := by positivity
      have : (m : ℝ) = (Q : ℝ) * k := by field_simp at hk; linarith
      exact_mod_cast this
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      have hQR : (Q : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
  by_cases hd : ((Q : ℤ) ∣ m)
  · rw [if_pos hd]
    have h1 : z = 1 := hzone.2 hd
    simp only [← hpow, h1, one_pow, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hd]
    have h1 : z ≠ 1 := fun h => hd (hzone.1 h)
    have hzQ : z ^ Q = 1 := by
      rw [hpow Q]
      have : ((Q : ℝ) * m / Q : ℝ) = (m : ℝ) := by
        have : (Q : ℝ) ≠ 0 := by positivity
        field_simp
      rw [this]
      exact_mod_cast ee_int m
    simp only [← hpow]
    rw [geom_sum_eq h1 Q, hzQ, sub_self, zero_div]

/-! ### `H` in additive-character form -/

namespace CastingOut

open PrimeLambert

/-- **`H` as a twisted exponential sum.**  For every frequency `h` and every additive character
`j/Q` with `j ≢ 0 (mod Q)`, the large-prime tail does not correlate with the character. -/
def AddCharTail (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
        * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N) atTop (𝓝 0)

/-- Expanding the class weight in the additive characters mod `Q`. -/
lemma classWeight_eq_addChar_sum {Q : ℕ} (hQ : 0 < Q) (r n : ℕ) :
    ((classWeight r Q n : ℝ) : ℂ)
      = (1 / (Q : ℂ)) * ∑ j ∈ Ico 1 Q, ee (((j : ℝ) * ((n : ℝ) - r) / Q : ℝ) : ℂ) := by
  classical
  have hQC : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set m : ℤ := (n : ℤ) - (r : ℤ) with hm
  have hcast : ∀ j : ℕ, (((j : ℝ) * m / Q : ℝ) : ℂ) = (((j : ℝ) * ((n : ℝ) - r) / Q : ℝ) : ℂ) := by
    intro j; rw [hm]; push_cast; ring
  have hfull := sum_ee_div Q hQ m
  have hsplit : ∑ j ∈ range Q, ee (((j : ℝ) * m / Q : ℝ) : ℂ)
      = 1 + ∑ j ∈ Ico 1 Q, ee (((j : ℝ) * m / Q : ℝ) : ℂ) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hQ]
    congr 1
    norm_num [ee]
  have hdvd : ((Q : ℤ) ∣ m) ↔ n ≡ r [MOD Q] := by
    rw [hm, Nat.modEq_iff_dvd, show ((r : ℤ) - (n : ℤ)) = -((n : ℤ) - (r : ℤ)) by ring, dvd_neg]
  rw [classWeight]
  by_cases hc : n ≡ r [MOD Q]
  · rw [if_pos hc]
    rw [hfull, if_pos (hdvd.2 hc)] at hsplit
    have : ∑ j ∈ Ico 1 Q, ee (((j : ℝ) * m / Q : ℝ) : ℂ) = (Q : ℂ) - 1 := by linear_combination -hsplit
    simp only [hcast] at this
    rw [this]
    push_cast
    field_simp
  · rw [if_neg hc]
    rw [hfull, if_neg (fun hd => hc (hdvd.1 hd))] at hsplit
    have : ∑ j ∈ Ico 1 Q, ee (((j : ℝ) * m / Q : ℝ) : ℂ) = -1 := by linear_combination -hsplit
    simp only [hcast] at this
    rw [this]
    push_cast
    field_simp
    ring

/-- **The reduction of `H` to twisted exponential sums.**  Orthogonality of the additive
characters mod `Q` converts the class weight into `(1/Q)∑_{j=1}^{Q−1} e(j(n−r)/Q)`, and the
rotation `θ` factors out as a unimodular constant. -/
theorem weylTailHypothesis_of_addChar {b : ℕ} (H : AddCharTail b) : WeylTailHypothesis b := by
  classical
  intro P Q r θ h hQ
  have hQC : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set u : ℕ → ℝ := fun n => θ + tailLarge P b n with hu
  set c : ℕ → ℂ := fun j => ee ((-((j : ℝ) * r) / Q : ℝ) : ℂ) with hc
  set d : ℕ → ℕ → ℂ := fun j n =>
    ee ((((j : ℝ) * n / Q : ℝ)) : ℂ) * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ) with hd
  set T : ℕ → ℕ → ℂ := fun j N => (∑ n ∈ range N, d j n) / N with hT
  set C : ℂ := ee (((h : ℝ) * θ : ℝ) : ℂ) / Q with hC
  have hTlim : ∀ j ∈ Ico 1 Q, Tendsto (T j) atTop (𝓝 0) := by
    intro j hj
    rw [mem_Ico] at hj
    exact H P Q j h hQ (by omega) hj.2
  have hstep : ∀ n : ℕ, ((classWeight r Q n : ℝ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((u n : ℝ) : ℂ))
      = C * ∑ j ∈ Ico 1 Q, c j * d j n := by
    intro n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((u n : ℝ) : ℂ))
        = ee (((h : ℝ) * θ : ℝ) : ℂ) * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ) := by
      rw [← ee_add, ee]
      congr 1
      rw [hu]
      push_cast
      ring
    have hjj : ∀ j : ℕ, ee (((j : ℝ) * ((n : ℝ) - r) / Q : ℝ) : ℂ)
        = c j * ee ((((j : ℝ) * n / Q : ℝ)) : ℂ) := by
      intro j
      rw [hc, ← ee_add]
      congr 1
      push_cast
      ring
    rw [classWeight_eq_addChar_sum hQ r n, hexp, hC, hd]
    simp only [hjj]
    have hrw : ∀ S A B : ℂ, (1 / (Q : ℂ) * S) * (A * B) = (A / Q) * (S * B) := by
      intro S A B; field_simp
    rw [hrw]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hid : ∀ N : ℕ, wFourierMean u (classWeight r Q) h N
      = C * ∑ j ∈ Ico 1 Q, c j * T j N := by
    intro N
    rw [wFourierMean]
    rw [Finset.sum_congr rfl (fun n _ => hstep n)]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hin : ∀ j : ℕ, ∑ n ∈ range N, c j * d j n = c j * ∑ n ∈ range N, d j n :=
      fun j => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun j _ => hin j)]
    rw [hT, mul_div_assoc, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
  have hsum : Tendsto (fun N : ℕ => ∑ j ∈ Ico 1 Q, c j * T j N) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Ico 1 Q)
      (fun j hj => (hTlim j hj).const_mul (c j))
    simpa using this
  have := hsum.const_mul C
  simp only [mul_zero] at this
  exact Tendsto.congr (fun N => (hid N).symm) this

/-- **`ConjC3` from the twisted exponential-sum hypothesis.**  The chain is
`AddCharTail → WeylTailHypothesis → RotationRouteC → IsRich → ConjC3`, all machine-checked. -/
theorem conjC3_of_addCharTail (H : ∀ b, 3 ≤ b → AddCharTail b) : ConjC3 :=
  conjC3_of_weylHypothesis fun b hb => weylTailHypothesis_of_addChar (H b hb)

end CastingOut

end NormalNumbers
