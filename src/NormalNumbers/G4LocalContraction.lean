/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FreqSep
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# G4 §4C, C1 and C2: one good prime contracts the character average

Brief §4C, after the frequency separation of `G4FreqSep`:

> Good primes have distinct active roots and a default residue class of probability at least
> `1/2`, giving independent-model contraction `exp(-c L 8^{-K})`.

This file proves the two local ingredients, both unconditional.

* **C1** (`eight_mul_distZ_sq_le_one_sub_cos`): `1 - cos(2πx) ≥ 8 · dist(x,ℤ)²`.
  This is exactly the brief's "reduce every coefficient modulo one into `[-1/2,1/2]` **before**
  moment comparison": `distZ` *is* the reduced representative, the cosine does not see the
  reduction, and nothing downstream refers to the unreduced coefficient again.  Proof:
  `1 - cos 2πt = 2 sin²(πt)` and Jordan's `sin(πt) ≥ 2t` on `[0,1/2]`.

* **C2** (`norm_localSum_le`): if a uniform sample of `p` residues has `k` non-default classes
  carrying phases `x i` (one per active root — the "distinct active roots" hypothesis) and
  `p - k ≥ p/2` default classes carrying phase `0`, then

      ‖(p - k) + ∑ᵢ e(xᵢ)‖ ≤ p - 4 ∑ᵢ dist(xᵢ,ℤ)² .

  The mechanism is *not* the triangle inequality (which gives only `≤ p`): expanding
  `‖m + b‖² = m² + 2m·Re b + ‖b‖²` and using the two separate facts `Re b ≤ k - 8D` (from C1)
  and `‖b‖ ≤ k` gives `‖m + b‖² ≤ (m+k)² - 16mD = p² - 16mD ≤ p² - 8pD`, and then
  `(p - 4D)² ≥ p² - 8pD`.  The cross term `2m·Re b` is what carries the gain, which is why the
  default class needs positive density — with `m = 0` the bound degenerates.

Combined with `G4FreqSep.sum_sq_distZ_freqDepth_ge` this gives, for a single good prime,
`‖avg‖ ≤ 1 - 4·4^{-4}·8^{-K}/p` (`norm_localAvg_le_of_sum_sq`), whose product over
`p ≤ R` is the `exp(-c L 8^{-K})` of the brief.  What it does **not** give is the transfer of
that product bound to the actual arithmetic progression; that is C3, the open crux.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### C1: phase to distance -/

/-- **C1**.  `1 - cos(2πx) ≥ 8 dist(x,ℤ)²` — the reduction modulo one, done once. -/
theorem eight_mul_distZ_sq_le_one_sub_cos (x : ℝ) :
    8 * distZ x ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have ht0 : 0 ≤ distZ x := distZ_nonneg x
  have ht2 : distZ x ≤ 1 / 2 := abs_sub_round x
  have hcos : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * distZ x) := by
    have h1 : 2 * Real.pi * x = 2 * Real.pi * (x - round x) + (round x : ℤ) * (2 * Real.pi) := by
      ring
    rw [h1, Real.cos_add_int_mul_two_pi]
    unfold distZ
    rcases abs_choice (x - round x) with h | h
    · rw [h]
    · rw [h, show 2 * Real.pi * -(x - round x) = -(2 * Real.pi * (x - round x)) by ring,
        Real.cos_neg]
  have h2 : Real.cos (2 * Real.pi * distZ x) = 1 - 2 * Real.sin (Real.pi * distZ x) ^ 2 := by
    rw [show 2 * Real.pi * distZ x = 2 * (Real.pi * distZ x) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (Real.pi * distZ x)
    linarith
  have hj : 2 * distZ x ≤ Real.sin (Real.pi * distZ x) := by
    have hpi := Real.pi_pos
    have h := Real.mul_le_sin (x := Real.pi * distZ x) (by positivity) (by nlinarith)
    calc 2 * distZ x = 2 / Real.pi * (Real.pi * distZ x) := by field_simp
      _ ≤ _ := h
  rw [hcos, h2]
  nlinarith [hj, ht0]

/-! ### C2: one good prime -/

/-- The additive character `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

@[simp] lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * Real.pi * x) :=
  Complex.exp_ofReal_mul_I_re _

lemma normSq_expand (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- **C2, the single good prime.**  With `k` active roots carrying phases `x i` and at least
`p/2` default classes, the unnormalised character sum drops below `p` by `4 ∑ dist(xᵢ,ℤ)²`. -/
theorem norm_localSum_le {p k : ℕ} (hk : 2 * k ≤ p) (x : Fin k → ℝ) :
    ‖((p - k : ℕ) : ℂ) + ∑ i, ee (x i)‖ ≤ (p : ℝ) - 4 * ∑ i, distZ (x i) ^ 2 := by
  set D : ℝ := ∑ i, distZ (x i) ^ 2 with hD
  set b : ℂ := ∑ i, ee (x i) with hb
  have hkp : k ≤ p := by omega
  have hm : ((p - k : ℕ) : ℝ) = (p : ℝ) - k := by
    rw [Nat.cast_sub hkp]
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- each term is at most 1/4, so 4 D ≤ k
  have hDk : 4 * D ≤ (k : ℝ) := by
    have : D ≤ ∑ _i : Fin k, (1 / 4 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : distZ (x i) ≤ 1 / 2 := abs_sub_round _
      have h0 : 0 ≤ distZ (x i) := distZ_nonneg _
      nlinarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  -- real part of b
  have hbre : b.re ≤ (k : ℝ) - 8 * D := by
    have hre : b.re = ∑ i, Real.cos (2 * Real.pi * x i) := by
      rw [hb, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => ee_re (x i)
    rw [hre]
    have : ∑ i, Real.cos (2 * Real.pi * x i) ≤ ∑ i : Fin k, (1 - 8 * distZ (x i) ^ 2) :=
      Finset.sum_le_sum fun i _ => by linarith [eight_mul_distZ_sq_le_one_sub_cos (x i)]
    calc ∑ i, Real.cos (2 * Real.pi * x i) ≤ ∑ i : Fin k, (1 - 8 * distZ (x i) ^ 2) := this
      _ = (k : ℝ) - 8 * D := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one, ← Finset.mul_sum, hD]
  -- norm of b
  have hbnorm : ‖b‖ ≤ (k : ℝ) := by
    calc ‖b‖ ≤ ∑ i, ‖ee (x i)‖ := norm_sum_le _ _
      _ = (k : ℝ) := by simp
  have hbsq : ‖b‖ ^ 2 ≤ (k : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
    nlinarith
  -- expand
  have hexp : ‖((p - k : ℕ) : ℂ) + b‖ ^ 2
      = ((p : ℝ) - k) ^ 2 + 2 * ((p : ℝ) - k) * b.re + ‖b‖ ^ 2 := by
    rw [normSq_expand, normSq_expand b]
    simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, hm]
    ring
  have hmge : (p : ℝ) / 2 ≤ (p : ℝ) - k := by
    have : (2 : ℝ) * k ≤ p := by exact_mod_cast hk
    linarith
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsq : ‖((p - k : ℕ) : ℂ) + b‖ ^ 2 ≤ ((p : ℝ) - 4 * D) ^ 2 := by
    have hstep : ‖((p - k : ℕ) : ℂ) + b‖ ^ 2 ≤ (p : ℝ) ^ 2 - 16 * ((p : ℝ) - k) * D := by
      rw [hexp]
      nlinarith [hbre, hbsq, hmge, hD0]
    nlinarith [hstep, hmge, hD0, sq_nonneg D]
  have hpos : (0 : ℝ) ≤ (p : ℝ) - 4 * D := by
    have : (k : ℝ) ≤ (p : ℝ) := Nat.cast_le.2 hkp
    linarith
  nlinarith [hsq, norm_nonneg (((p - k : ℕ) : ℂ) + b), hpos]


/-- The same, indexed by an arbitrary finite set of active roots. -/
theorem norm_localSum_le' {p : ℕ} {ι : Type*} [Fintype ι] (hk : 2 * Fintype.card ι ≤ p)
    (x : ι → ℝ) :
    ‖((p - Fintype.card ι : ℕ) : ℂ) + ∑ i, ee (x i)‖ ≤ (p : ℝ) - 4 * ∑ i, distZ (x i) ^ 2 := by
  classical
  have e := Fintype.equivFin ι
  have h1 : ∑ i, ee (x i) = ∑ j : Fin (Fintype.card ι), ee (x (e.symm j)) :=
    (Equiv.sum_comp e.symm (fun i => ee (x i))).symm
  have h2 : ∑ i, distZ (x i) ^ 2 = ∑ j : Fin (Fintype.card ι), distZ (x (e.symm j)) ^ 2 :=
    (Equiv.sum_comp e.symm (fun i => distZ (x i) ^ 2)).symm
  rw [h1, h2]
  exact norm_localSum_le hk _

/-- **The normalised single-prime contraction.**  If the squared distances of the active phases
total at least `θ`, the local character average has norm at most `1 - 4θ/p`. -/
theorem norm_localAvg_le_of_sum_sq {p : ℕ} {ι : Type*} [Fintype ι] (hp : 0 < p)
    (hk : 2 * Fintype.card ι ≤ p) (x : ι → ℝ) {θ : ℝ} (hθ : θ ≤ ∑ i, distZ (x i) ^ 2) :
    ‖(p : ℂ)⁻¹ * (((p - Fintype.card ι : ℕ) : ℂ) + ∑ i, ee (x i))‖ ≤ 1 - 4 * θ / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h := norm_localSum_le' hk x
  have hmono : (p : ℝ) - 4 * ∑ i, distZ (x i) ^ 2 ≤ (p : ℝ) - 4 * θ := by linarith
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hp0]
  calc ‖((p - Fintype.card ι : ℕ) : ℂ) + ∑ i, ee (x i)‖
      ≤ (p : ℝ) - 4 * ∑ i, distZ (x i) ^ 2 := h
    _ ≤ (p : ℝ) - 4 * θ := hmono
    _ = (p : ℝ) * (1 - 4 * θ / p) := by field_simp

/-! ### The product over good primes -/

/-- `∏ (1 - f i) ≤ exp(-∑ f i)`: the step from per-prime contraction to
`exp(-c L 8^{-K})` once `∑_{p ≤ R} p⁻¹ = L - o(L)`. -/
lemma prod_one_sub_le_exp_neg_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (_hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, (1 - f i) ≤ Real.exp (-∑ i ∈ s, f i) := by
  have hsum : -∑ i ∈ s, f i = ∑ i ∈ s, -(f i) := by rw [Finset.sum_neg_distrib]
  rw [hsum, Real.exp_sum]
  refine Finset.prod_le_prod (fun i hi => by linarith [hf1 i hi]) (fun i hi => ?_)
  have := Real.add_one_le_exp (-(f i))
  linarith

/-- **The independent-model decay.**  If every prime in `𝒫` contracts by `1 - c/p`, the product
is at most `exp(-c ∑_{p ∈ 𝒫} p⁻¹)`.  With `c = 4·4^{-4}·8^{-K}` (from
`G4FreqSep.sum_sq_distZ_freqDepth_ge` through `norm_localAvg_le_of_sum_sq`) and
`∑_{p ≤ R} p⁻¹ = L - o(L)`, this is the brief's `exp(-c L 8^{-K})`.

What remains open is **C3**: this is a bound in the independent residue model, and the transfer
to the actual arithmetic progression is not automatic independence. -/
theorem prod_contraction_le_exp {ι : Type*} (s : Finset ι) (w : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw : ∀ i ∈ s, 0 < w i) (hcw : ∀ i ∈ s, c ≤ w i) :
    ∏ i ∈ s, (1 - c / w i) ≤ Real.exp (-∑ i ∈ s, c / w i) := by
  refine prod_one_sub_le_exp_neg_sum s (fun i => c / w i) (fun i hi => ?_) (fun i hi => ?_)
  · exact div_nonneg hc (hw i hi).le
  · rw [div_le_one (hw i hi)]
    exact hcw i hi

end NormalNumbers.G4
