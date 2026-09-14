import NormalNumbers.PrimeLambertHexagonCounterexample

/-!
# Refutation of hexagon nonnegativity on `ℤ/19ℤ` (the eighth-root witness)

`PrimeLambertHexagonCounterexample` refutes mean retention `|𝔼 f|^6 ≤ H(f)` on `ℤ/7ℤ`, but
its witness has `H > 0`.  The attended addendum (2026-09-14, 00:39 UTC) gives a stronger and
simpler witness on `ℤ/19ℤ`: with `η = e^{2πi/8}` and exponents

  `e = (0,2,4,3,3,2,1,2,4,0,2,2,4,0,2,3,2,1,1)`,   `f(x) = η^{e_x}`,

the `19³ = 6859` hexagon phases have residue counts mod 8

  `(1561, 450, 753, 900, 1092, 900, 753, 450)`   (kernel `decide`),

so `6859 · H(f) = 469 − 450√2 < 0` (certificate `469² < 2·450²`), while the exponent
multiplicities `#0 = 3, #1 = 3, #2 = 7, #3 = 3, #4 = 3` give `∑ f = i(7 + 3√2)` and
`|𝔼 f| = (7 + 3√2)/19 > 1/2`.

This refutes both

* `HexNonneg 19`: every unimodular `f` has `Re H(f) ≥ 0`, and
* `HexNonnegOfLargeMean 19`: every unimodular `f` with `|𝔼 f| > 1/2` has `Re H(f) ≥ 0`,

so neither taking absolute values nor squaring `H` can rescue a universally positive lower
bound for the hexagon correlation in terms of the mean.  The eighth root of unity is
identified exactly through `cos(π/4) = sin(π/4) = √2/2`; no numerics.  (The IVT corollary of
the addendum — an interpolant with `H = 0` and mean `> 1/2` — is recorded in the docs only.)
-/

open Complex Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- The (false) nonnegativity conjecture for the cyclic hexagon correlation on `ZMod q`. -/
def HexNonneg (q : ℕ) [NeZero q] : Prop :=
  ∀ f : ZMod q → ℂ, (∀ x, ‖f x‖ = 1) → 0 ≤ (hexCorr f).re

/-- The (false) nonnegativity conjecture under the mean constraint `|𝔼 f| > 1/2`. -/
def HexNonnegOfLargeMean (q : ℕ) [NeZero q] : Prop :=
  ∀ f : ZMod q → ℂ, (∀ x, ‖f x‖ = 1) → 1 / 2 < ‖meanF f‖ → 0 ≤ (hexCorr f).re

lemma hexNonnegOfLargeMean_of_hexNonneg {q : ℕ} [NeZero q] (h : HexNonneg q) :
    HexNonnegOfLargeMean q := fun f hf _ => h f hf

/-! ### The eighth root of unity `η = exp(πi/4) = (1 + i)√2/2` -/

/-- `√2` as a real number. -/
noncomputable def s2 : ℝ := Real.sqrt 2

lemma s2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma s2_pos : 0 < s2 := Real.sqrt_pos.mpr (by norm_num)
lemma s2_sqC : (s2 : ℂ) ^ 2 = 2 := by exact_mod_cast s2_sq

/-- `η = exp(2πi/8)`. -/
noncomputable def η : ℂ := exp (((Real.pi / 4 : ℝ) : ℂ) * I)

lemma η_eq : η = ((s2 / 2 : ℝ) : ℂ) + ((s2 / 2 : ℝ) : ℂ) * I := by
  unfold η
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  rfl

lemma η_sq : η ^ 2 = I := by
  rw [η_eq]
  push_cast
  linear_combination ((s2 : ℂ) / 2) ^ 2 * I_sq + (I / 2) * s2_sqC

lemma η_pow_four : η ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, η_sq, I_sq]

lemma η_pow_eight : η ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, η_pow_four]; norm_num

lemma η_ne_zero : η ≠ 0 := by unfold η; exact exp_ne_zero _

lemma norm_η : ‖η‖ = 1 := by unfold η; exact Complex.norm_exp_ofReal_mul_I _

/-- `η · (i − 1) = −√2`. -/
lemma η_mul_I_sub_one : η * (I - 1) = -(s2 : ℂ) := by
  rw [η_eq]; push_cast; linear_combination ((s2 : ℂ) / 2) * I_sq

/-- `η · (1 + i) = √2 · i`. -/
lemma η_mul_one_add_I : η * (1 + I) = (s2 : ℂ) * I := by
  rw [η_eq]; push_cast; linear_combination ((s2 : ℂ) / 2) * I_sq

lemma conj_η_pow (n : ℕ) : (starRingEnd ℂ) (η ^ n) = η ^ (-(n : ℤ)) := by
  rw [map_pow, ← inv_eq_conj norm_η, inv_pow, ← zpow_natCast, ← zpow_neg]

/-- Reduce a `zpow` of `η` modulo 8. -/
lemma η_zpow_mod (n : ℤ) : η ^ n = η ^ (n % 8).toNat := by
  have hn : n = 8 * (n / 8) + n % 8 := by omega
  have hnn : 0 ≤ n % 8 := Int.emod_nonneg n (by norm_num)
  have h8z : η ^ (8 : ℤ) = 1 := by exact_mod_cast η_pow_eight
  conv_lhs => rw [hn]
  rw [zpow_add₀ η_ne_zero, zpow_mul, h8z, one_zpow, one_mul]
  conv_lhs => rw [← Int.toNat_of_nonneg hnn]
  rw [zpow_natCast]

/-- Generic fibre reduction: a sum of `η`-powers is the count-weighted sum over residues. -/
lemma sum_η_zpow_eq {ι : Type*} [Fintype ι] (E : ι → ℤ) (cnt : Fin 8 → ℕ)
    (hcnt : ∀ k : Fin 8,
      ((univ : Finset ι).filter (fun t => (E t % 8).toNat = (k : ℕ))).card = cnt k) :
    ∑ t, η ^ E t = ∑ k : Fin 8, (cnt k : ℂ) * η ^ (k : ℕ) := by
  have hmaps : ∀ t ∈ (univ : Finset ι), (E t % 8).toNat ∈ range 8 := by
    intro t _
    rw [mem_range]
    have h1 : E t % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
    have h2 : 0 ≤ E t % 8 := Int.emod_nonneg _ (by norm_num)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => η ^ E t)]
  rw [Finset.sum_range (fun k => ∑ t ∈ univ with (E t % 8).toNat = k, η ^ E t)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← hcnt k, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [mem_filter] at ht
  rw [η_zpow_mod, ht.2, Nat.cast_one, one_mul]

/-! ### The witness on `ℤ/19ℤ` -/

/-- Exponent table `(0,2,4,3,3,2,1,2,4,0,2,2,4,0,2,3,2,1,1)`. -/
def ex19 : Fin 19 → ℕ := ![0, 2, 4, 3, 3, 2, 1, 2, 4, 0, 2, 2, 4, 0, 2, 3, 2, 1, 1]

/-- The witness `f(x) = η^{e_x}`. -/
noncomputable def fN (x : ZMod 19) : ℂ := η ^ (ex19 x)

lemma norm_fN (x : ZMod 19) : ‖fN x‖ = 1 := by
  unfold fN; rw [norm_pow, norm_η, one_pow]

/-- Integer phase exponent of the hexagon term. -/
def hexE19 (x a b : ZMod 19) : ℤ :=
  (ex19 (x - a) : ℤ) + ex19 (x - b) + ex19 (x + a + b)
    - ex19 (x + a) - ex19 (x + b) - ex19 (x - a - b)

lemma hex_term19 (x a b : ZMod 19) :
    fN (x - a) * fN (x - b) * fN (x + a + b) *
      (starRingEnd ℂ) (fN (x + a) * fN (x + b) * fN (x - a - b)) = η ^ hexE19 x a b := by
  unfold fN hexE19
  rw [map_mul, map_mul, conj_η_pow, conj_η_pow, conj_η_pow]
  simp only [sub_eq_add_neg, zpow_add₀ η_ne_zero, zpow_natCast]
  ring

/-- Hexagon residue counts `(1561, 450, 753, 900, 1092, 900, 753, 450)`. -/
def hexCount19 : Fin 8 → ℕ := ![1561, 450, 753, 900, 1092, 900, 753, 450]

set_option maxRecDepth 100000 in
lemma hexCount19_eq (k : Fin 8) :
    ((univ : Finset (ZMod 19 × ZMod 19 × ZMod 19)).filter
      (fun t => (hexE19 t.1 t.2.1 t.2.2 % 8).toNat = (k : ℕ))).card = hexCount19 k := by
  revert k; decide +kernel

/-- Exponent multiplicities `(3, 3, 7, 3, 3, 0, 0, 0)`. -/
def meanCount19 : Fin 8 → ℕ := ![3, 3, 7, 3, 3, 0, 0, 0]

lemma meanCount19_eq (k : Fin 8) :
    ((univ : Finset (ZMod 19)).filter
      (fun t => ((ex19 t : ℤ) % 8).toNat = (k : ℕ))).card = meanCount19 k := by
  revert k; decide +kernel

/-- `6859 · H(f) = 469 − 450√2`. -/
lemma hexCorr_fN_num :
    (∑ x : ZMod 19, ∑ a : ZMod 19, ∑ b : ZMod 19,
      fN (x - a) * fN (x - b) * fN (x + a + b) *
        (starRingEnd ℂ) (fN (x + a) * fN (x + b) * fN (x - a - b)))
      = 469 - 450 * (s2 : ℂ) := by
  simp_rw [hex_term19]
  have h : (∑ x : ZMod 19, ∑ a : ZMod 19, ∑ b : ZMod 19, η ^ hexE19 x a b)
      = ∑ t : ZMod 19 × ZMod 19 × ZMod 19, η ^ hexE19 t.1 t.2.1 t.2.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_prod_type]
  rw [h, sum_η_zpow_eq _ hexCount19 hexCount19_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hexCount19]
  simp
  have h3 : η ^ 3 = I * η := by rw [pow_succ, η_sq]
  have h5 : η ^ 5 = -η := by rw [pow_succ, η_pow_four]; ring
  have h6 : η ^ 6 = -I := by rw [show (6 : ℕ) = 4 + 2 by norm_num, pow_add, η_pow_four, η_sq]; ring
  have h7 : η ^ 7 = -(I * η) := by rw [show (7 : ℕ) = 4 + 3 by norm_num, pow_add, η_pow_four, h3]; ring
  rw [η_sq, h3, η_pow_four, h5, h6, h7]
  linear_combination 450 * η_mul_I_sub_one

/-- `∑ f = i(7 + 3√2)`. -/
lemma sum_fN : ∑ x : ZMod 19, fN x = I * ((7 + 3 * s2 : ℝ) : ℂ) := by
  have h := sum_η_zpow_eq (fun x : ZMod 19 => ((ex19 x : ℕ) : ℤ)) meanCount19 meanCount19_eq
  simp only [zpow_natCast] at h
  unfold fN
  refine h.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, meanCount19]
  simp
  have h3 : η ^ 3 = I * η := by rw [pow_succ, η_sq]
  rw [η_sq, h3, η_pow_four]
  linear_combination 3 * η_mul_one_add_I

/-- Real form: `H(f) = (469 − 450√2)/6859`. -/
lemma hexCorr_fN : hexCorr fN = (((469 - 450 * s2) / 6859 : ℝ) : ℂ) := by
  unfold hexCorr
  rw [hexCorr_fN_num]
  push_cast
  ring

/-- `|𝔼 f| = (7 + 3√2)/19`. -/
lemma norm_meanF_fN : ‖meanF fN‖ = (7 + 3 * s2) / 19 := by
  unfold meanF
  rw [sum_fN, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by have := s2_pos; linarith)]
  simp

lemma hexCorr_fN_neg : (hexCorr fN).re < 0 := by
  rw [hexCorr_fN, Complex.ofReal_re]
  have hs := s2_sq
  have hp := s2_pos
  have h : (450 * s2) ^ 2 = 405000 := by rw [mul_pow, hs]; norm_num
  have : 469 < 450 * s2 := by nlinarith
  linarith

lemma half_lt_meanF_fN : 1 / 2 < ‖meanF fN‖ := by
  rw [norm_meanF_fN]
  have hs := s2_sq
  have hp := s2_pos
  have : 5 / 6 < s2 := by nlinarith
  linarith

/-- **Refutation.**  Hexagon nonnegativity fails on `ℤ/19ℤ` even for `|𝔼 f| > 1/2`. -/
theorem not_hexNonnegOfLargeMean_nineteen : ¬ HexNonnegOfLargeMean 19 := by
  intro h
  have := h fN norm_fN half_lt_meanF_fN
  linarith [hexCorr_fN_neg]

/-- **Refutation.**  Hexagon nonnegativity fails on `ℤ/19ℤ`. -/
theorem not_hexNonneg_nineteen : ¬ HexNonneg 19 :=
  fun h => not_hexNonnegOfLargeMean_nineteen (hexNonnegOfLargeMean_of_hexNonneg h)

/-- Mean retention also fails on `ℤ/19ℤ` (it implies nonnegativity). -/
theorem not_meanRetention_nineteen : ¬ MeanRetention 19 := by
  intro h
  have := h fN norm_fN
  have := hexCorr_fN_neg
  have := pow_nonneg (norm_nonneg (meanF fN)) 6
  linarith

end NormalNumbers.PrimeLambert
