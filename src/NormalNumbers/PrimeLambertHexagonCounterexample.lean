import Mathlib

/-!
# Refutation of hexagon mean retention on `ℤ/7ℤ`

The cyclic hexagon correlation of `f : ZMod q → ℂ` is

  `H(f) = 𝔼_{x,a,b} f(x−a) f(x−b) f(x+a+b) · conj( f(x+a) f(x+b) f(x−a−b) )`.

The **mean-retention claim** `MeanRetention q`: for every unimodular `f`,
`|𝔼 f|^6 ≤ Re H(f)`.  (`H(f)` is always real, so `Re` loses nothing.)

This module records the exact witness of the attended addendum (2026-09-14) and proves
`¬ MeanRetention 7`: with `ζ = e^{2πi/7}` and exponents `(0,5,3,6,5,5,4)`,

* the 343 hexagon phases have residue counts `(133,0,42,63,63,42,0)` (kernel `decide`),
* the 49 pair phases of `|S|²` have counts `(13,8,7,3,3,7,8)` (kernel `decide`),
* with `c = ζ + ζ⁻¹ = 2cos(2π/7)`, `343 H = 112 − 63c − 21c²` and `|S|² = 2 + 5c + 4c²`,
* `c³ + c² − 2c − 1 = 0` and `c > 6/5`, whence `|S|^6 > 343·(343 H)`, i.e. `H < |𝔼 f|^6`.

The complex-root identification is proved, not assumed: `c` is `2cos(2π/7)` by definition and
`c > 1` comes from `2π/7 < π/3`.  The weaker claim `H(f) ≥ 0` is **not** refuted here (this
witness has `H > 0`); the `C₁₉` witness of the audit is not formalized.
-/

open Complex Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- Cyclic hexagon correlation on `ZMod q`. -/
noncomputable def hexCorr {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ℂ :=
  (∑ x : ZMod q, ∑ a : ZMod q, ∑ b : ZMod q,
      f (x - a) * f (x - b) * f (x + a + b) *
        (starRingEnd ℂ) (f (x + a) * f (x + b) * f (x - a - b))) / (q : ℂ) ^ 3

/-- Normalized mean. -/
noncomputable def meanF {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ℂ := (∑ x : ZMod q, f x) / q

/-- The (false) mean-retention conjecture on `ZMod q`. -/
def MeanRetention (q : ℕ) [NeZero q] : Prop :=
  ∀ f : ZMod q → ℂ, (∀ x, ‖f x‖ = 1) → ‖meanF f‖ ^ 6 ≤ (hexCorr f).re

/-! ### The seventh root of unity -/

/-- `ζ = exp(2πi/7)`. -/
noncomputable def ζ : ℂ := exp (2 * Real.pi * I / 7)

lemma ζ_prim : IsPrimitiveRoot ζ 7 := by
  have := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  simpa [ζ] using this

lemma ζ_pow_seven : ζ ^ 7 = 1 := ζ_prim.pow_eq_one
lemma ζ_ne_one : ζ ≠ 1 := ζ_prim.ne_one (by norm_num)
lemma ζ_ne_zero : ζ ≠ 0 := by unfold ζ; exact exp_ne_zero _

lemma ζ_sum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
  have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = ζ ^ 7 - 1 := by ring
  rw [ζ_pow_seven, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ζ_ne_one)

lemma norm_ζ : ‖ζ‖ = 1 := by
  unfold ζ
  rw [show 2 * (Real.pi : ℂ) * I / 7 = ((2 * Real.pi / 7 : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_ζ : (starRingEnd ℂ) ζ = ζ ^ 6 := by
  rw [← Complex.inv_eq_conj norm_ζ]
  have h : ζ ^ 6 * ζ = 1 := by rw [← pow_succ]; exact ζ_pow_seven
  exact inv_eq_of_mul_eq_one_left h

/-- `c = 2cos(2π/7)`. -/
noncomputable def cR : ℝ := 2 * Real.cos (2 * Real.pi / 7)

lemma cR_eq : (cR : ℂ) = ζ + ζ ^ 6 := by
  have h6 : ζ ^ 6 = exp (-(2 * Real.pi * I / 7)) := by
    rw [exp_neg]
    have h : ζ ^ 6 * ζ = 1 := by rw [← pow_succ]; exact ζ_pow_seven
    exact (inv_eq_of_mul_eq_one_left h).symm
  have e1 : ((2 * Real.pi / 7 : ℝ) : ℂ) * I = 2 * Real.pi * I / 7 := by push_cast; ring
  have e2 : -((2 * Real.pi / 7 : ℝ) : ℂ) * I = -(2 * Real.pi * I / 7) := by push_cast; ring
  unfold cR
  rw [h6, show ((2 * Real.cos (2 * Real.pi / 7) : ℝ) : ℂ) = 2 * ((Real.cos (2 * Real.pi / 7) : ℝ) : ℂ)
    by push_cast; ring, Complex.ofReal_cos, Complex.two_cos, e1, e2]
  rfl

lemma cR_cubic : cR ^ 3 + cR ^ 2 - 2 * cR - 1 = 0 := by
  have h : ((cR : ℂ)) ^ 3 + (cR : ℂ) ^ 2 - 2 * cR - 1 = 0 := by
    rw [cR_eq]
    linear_combination (ζ ^ 11 + 3 * ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + 3 * ζ + 2) * ζ_pow_seven + ζ_sum
  exact_mod_cast h

lemma cR_gt_one : 1 < cR := by
  unfold cR
  have h : Real.cos (Real.pi / 3) < Real.cos (2 * Real.pi / 7) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    nlinarith [Real.pi_pos]
  rw [Real.cos_pi_div_three] at h
  linarith

lemma cR_gt : 6 / 5 < cR := by
  have h1 := cR_gt_one
  have h := cR_cubic
  by_contra hle
  push Not at hle
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h1)]

/-! ### The witness -/

/-- Exponent table `(0,5,3,6,5,5,4)`. -/
def ex : Fin 7 → ℕ := ![0, 5, 3, 6, 5, 5, 4]

/-- The witness `f(x) = ζ^{e_x}`. -/
noncomputable def fW (x : ZMod 7) : ℂ := ζ ^ (ex x)

lemma norm_fW (x : ZMod 7) : ‖fW x‖ = 1 := by
  unfold fW; rw [norm_pow, norm_ζ, one_pow]

/-- Integer phase exponent of the hexagon term. -/
def hexE (x a b : ZMod 7) : ℤ :=
  (ex (x - a) : ℤ) + ex (x - b) + ex (x + a + b) - ex (x + a) - ex (x + b) - ex (x - a - b)

lemma conj_ζ_pow (n : ℕ) : (starRingEnd ℂ) (ζ ^ n) = ζ ^ (-(n : ℤ)) := by
  rw [map_pow, ← inv_eq_conj norm_ζ, inv_pow, ← zpow_natCast, ← zpow_neg]

lemma hex_term (x a b : ZMod 7) :
    fW (x - a) * fW (x - b) * fW (x + a + b) *
      (starRingEnd ℂ) (fW (x + a) * fW (x + b) * fW (x - a - b)) = ζ ^ hexE x a b := by
  unfold fW hexE
  rw [map_mul, map_mul, conj_ζ_pow, conj_ζ_pow, conj_ζ_pow]
  simp only [sub_eq_add_neg, zpow_add₀ ζ_ne_zero, zpow_natCast]
  ring

/-- Reduce a `zpow` of `ζ` modulo 7. -/
lemma ζ_zpow_mod (n : ℤ) : ζ ^ n = ζ ^ (n % 7).toNat := by
  have hn : n = 7 * (n / 7) + n % 7 := by omega
  have hnn : 0 ≤ n % 7 := Int.emod_nonneg n (by norm_num)
  have h7z : ζ ^ (7 : ℤ) = 1 := by exact_mod_cast ζ_pow_seven
  conv_lhs => rw [hn]
  rw [zpow_add₀ ζ_ne_zero, zpow_mul, h7z, one_zpow, one_mul]
  conv_lhs => rw [← Int.toNat_of_nonneg hnn]
  rw [zpow_natCast]

/-- Hexagon residue counts `(133,0,42,63,63,42,0)`. -/
def hexCount : Fin 7 → ℕ := ![133, 0, 42, 63, 63, 42, 0]

lemma hexCount_eq (k : Fin 7) :
    ((univ : Finset (ZMod 7 × ZMod 7 × ZMod 7)).filter
      (fun t => (hexE t.1 t.2.1 t.2.2 % 7).toNat = (k : ℕ))).card = hexCount k := by
  revert k; decide +kernel

/-- Pair residue counts `(13,8,7,3,3,7,8)`. -/
def pairCount : Fin 7 → ℕ := ![13, 8, 7, 3, 3, 7, 8]

lemma pairCount_eq (k : Fin 7) :
    ((univ : Finset (ZMod 7 × ZMod 7)).filter
      (fun t => (((ex t.1 : ℤ) - ex t.2) % 7).toNat = (k : ℕ))).card = pairCount k := by
  revert k; decide +kernel

/-- Generic fibre reduction: a sum of `ζ`-powers is the count-weighted sum over residues. -/
lemma sum_zpow_eq {ι : Type*} [Fintype ι] (E : ι → ℤ) (cnt : Fin 7 → ℕ)
    (hcnt : ∀ k : Fin 7, ((univ : Finset ι).filter (fun t => (E t % 7).toNat = (k : ℕ))).card = cnt k) :
    ∑ t, ζ ^ E t = ∑ k : Fin 7, (cnt k : ℂ) * ζ ^ (k : ℕ) := by
  have hmaps : ∀ t ∈ (univ : Finset ι), (E t % 7).toNat ∈ range 7 := by
    intro t _
    rw [mem_range]
    have h1 : E t % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
    have h2 : 0 ≤ E t % 7 := Int.emod_nonneg _ (by norm_num)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => ζ ^ E t)]
  rw [Finset.sum_range (fun k => ∑ t ∈ univ with (E t % 7).toNat = k, ζ ^ E t)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← hcnt k, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [mem_filter] at ht
  rw [ζ_zpow_mod, ht.2, Nat.cast_one, one_mul]

/-- `343 · H(f_W) = 133 + 42(ζ² + ζ⁵) + 63(ζ³ + ζ⁴)`. -/
lemma hexCorr_fW_num :
    (∑ x : ZMod 7, ∑ a : ZMod 7, ∑ b : ZMod 7,
      fW (x - a) * fW (x - b) * fW (x + a + b) *
        (starRingEnd ℂ) (fW (x + a) * fW (x + b) * fW (x - a - b)))
      = 133 + 42 * (ζ ^ 2 + ζ ^ 5) + 63 * (ζ ^ 3 + ζ ^ 4) := by
  simp_rw [hex_term]
  have h : (∑ x : ZMod 7, ∑ a : ZMod 7, ∑ b : ZMod 7, ζ ^ hexE x a b)
      = ∑ t : ZMod 7 × ZMod 7 × ZMod 7, ζ ^ hexE t.1 t.2.1 t.2.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_prod_type]
  rw [h, sum_zpow_eq _ hexCount hexCount_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hexCount]
  simp
  ring

/-- `|S|² = 13 + 8(ζ + ζ⁶) + 7(ζ² + ζ⁵) + 3(ζ³ + ζ⁴)`. -/
lemma normSq_sum_fW :
    (∑ x : ZMod 7, fW x) * (starRingEnd ℂ) (∑ x : ZMod 7, fW x)
      = 13 + 8 * (ζ + ζ ^ 6) + 7 * (ζ ^ 2 + ζ ^ 5) + 3 * (ζ ^ 3 + ζ ^ 4) := by
  rw [map_sum, Finset.sum_mul_sum]
  have h : (∑ x : ZMod 7, ∑ y : ZMod 7, fW x * (starRingEnd ℂ) (fW y))
      = ∑ t : ZMod 7 × ZMod 7, ζ ^ ((ex t.1 : ℤ) - ex t.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    unfold fW
    rw [conj_ζ_pow, sub_eq_add_neg, zpow_add₀ ζ_ne_zero, zpow_natCast]
  rw [h, sum_zpow_eq _ pairCount pairCount_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pairCount]
  simp
  ring

/-- The hexagon numerator in terms of `c`. -/
lemma hex_num_c : (133 : ℂ) + 42 * (ζ ^ 2 + ζ ^ 5) + 63 * (ζ ^ 3 + ζ ^ 4)
    = 112 - 63 * cR - 21 * (cR : ℂ) ^ 2 := by
  rw [cR_eq]
  linear_combination (21 * ζ ^ 5 + 42) * ζ_pow_seven + 63 * ζ_sum

/-- The pair numerator in terms of `c`. -/
lemma pair_num_c : (13 : ℂ) + 8 * (ζ + ζ ^ 6) + 7 * (ζ ^ 2 + ζ ^ 5) + 3 * (ζ ^ 3 + ζ ^ 4)
    = 2 + 5 * cR + 4 * (cR : ℂ) ^ 2 := by
  rw [cR_eq]
  linear_combination (-4 * ζ ^ 5 - 8) * ζ_pow_seven + 3 * ζ_sum

/-- Real form: `343 · H(f_W) = 112 − 63c − 21c²`. -/
lemma hexCorr_fW : hexCorr fW = (((112 - 63 * cR - 21 * cR ^ 2) / 343 : ℝ) : ℂ) := by
  unfold hexCorr
  rw [hexCorr_fW_num, hex_num_c]
  push_cast
  ring

/-- Real form: `|S|² = 2 + 5c + 4c²`. -/
lemma normSq_fW : normSq (∑ x : ZMod 7, fW x) = 2 + 5 * cR + 4 * cR ^ 2 := by
  have h := normSq_sum_fW
  rw [mul_conj, pair_num_c] at h
  exact_mod_cast h

/-- **Refutation.**  Mean retention fails on `ℤ/7ℤ`. -/
theorem not_meanRetention_seven : ¬ MeanRetention 7 := by
  intro h
  have hw := h fW norm_fW
  rw [hexCorr_fW, Complex.ofReal_re] at hw
  have h7 : ‖(7 : ℂ)‖ = 7 := by
    rw [show (7 : ℂ) = ((7 : ℕ) : ℂ) by norm_num, Complex.norm_natCast]; norm_num
  have hmean : ‖meanF fW‖ ^ 6 = (normSq (∑ x : ZMod 7, fW x)) ^ 3 / 7 ^ 6 := by
    unfold meanF
    rw [norm_div, normSq_eq_norm_sq]
    push_cast
    rw [h7]
    ring
  rw [hmean, normSq_fW] at hw
  have hc := cR_gt
  have hcub := cR_cubic
  have key : (2 + 5 * cR + 4 * cR ^ 2) ^ 3 - 343 * (112 - 63 * cR - 21 * cR ^ 2)
      = -37975 + 22883 * cR + 7840 * cR ^ 2
        + (64 * cR ^ 3 + 176 * cR ^ 2 + 348 * cR + 433) * (cR ^ 3 + cR ^ 2 - 2 * cR - 1) := by
    ring
  rw [hcub, mul_zero, add_zero] at key
  have hpos : 0 < -37975 + 22883 * cR + 7840 * cR ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (show (0:ℝ) < 7840 * (cR + 6 / 5) + 22883 by linarith)]
  have : (2 + 5 * cR + 4 * cR ^ 2) ^ 3 / 7 ^ 6 > (112 - 63 * cR - 21 * cR ^ 2) / 343 := by
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [key, hpos]
  linarith

end NormalNumbers.PrimeLambert
