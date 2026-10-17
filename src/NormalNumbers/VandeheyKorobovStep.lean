/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovBigM
import NormalNumbers.VandeheyKorobovCorrelation

/-!
# The squared step in Vandehey's Proposition 4.1

This file inserts the completed correlation estimate into the differencing
inequality.  The result is the display spanning pp. 12--13 of Vandehey's
proof, before Claim 4.6 and the rounded-divisor bounds are substituted.
-/

namespace NormalNumbers.VandeheyKorobov

open Finset Erdos438.Fourier

/-- The squared Proposition 4.1 estimate before the rounded divisor is
optimized.  This combines Lemma 3.1 with the full correlation aggregation;
the assumed estimate is used only at reduced moduli dividing `m`. -/
theorem norm_power_sum_sq_le_aggregated
    (b m m' N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm : m ≠ 0) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m)
    (hsupp' : m'.primeFactors = m.primeFactors)
    (hfour : 4 ∣ m → 4 ∣ m') (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (A B α γ δ ν r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbound : ∀ (q : ℕ) (c : ℤ) (L : ℕ), q ≠ 0 → q ∣ m → L ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        (A * (q : ℝ) ^ α * (L : ℝ) ^ γ +
          B * (q : ℝ) ^ (-δ) * (L : ℝ) ^ ν) *
            (1 + Real.log q) ^ r) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    let n := m / mbar
    let U := (N : ℝ) ^ γ * (1 + Real.log m) ^ r
    let V := (N : ℝ) ^ ν * (1 + Real.log m) ^ r
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ^ 2 ≤
      m' * N + 2 * m' *
        (((N : ℝ) / τ) / n *
            (A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
              B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ))) +
          (2 : ℝ) ^ P.card *
            (A * U * (Literature.VandeheyDiff.cP P α * (n : ℝ) ^ α) +
              B * V * Literature.VandeheyDiff.cP P δ)) := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  let n := m / mbar
  let U := (N : ℝ) ^ γ * (1 + Real.log m) ^ r
  let V := (N : ℝ) ^ ν * (1 + Real.log m) ^ r
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hm' : m' ≠ 0 := by
    intro hm'0
    subst m'
    simp only [zero_dvd_iff] at hm'dvd
    exact hm hm'dvd
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'
  have hbm' : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hcommon : ∀ (q : ℕ) (c : ℤ) (L : ℕ), q ≠ 0 → q ∣ m → L ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        A * (q : ℝ) ^ α * U + B * (q : ℝ) ^ (-δ) * V := by
    intro q c L hq hqdvd hLN hc
    exact two_term_bound_mono
      (∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1))) q m L N
      A B α γ δ ν r hq hm hqdvd hLN hA hB hγ hν hr
      (hbound q c L hq hqdvd hLN hc)
  have hdiff := norm_power_sum_range_sq_le_differencing_cutoff
    b m m' a N hmpos hm'pos hbm'
  have hcorr := shifted_correlation_sum_le
    b m m' N a hb hm hm'dvd hbm hsupp' hfour ha P hP hsuppm
    A B U V α δ hA hB (by positivity) (by positivity) hα hδ hδ1 hcommon
  dsimp only at hdiff hcorr ⊢
  refine hdiff.trans ?_
  gcongr

/-- All arithmetic facts about the rounded modulus needed after the squared
estimate: equations (12)--(13) and Claim 4.6, in one package. -/
theorem rounded_step_data
    (b m : ℕ) (hb : 2 ≤ b) (hm : m ≠ 0) (hbm : Nat.Coprime b m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    let m' := roundedDivisor m x
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    m' ∣ m ∧
      m'.primeFactors = m.primeFactors ∧
      (4 ∣ m → 4 ∣ m') ∧
      (m : ℝ) ^ x ≤ m' ∧
      (m' : ℝ) ≤ 2 * Literature.VandeheyDiff.primeProd P * (m : ℝ) ^ x ∧
      mbar ≤ Literature.VandeheyDiff.bigM b P * m' := by
  dsimp only
  have hsupp : m.primeFactors ⊆ P := by
    intro p hp
    exact hsuppm p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hspec := roundedDivisor_spec P (fun p hp => (hP p hp).1) hm hsupp hx0 hx1
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
    hspec.2.2.2.2, ?_⟩
  exact gcd_pow_rounded_orderOf_le_bigM_mul b hb P hP m hm hbm hsuppm x hx0 hx1

/-- Converting an exponent affine in `log N / log m` into a monomial.
This is the algebra used in equations (12)--(13) of Proposition 4.1. -/
lemma rpow_affine_log (m N u v : ℝ) (hm : 1 < m) (hN : 0 < N) :
    m ^ (u + v * (Real.log N / Real.log m)) = m ^ u * N ^ v := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hlogm : Real.log m ≠ 0 := (Real.log_pos hm).ne'
  rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hm0,
    Real.rpow_def_of_pos hN]
  rw [show Real.log m * (u + v * (Real.log N / Real.log m)) =
      Real.log m * u + Real.log N * v by field_simp]
  exact Real.exp_add _ _

lemma one_le_primeProd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (1 : ℝ) ≤ Literature.VandeheyDiff.primeProd P := by
  unfold Literature.VandeheyDiff.primeProd
  exact_mod_cast Finset.one_le_prod' fun p hp => (hP p hp).one_le

lemma one_le_bigM (b : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (1 : ℝ) ≤ Literature.VandeheyDiff.bigM b P := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (bigM_ne_zero b P hP)

lemma one_le_cP (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {x : ℝ} (hx : 0 < x) :
    1 ≤ Literature.VandeheyDiff.cP P x := by
  unfold Literature.VandeheyDiff.cP
  calc
    (1 : ℝ) = ∏ p ∈ P, (1 : ℝ) := by simp
    _ ≤ ∏ p ∈ P, (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
      apply Finset.prod_le_prod (fun _ _ => zero_le_one)
      intro p hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).two_le
      have hpow : 1 < (p : ℝ) ^ x := Real.one_lt_rpow hpR hx
      rw [le_div_iff₀ (sub_pos.mpr hpow)]
      linarith

lemma norm_power_sum_range_le (b m N : ℕ) (a : ℤ) :
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤ N := by
  calc
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤
        ∑ j ∈ range N, ‖phase m a ((b : ℤ) ^ (j + 1))‖ := norm_sum_le _ _
    _ = N := by simp [norm_phase]

lemma rounded_linear_monomial_le
    (m m' N Q α γ ν x : ℝ)
    (hm : 1 < m) (hN : 0 < N)
    (hα : 0 < α)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hm'upper : m' ≤ 2 * Q * m ^ x) :
    m' * N ^ ν ≤
      2 * Q * m ^ (α / (1 + α)) *
        N ^ ((1 + γ + α * ν) / (1 + α)) := by
  have hden : 1 + α ≠ 0 := by linarith
  have hmx :
      m ^ x = m ^ (α / (1 + α)) *
        N ^ ((1 + γ - ν) / (1 + α)) := by
    rw [hx]
    exact rpow_affine_log m N _ _ hm hN
  have hNexp :
      N ^ ((1 + γ - ν) / (1 + α)) * N ^ ν =
        N ^ ((1 + γ + α * ν) / (1 + α)) := by
    rw [← Real.rpow_add hN]
    congr 1
    field_simp
    ring
  calc
    m' * N ^ ν ≤ (2 * Q * m ^ x) * N ^ ν := by gcongr
    _ = 2 * Q * m ^ (α / (1 + α)) *
        N ^ ((1 + γ + α * ν) / (1 + α)) := by
      rw [hmx]
      calc
        2 * Q * (m ^ (α / (1 + α)) * N ^ ((1 + γ - ν) / (1 + α))) * N ^ ν =
            2 * Q * m ^ (α / (1 + α)) *
              (N ^ ((1 + γ - ν) / (1 + α)) * N ^ ν) := by ring
        _ = _ := by rw [hNexp]

lemma rounded_positive_monomial_le
    (m m' N α γ ν x : ℝ)
    (hm : 1 < m) (hm' : 0 < m') (hN : 0 < N)
    (hα : 0 < α)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hm'lower : m ^ x ≤ m') :
    (m / m') ^ α * N ^ (1 + γ) ≤
      m ^ (α / (1 + α)) *
        N ^ ((1 + γ + α * ν) / (1 + α)) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hmx0 : 0 < m ^ x := Real.rpow_pos_of_pos hm0 _
  have hden : 1 + α ≠ 0 := by linarith
  have hratio : m / m' ≤ m / m ^ x :=
    (div_le_div_iff_of_pos_left hm0 hm' hmx0).2 hm'lower
  have hpow : (m / m') ^ α ≤ (m / m ^ x) ^ α :=
    Real.rpow_le_rpow (by positivity) hratio hα.le
  have hratioPow : (m / m ^ x) ^ α = m ^ (α * (1 - x)) := by
    calc
      (m / m ^ x) ^ α = m ^ α / (m ^ x) ^ α :=
        Real.div_rpow hm0.le (Real.rpow_nonneg hm0.le _) _
      _ = m ^ α / m ^ (x * α) := by rw [Real.rpow_mul hm0.le]
      _ = m ^ (α - x * α) := (Real.rpow_sub hm0 _ _).symm
      _ = m ^ (α * (1 - x)) := by ring
  have hexp :
      α * (1 - x) = α / (1 + α) +
        (-(α * ((1 + γ - ν) / (1 + α)))) *
          (Real.log N / Real.log m) := by
    rw [hx]
    field_simp [hden]
    ring
  have hNcalc :
      -(α * ((1 + γ - ν) / (1 + α))) + (1 + γ) =
        (1 + γ + α * ν) / (1 + α) := by
    field_simp [hden]
    ring
  have hmonomial :
      (m / m ^ x) ^ α * N ^ (1 + γ) =
        m ^ (α / (1 + α)) *
          N ^ ((1 + γ + α * ν) / (1 + α)) := by
    rw [hratioPow, hexp, rpow_affine_log m N _ _ hm hN]
    calc
      m ^ (α / (1 + α)) * N ^ (-(α * ((1 + γ - ν) / (1 + α)))) *
          N ^ (1 + γ) =
          m ^ (α / (1 + α)) *
            (N ^ (-(α * ((1 + γ - ν) / (1 + α)))) * N ^ (1 + γ)) := by ring
      _ = m ^ (α / (1 + α)) *
          N ^ (-(α * ((1 + γ - ν) / (1 + α))) + (1 + γ)) := by
        rw [← Real.rpow_add hN]
      _ = _ := by rw [hNcalc]
  calc
    (m / m') ^ α * N ^ (1 + γ) ≤
        (m / m ^ x) ^ α * N ^ (1 + γ) := by gcongr
    _ = _ := hmonomial

lemma rounded_negative_monomial_le
    (m m' N Q α γ δ ν x : ℝ)
    (hm : 1 < m) (hm' : 0 < m') (hN : 0 < N) (hQ : 0 < Q)
    (hα : 0 < α) (hδ : 0 < δ)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hm'upper : m' ≤ 2 * Q * m ^ x) :
    (m / m') ^ (-δ) * N ^ (1 + ν) ≤
      2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
        N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α)) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hmx0 : 0 < m ^ x := Real.rpow_pos_of_pos hm0 _
  have hden : 1 + α ≠ 0 := by linarith
  have hneg : (m / m') ^ (-δ) = (m' / m) ^ δ := by
    rw [Real.rpow_def_of_pos (div_pos hm0 hm'),
      Real.rpow_def_of_pos (div_pos hm' hm0),
      Real.log_div hm0.ne' hm'.ne', Real.log_div hm'.ne' hm0.ne']
    congr 1
    ring
  have hratio : m' / m ≤ (2 * Q * m ^ x) / m :=
    (div_le_div_iff_of_pos_right hm0).2 hm'upper
  have hpow : (m' / m) ^ δ ≤ ((2 * Q * m ^ x) / m) ^ δ :=
    Real.rpow_le_rpow (by positivity) hratio hδ.le
  have hratioPow : (m ^ x / m) ^ δ = m ^ (δ * (x - 1)) := by
    calc
      (m ^ x / m) ^ δ = (m ^ x) ^ δ / m ^ δ :=
        Real.div_rpow (Real.rpow_nonneg hm0.le _) hm0.le _
      _ = m ^ (x * δ) / m ^ δ := by rw [Real.rpow_mul hm0.le]
      _ = m ^ (x * δ - δ) := (Real.rpow_sub hm0 _ _).symm
      _ = m ^ (δ * (x - 1)) := by ring
  have hscaled :
      ((2 * Q * m ^ x) / m) ^ δ =
        2 ^ δ * Q ^ δ * m ^ (δ * (x - 1)) := by
    rw [show (2 * Q * m ^ x) / m = (2 * Q) * (m ^ x / m) by ring]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hQ.le, hratioPow]
  have hexp :
      δ * (x - 1) = -δ / (1 + α) +
        (δ * ((1 + γ - ν) / (1 + α))) *
          (Real.log N / Real.log m) := by
    rw [hx]
    field_simp [hden]
    ring
  have hNcalc :
      δ * ((1 + γ - ν) / (1 + α)) + (1 + ν) =
        1 + ν + (1 + γ - ν) * δ / (1 + α) := by ring
  have hmonomial :
      ((2 * Q * m ^ x) / m) ^ δ * N ^ (1 + ν) =
        2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
          N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α)) := by
    rw [hscaled, hexp, rpow_affine_log m N _ _ hm hN]
    calc
      2 ^ δ * Q ^ δ *
          (m ^ (-δ / (1 + α)) * N ^ (δ * ((1 + γ - ν) / (1 + α)))) *
            N ^ (1 + ν) =
          2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
            (N ^ (δ * ((1 + γ - ν) / (1 + α))) * N ^ (1 + ν)) := by ring
      _ = 2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
          N ^ (δ * ((1 + γ - ν) / (1 + α)) + (1 + ν)) := by
        rw [← Real.rpow_add hN]
      _ = _ := by rw [hNcalc]
  calc
    (m / m') ^ (-δ) * N ^ (1 + ν) =
        (m' / m) ^ δ * N ^ (1 + ν) := by rw [hneg]
    _ ≤ ((2 * Q * m ^ x) / m) ^ δ * N ^ (1 + ν) := by gcongr
    _ = _ := hmonomial

/-- Substitution of equations (12)--(13) into the three squared terms on
page 13.  The first two terms acquire the same exponent pair and therefore
combine into the square of `A'`; the last is the square of `B'`. -/
lemma rounded_three_terms_le_two_terms
    (m m' N M Q s A B C1 C2 Ca Cd α γ δ ν L x : ℝ)
    (hm : 1 < m) (hm' : 0 < m') (hN : 0 < N) (hQ : 0 < Q)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd)
    (hL : 0 ≤ L) (hα : 0 < α) (hδ : 0 < δ)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hm'lower : m ^ x ≤ m') (hm'upper : m' ≤ 2 * Q * m ^ x) :
    (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L +
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L +
        2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L ≤
      (2 ^ (s + 2) * Q * (B * Cd + A * Ca) + 2 * Q + 2 * A * M * C1) *
          m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α)) * L +
        (2 ^ (1 + δ) * B * M * Q ^ δ * C2) *
          m ^ (-δ / (1 + α)) *
            N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α)) * L := by
  have hlin := rounded_linear_monomial_le m m' N Q α γ ν x hm hN hα hx hm'upper
  have hpos := rounded_positive_monomial_le m m' N α γ ν x hm hm' hN hα hx hm'lower
  have hneg := rounded_negative_monomial_le m m' N Q α γ δ ν x
    hm hm' hN hQ hα hδ hx hm'upper
  have hs_nonneg : 0 ≤ (2 : ℝ) ^ (s + 1) := Real.rpow_nonneg (by norm_num) _
  have hcoef0 : 0 ≤ 2 ^ (s + 1) * B * Cd + 1 := by positivity
  have hcoef1 : 0 ≤ 2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca := by positivity
  have hcoef2 : 0 ≤ 2 * B * M * C2 := by positivity
  have hs2 : (2 : ℝ) ^ (s + 2) = 2 ^ (s + 1) * 2 := by
    rw [show s + 2 = (s + 1) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have hδ2 : (2 : ℝ) ^ (1 + δ) = 2 * 2 ^ δ := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hterm0 :
      (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L ≤
        (2 ^ (s + 1) * B * Cd + 1) *
          (2 * Q * m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L := by
    calc
      (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L =
          (2 ^ (s + 1) * B * Cd + 1) * (m' * N ^ ν) * L := by ring
      _ ≤ (2 ^ (s + 1) * B * Cd + 1) *
          (2 * Q * m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hcoef0) hL
  have hterm1 :
      (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L ≤
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L := by
    calc
      (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L =
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          ((m / m') ^ α * N ^ (1 + γ)) * L := by ring
      _ ≤ (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpos hcoef1) hL
  have hterm2 :
      2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L ≤
        2 * B * M * C2 *
          (2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
            N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α))) * L := by
    calc
      2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L =
          (2 * B * M * C2) * ((m / m') ^ (-δ) * N ^ (1 + ν)) * L := by ring
      _ ≤ (2 * B * M * C2) *
          (2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
            N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α))) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hneg hcoef2) hL
  calc
    (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L +
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L +
        2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L ≤
      (2 ^ (s + 1) * B * Cd + 1) *
          (2 * Q * m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L +
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m ^ (α / (1 + α)) *
            N ^ ((1 + γ + α * ν) / (1 + α))) * L +
        2 * B * M * C2 *
          (2 ^ δ * Q ^ δ * m ^ (-δ / (1 + α)) *
            N ^ (1 + ν + (1 + γ - ν) * δ / (1 + α))) * L := by
        exact add_le_add (add_le_add hterm0 hterm1) hterm2
    _ = _ := by rw [hs2, hδ2]; ring

lemma rpow_sq_eq (x e : ℝ) (hx : 0 < x) :
    (x ^ e) ^ 2 = x ^ (2 * e) := by
  rw [pow_two, ← Real.rpow_add hx]
  congr 1
  ring

/-- Take the square root of a sum of two nonnegative monomial squares.
This packages the final `sqrt (X + Y) ≤ sqrt X + sqrt Y` step of
Proposition 4.1 while keeping all real exponents explicit. -/
lemma le_two_monomials_of_sq_le
    (z C D m N W ap gp dp vp t : ℝ)
    (hz : 0 ≤ z) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hm : 0 < m) (hN : 0 < N) (hW : 0 < W)
    (h : z ^ 2 ≤
      C * m ^ (2 * ap) * N ^ (2 * gp) * W ^ (2 * t) +
      D * m ^ (2 * dp) * N ^ (2 * vp) * W ^ (2 * t)) :
    z ≤ (Real.sqrt C * m ^ ap * N ^ gp +
      Real.sqrt D * m ^ dp * N ^ vp) * W ^ t := by
  let U := Real.sqrt C * m ^ ap * N ^ gp * W ^ t
  let V := Real.sqrt D * m ^ dp * N ^ vp * W ^ t
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hUsq : U ^ 2 = C * m ^ (2 * ap) * N ^ (2 * gp) * W ^ (2 * t) := by
    dsimp [U]
    simp only [mul_pow]
    rw [Real.sq_sqrt hC, rpow_sq_eq m ap hm, rpow_sq_eq N gp hN,
      rpow_sq_eq W t hW]
  have hVsq : V ^ 2 = D * m ^ (2 * dp) * N ^ (2 * vp) * W ^ (2 * t) := by
    dsimp [V]
    simp only [mul_pow]
    rw [Real.sq_sqrt hD, rpow_sq_eq m dp hm, rpow_sq_eq N vp hN,
      rpow_sq_eq W t hW]
  have hzsq : z ^ 2 ≤ (U + V) ^ 2 := by
    calc
      z ^ 2 ≤ U ^ 2 + V ^ 2 := by simpa only [hUsq, hVsq] using h
      _ ≤ (U + V) ^ 2 := by nlinarith [mul_nonneg hU0 hV0]
  have hzUV : z ≤ U + V := (sq_le_sq₀ hz (add_nonneg hU0 hV0)).mp hzsq
  calc
    z ≤ U + V := hzUV
    _ = (Real.sqrt C * m ^ ap * N ^ gp +
        Real.sqrt D * m ^ dp * N ^ vp) * W ^ t := by
      dsimp [U, V]
      ring

lemma one_le_step_sqrt_constants
    (b : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A B α δ : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ Real.sqrt
        ((2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
            (B * Literature.VandeheyDiff.cP P δ +
              A * Literature.VandeheyDiff.cP P α) +
          2 * Literature.VandeheyDiff.primeProd P +
          2 * A * Literature.VandeheyDiff.bigM b P *
            Literature.VandeheyDiff.cP P (1 + α)) ∧
      1 ≤ Real.sqrt
        ((2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
          (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
            Literature.VandeheyDiff.cP P (1 - δ)) := by
  have hQ : (1 : ℝ) ≤ Literature.VandeheyDiff.primeProd P := one_le_primeProd P hP
  have hM : (1 : ℝ) ≤ Literature.VandeheyDiff.bigM b P := one_le_bigM b P hP
  have hCα : (1 : ℝ) ≤ Literature.VandeheyDiff.cP P α := one_le_cP P hP hα
  have hCδ : (1 : ℝ) ≤ Literature.VandeheyDiff.cP P δ := one_le_cP P hP hδ
  have hC1 : (1 : ℝ) ≤ Literature.VandeheyDiff.cP P (1 + α) :=
    one_le_cP P hP (by linarith)
  have hC2 : (1 : ℝ) ≤ Literature.VandeheyDiff.cP P (1 - δ) :=
    one_le_cP P hP (by linarith)
  have hcoefA : 1 ≤
      (2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
          (B * Literature.VandeheyDiff.cP P δ +
            A * Literature.VandeheyDiff.cP P α) +
        2 * Literature.VandeheyDiff.primeProd P +
        2 * A * Literature.VandeheyDiff.bigM b P *
          Literature.VandeheyDiff.cP P (1 + α) := by
    have hfirst : 0 ≤
        (2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
          (B * Literature.VandeheyDiff.cP P δ +
            A * Literature.VandeheyDiff.cP P α) := by positivity
    have hlast : 0 ≤ 2 * A * Literature.VandeheyDiff.bigM b P *
        Literature.VandeheyDiff.cP P (1 + α) := by positivity
    have h2Q : (1 : ℝ) ≤ 2 * Literature.VandeheyDiff.primeProd P := by linarith
    linarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (1 + δ) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hQpow : (1 : ℝ) ≤
      (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ :=
    Real.one_le_rpow hQ hδ.le
  have hcoefB : 1 ≤
      (2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
        (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
          Literature.VandeheyDiff.cP P (1 - δ) := by
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
          (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
            Literature.VandeheyDiff.cP P (1 - δ) := by gcongr
  exact ⟨Real.one_le_sqrt.mpr hcoefA, Real.one_le_sqrt.mpr hcoefB⟩

lemma negative_step_monomial_ge_length
    (m N α γ δ ν : ℝ)
    (hm : 0 < m) (hN : 1 ≤ N) (hα : 0 < α) (hδ : 0 < δ)
    (hν : 1 ≤ ν)
    (htriv : m ≤ N ^ (1 + γ - ν)) :
    N ≤ m ^ (-δ / (2 * (1 + α))) *
      N ^ ((1 + ν) / 2 + (1 + γ - ν) * δ / (2 * (1 + α))) := by
  let dp := -δ / (2 * (1 + α))
  let vp := (1 + ν) / 2 + (1 + γ - ν) * δ / (2 * (1 + α))
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hdp : dp ≤ 0 := by
    dsimp [dp]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hpow := Real.rpow_le_rpow_of_nonpos hm htriv hdp
  rw [← Real.rpow_mul hN0.le] at hpow
  have hcalc : (1 + γ - ν) * dp + vp = (1 + ν) / 2 := by
    dsimp [dp, vp]
    field_simp
    ring
  have hmul :
      N ^ ((1 + γ - ν) * dp) * N ^ vp ≤ m ^ dp * N ^ vp := by gcongr
  have hcombine :
      N ^ ((1 + γ - ν) * dp) * N ^ vp = N ^ ((1 + ν) / 2) := by
    rw [← Real.rpow_add hN0, hcalc]
  have hNpow : N ≤ N ^ ((1 + ν) / 2) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith : (1 : ℝ) ≤ (1 + ν) / 2))
  change N ≤ m ^ dp * N ^ vp
  exact hNpow.trans (hcombine.symm.le.trans hmul)

lemma positive_step_monomial_ge_length
    (m N α γ ν x : ℝ)
    (hm : 1 < m) (hN : 1 ≤ N) (hα : 0 < α) (hν : 1 ≤ ν)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hNx : N ≤ m ^ x) :
    N ≤ m ^ (α / (2 * (1 + α))) *
      N ^ ((1 + γ + α * ν) / (2 * (1 + α))) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hsqrt := Real.rpow_le_rpow hN0.le hNx (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hmul :
      N ^ (1 / 2 : ℝ) * N ^ (ν / 2) ≤ (m ^ x) ^ (1 / 2 : ℝ) * N ^ (ν / 2) := by
    gcongr
  have hleft : N ^ (1 / 2 : ℝ) * N ^ (ν / 2) = N ^ ((1 + ν) / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hright :
      (m ^ x) ^ (1 / 2 : ℝ) * N ^ (ν / 2) =
        m ^ (α / (2 * (1 + α))) *
          N ^ ((1 + γ + α * ν) / (2 * (1 + α))) := by
    rw [← Real.rpow_mul (lt_trans zero_lt_one hm).le]
    have hexp : x * (1 / 2 : ℝ) = α / (2 * (1 + α)) +
        ((1 + γ - ν) / (2 * (1 + α))) * (Real.log N / Real.log m) := by
      rw [hx]
      field_simp
    rw [hexp, rpow_affine_log m N _ _ hm hN0]
    calc
      m ^ (α / (2 * (1 + α))) * N ^ ((1 + γ - ν) / (2 * (1 + α))) *
          N ^ (ν / 2) =
          m ^ (α / (2 * (1 + α))) *
            (N ^ ((1 + γ - ν) / (2 * (1 + α))) * N ^ (ν / 2)) := by ring
      _ = m ^ (α / (2 * (1 + α))) *
          N ^ ((1 + γ - ν) / (2 * (1 + α)) + ν / 2) := by
        rw [← Real.rpow_add hN0]
      _ = _ := by
        congr 2
        field_simp
        ring
  have hNpow : N ≤ N ^ ((1 + ν) / 2) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith : (1 : ℝ) ≤ (1 + ν) / 2))
  exact hNpow.trans (hleft.symm.le.trans (hmul.trans_eq hright))

/-- The common normalization behind both main terms in Proposition 4.1.
Writing `q = m'/mbar`, the left side is
`N * (mbar/tau) * (m/m')^e * q^(1+e)`.  Thus the same lemma handles
the positive exponent `e = α` and the negative exponent `e = -δ`. -/
lemma weighted_main_term_le
    (m m' mbar tau N M e : ℝ)
    (hm : 0 < m) (hm' : 0 < m') (hmbar : 0 < mbar) (htau : 0 < tau)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hm'bar : m' ≤ mbar) (hbar : mbar ≤ M * tau)
    (he : 0 ≤ 1 + e) :
    m' * ((N / tau) / (m / mbar)) * (m / mbar) ^ (1 + e) ≤
      M * N * (m / m') ^ e := by
  have hq0 : 0 ≤ m' / mbar := by positivity
  have hq1 : m' / mbar ≤ 1 := (div_le_one hmbar).2 hm'bar
  have hzt : mbar / tau ≤ M := by
    rw [div_le_iff₀ htau]
    simpa [mul_comm] using hbar
  have hqpow : (m' / mbar) ^ (1 + e) ≤ 1 :=
    Real.rpow_le_one hq0 hq1 he
  have hident :
      m' * ((N / tau) / (m / mbar)) * (m / mbar) ^ (1 + e) =
        N * (mbar / tau) * (m / m') ^ e * (m' / mbar) ^ (1 + e) := by
    rw [Real.rpow_add (div_pos hm hmbar) 1 e, Real.rpow_one]
    rw [show m / mbar = (m / m') * (m' / mbar) by field_simp]
    rw [Real.mul_rpow (by positivity : 0 ≤ m / m') hq0]
    rw [Real.rpow_add (div_pos hm' hmbar) 1 e, Real.rpow_one]
    field_simp
  rw [hident]
  calc
    N * (mbar / tau) * (m / m') ^ e * (m' / mbar) ^ (1 + e) ≤
        N * M * (m / m') ^ e * 1 := by gcongr
    _ = M * N * (m / m') ^ e := by ring

/-- The final algebraic collection on pp. 12--13 of Proposition 4.1.
It turns the four terms of `norm_power_sum_sq_le_aggregated` into the
paper's three squared terms, assuming the rounded-divisor and order bounds. -/
lemma aggregated_rhs_le_three_terms
    (m m' mbar tau N M Q s A B C1 C2 Ca Cd α γ δ ν L : ℝ)
    (hm : 0 < m) (hm' : 0 < m') (hmbar : 0 < mbar) (htau : 0 < tau)
    (hN : 1 ≤ N) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCa : 0 ≤ Ca)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hν : 1 ≤ ν) (hL : 1 ≤ L)
    (hm'bar : m' ≤ mbar) (hbar : mbar ≤ M * tau)
    (hm'QN : m' ≤ 2 * Q * N) :
    m' * N + 2 * m' *
        (((N / tau) / (m / mbar)) *
            (A * (N ^ γ * L) * (C1 * (m / mbar) ^ (1 + α)) +
              B * (N ^ ν * L) * (C2 * (m / mbar) ^ (1 - δ))) +
          2 ^ s *
            (A * (N ^ γ * L) * (Ca * (m / mbar) ^ α) +
              B * (N ^ ν * L) * Cd)) ≤
      (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L +
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L +
        2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L := by
  have hN0 : 0 ≤ N := hN.trans' zero_le_one
  have hL0 : 0 ≤ L := hL.trans' zero_le_one
  have hpowNγ : 0 ≤ N ^ γ := Real.rpow_nonneg hN0 _
  have hpowNν : 0 ≤ N ^ ν := Real.rpow_nonneg hN0 _
  have hpowNa : 0 ≤ (m / m') ^ α := Real.rpow_nonneg (by positivity) _
  have hpowNd : 0 ≤ (m / m') ^ (-δ) := Real.rpow_nonneg (by positivity) _
  have hNν : N ≤ N ^ ν := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hν
  have hzero :
      m' * N ≤ m' * N ^ ν * L := by
    calc
      m' * N ≤ m' * N ^ ν := by gcongr
      _ ≤ m' * N ^ ν * L := by
        nth_rewrite 1 [← mul_one (m' * N ^ ν)]
        gcongr
  have hmainA0 := weighted_main_term_le m m' mbar tau N M α hm hm' hmbar htau
    hN0 hM hm'bar hbar (by linarith)
  have hmainA :
      2 * m' * ((N / tau) / (m / mbar)) *
          (A * (N ^ γ * L) * (C1 * (m / mbar) ^ (1 + α))) ≤
        2 * A * M * C1 * (m / m') ^ α * N ^ (1 + γ) * L := by
    rw [Real.rpow_add (show 0 < N by linarith) 1 γ, Real.rpow_one]
    calc
      2 * m' * ((N / tau) / (m / mbar)) *
          (A * (N ^ γ * L) * (C1 * (m / mbar) ^ (1 + α))) =
          (2 * A * C1 * N ^ γ * L) *
            (m' * ((N / tau) / (m / mbar)) * (m / mbar) ^ (1 + α)) := by ring
      _ ≤ (2 * A * C1 * N ^ γ * L) * (M * N * (m / m') ^ α) := by
        gcongr
      _ = 2 * A * M * C1 * (m / m') ^ α * (N * N ^ γ) * L := by ring
  have hmainB0 := weighted_main_term_le m m' mbar tau N M (-δ) hm hm' hmbar htau
    hN0 hM hm'bar hbar (by linarith)
  have hmainB :
      2 * m' * ((N / tau) / (m / mbar)) *
          (B * (N ^ ν * L) * (C2 * (m / mbar) ^ (1 - δ))) ≤
        2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L := by
    rw [show (1 - δ) = 1 + (-δ) by ring]
    rw [Real.rpow_add (show 0 < N by linarith) 1 ν, Real.rpow_one]
    calc
      2 * m' * ((N / tau) / (m / mbar)) *
          (B * (N ^ ν * L) * (C2 * (m / mbar) ^ (1 + -δ))) =
          (2 * B * C2 * N ^ ν * L) *
            (m' * ((N / tau) / (m / mbar)) * (m / mbar) ^ (1 + -δ)) := by ring
      _ ≤ (2 * B * C2 * N ^ ν * L) * (M * N * (m / m') ^ (-δ)) := by
        gcongr
      _ = 2 * B * M * C2 * (m / m') ^ (-δ) * (N * N ^ ν) * L := by ring
  have hrbase : m / mbar ≤ m / m' := by
    exact div_le_div_of_nonneg_left hm.le hm' hm'bar
  have hrpow : (m / mbar) ^ α ≤ (m / m') ^ α :=
    Real.rpow_le_rpow (by positivity) hrbase hα.le
  have herrA :
      2 * m' * 2 ^ s * (A * (N ^ γ * L) * (Ca * (m / mbar) ^ α)) ≤
        2 ^ (s + 2) * A * Q * Ca * (m / m') ^ α * N ^ (1 + γ) * L := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) s 2, Real.rpow_two]
    rw [Real.rpow_add (show 0 < N by linarith) 1 γ, Real.rpow_one]
    calc
      2 * m' * 2 ^ s * (A * (N ^ γ * L) * (Ca * (m / mbar) ^ α)) ≤
          2 * (2 * Q * N) * 2 ^ s *
            (A * (N ^ γ * L) * (Ca * (m / m') ^ α)) := by gcongr
      _ = 2 ^ s * 2 ^ 2 * A * Q * Ca * (m / m') ^ α * (N * N ^ γ) * L := by ring
  have herrB :
      2 * m' * 2 ^ s * (B * (N ^ ν * L) * Cd) ≤
        2 ^ (s + 1) * B * Cd * m' * N ^ ν * L := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) s 1, Real.rpow_one]
    ring_nf
    exact le_rfl
  calc
    m' * N + 2 * m' *
        (((N / tau) / (m / mbar)) *
            (A * (N ^ γ * L) * (C1 * (m / mbar) ^ (1 + α)) +
              B * (N ^ ν * L) * (C2 * (m / mbar) ^ (1 - δ))) +
          2 ^ s *
            (A * (N ^ γ * L) * (Ca * (m / mbar) ^ α) +
              B * (N ^ ν * L) * Cd)) =
        m' * N +
          (2 * m' * ((N / tau) / (m / mbar)) *
            (A * (N ^ γ * L) * (C1 * (m / mbar) ^ (1 + α)))) +
          (2 * m' * ((N / tau) / (m / mbar)) *
            (B * (N ^ ν * L) * (C2 * (m / mbar) ^ (1 - δ)))) +
          (2 * m' * 2 ^ s * (A * (N ^ γ * L) * (Ca * (m / mbar) ^ α))) +
          (2 * m' * 2 ^ s * (B * (N ^ ν * L) * Cd)) := by ring
    _ ≤ m' * N ^ ν * L +
          (2 * A * M * C1 * (m / m') ^ α * N ^ (1 + γ) * L) +
          (2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L) +
          (2 ^ (s + 2) * A * Q * Ca * (m / m') ^ α * N ^ (1 + γ) * L) +
          (2 ^ (s + 1) * B * Cd * m' * N ^ ν * L) := by gcongr
    _ = (2 ^ (s + 1) * B * Cd + 1) * m' * N ^ ν * L +
        (2 * A * M * C1 + 2 ^ (s + 2) * A * Q * Ca) *
          (m / m') ^ α * N ^ (1 + γ) * L +
        2 * B * M * C2 * (m / m') ^ (-δ) * N ^ (1 + ν) * L := by ring

/-- Proposition 4.1's three-term squared estimate, with the rounded divisor
specialized back to natural-number data.  The order term is controlled by
Lemma 2.1 at `mbar`; Claim 4.4 identifies its order with `τ`. -/
theorem norm_power_sum_sq_le_three_terms
    (b m N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm2 : 2 ≤ m) (hm : m ≠ 0) (hbm : Nat.Coprime b m)
    (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (A B α γ δ ν r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hν0 : 0 ≤ ν) (hr : 0 ≤ r)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) (hν : 1 ≤ ν)
    (hN : 1 ≤ N)
    (hm'QN : roundedDivisor m x ≤ 2 * Literature.VandeheyDiff.primeProd P * N)
    (hbound : ∀ (q : ℕ) (c : ℤ) (L : ℕ), q ≠ 0 → q ∣ m → L ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        (A * (q : ℝ) ^ α * (L : ℝ) ^ γ +
          B * (q : ℝ) ^ (-δ) * (L : ℝ) ^ ν) *
            (1 + Real.log q) ^ r) :
    let m' := roundedDivisor m x
    let L := (1 + Real.log m) ^ r
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ^ 2 ≤
      ((2 : ℝ) ^ ((P.card : ℝ) + 1) * B *
          Literature.VandeheyDiff.cP P δ + 1) *
          (m' : ℝ) * (N : ℝ) ^ ν * L +
        (2 * A * Literature.VandeheyDiff.bigM b P *
            Literature.VandeheyDiff.cP P (1 + α) +
          (2 : ℝ) ^ ((P.card : ℝ) + 2) * A *
            Literature.VandeheyDiff.primeProd P *
              Literature.VandeheyDiff.cP P α) *
          ((m : ℝ) / m') ^ α * (N : ℝ) ^ (1 + γ) * L +
        2 * B * Literature.VandeheyDiff.bigM b P *
          Literature.VandeheyDiff.cP P (1 - δ) *
            ((m : ℝ) / m') ^ (-δ) * (N : ℝ) ^ (1 + ν) * L := by
  dsimp only
  let m' := roundedDivisor m x
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  let L := (1 + Real.log m) ^ r
  have hdata := rounded_step_data b m hb hm hbm P hP hsuppm x hx0 hx1
  dsimp only at hdata
  obtain ⟨hm'dvd, hsupp', hfour, -, -, -⟩ := hdata
  change m' ∣ m at hm'dvd
  change m'.primeFactors = m.primeFactors at hsupp'
  change 4 ∣ m → 4 ∣ m' at hfour
  have hm'0 : m' ≠ 0 := by
    dsimp [m']
    exact roundedDivisor_ne_zero m x
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'0
  have hbm' : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b m').mpr hbm').isOfFinOrder
  have hclaim := orderOf_gcd_pow_sub_one_eq_and_maximal b m m' hb hm'dvd hbm
  dsimp only at hclaim
  have hm'bar : m' ∣ mbar := hclaim.2 m' hm'dvd rfl
  have hmbar0 : mbar ≠ 0 := by
    dsimp [mbar]
    exact Nat.gcd_ne_zero_right hm
  have hmbarpos : 0 < mbar := Nat.pos_of_ne_zero hmbar0
  have hm'dvdle : m' ≤ mbar := Nat.le_of_dvd hmbarpos hm'bar
  have hm'one : m' ≠ 1 := by
    intro hm'1
    have hempty : m.primeFactors = ∅ := by
      rw [← hsupp', hm'1]
      simp
    rw [Nat.primeFactors_eq_empty] at hempty
    omega
  have hm'2 : 2 ≤ m' := by omega
  have hmbar2 : 2 ≤ mbar := hm'2.trans hm'dvdle
  have hmbardvd : mbar ∣ m := by
    dsimp [mbar]
    exact Nat.gcd_dvd_right _ _
  have hbmbar : Nat.Coprime b mbar := hbm.of_dvd_right hmbardvd
  have hsuppbar : ∀ p, p.Prime → p ∣ mbar → p ∈ P := by
    intro p hp hpdvd
    exact hsuppm p hp (hpdvd.trans hmbardvd)
  have hbarNat := le_bigM_mul_orderOf b hb P hP mbar hmbar2 hsuppbar hbmbar
  rw [hclaim.1] at hbarNat
  have hbar : (mbar : ℝ) ≤ Literature.VandeheyDiff.bigM b P * (τ : ℝ) := by
    exact_mod_cast hbarNat
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    apply Real.one_le_rpow
    · have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
      linarith
    · exact hr
  have hagg := norm_power_sum_sq_le_aggregated b m m' N a hb hm hm'dvd hbm
    hsupp' hfour ha P (fun p hp => (hP p hp).1) hsuppm
    A B α γ δ ν r hA hB hγ hν0 hr hα hδ hδ1 hbound
  dsimp only at hagg
  rw [Nat.cast_div_charZero hmbardvd] at hagg
  have hthree := aggregated_rhs_le_three_terms
    (m : ℝ) (m' : ℝ) (mbar : ℝ) (τ : ℝ) (N : ℝ)
    (Literature.VandeheyDiff.bigM b P : ℝ)
    (Literature.VandeheyDiff.primeProd P : ℝ) (P.card : ℝ)
    A B (Literature.VandeheyDiff.cP P (1 + α))
    (Literature.VandeheyDiff.cP P (1 - δ))
    (Literature.VandeheyDiff.cP P α)
    (Literature.VandeheyDiff.cP P δ) α γ δ ν L
    (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast hm'pos)
    (by exact_mod_cast hmbarpos) (by exact_mod_cast hτpos)
    (by exact_mod_cast hN) (by positivity) (by positivity) hA hB
    (cP_pos P (fun p hp => (hP p hp).1) (by linarith)).le
    (cP_pos P (fun p hp => (hP p hp).1) (by linarith)).le
    (cP_pos P (fun p hp => (hP p hp).1) hα).le
    hα hδ hδ1 hν hL (by exact_mod_cast hm'dvdle) hbar
    (by exact_mod_cast hm'QN)
  exact hagg.trans (by simpa only [Real.rpow_natCast] using hthree)

/-- The nontrivial branch of Proposition 4.1 after equations (12)--(13):
the squared sum is bounded by the two exact squared monomials defining
`A'` and `B'`. -/
theorem norm_power_sum_sq_le_two_terms
    (b m N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm2 : 2 ≤ m) (hbm : Nat.Coprime b m)
    (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (A B α γ δ ν r : ℝ)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hν0 : 0 ≤ ν) (hr : 0 ≤ r)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) (hν : 1 ≤ ν)
    (hN : 1 ≤ N)
    (hm'QN : roundedDivisor m x ≤ 2 * Literature.VandeheyDiff.primeProd P * N)
    (hbound : ∀ (q : ℕ) (c : ℤ) (T : ℕ), q ≠ 0 → q ∣ m → T ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range T, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        (A * (q : ℝ) ^ α * (T : ℝ) ^ γ +
          B * (q : ℝ) ^ (-δ) * (T : ℝ) ^ ν) *
            (1 + Real.log q) ^ r) :
    let L := (1 + Real.log m) ^ r
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ^ 2 ≤
      ((2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
          (B * Literature.VandeheyDiff.cP P δ +
            A * Literature.VandeheyDiff.cP P α) +
        2 * Literature.VandeheyDiff.primeProd P +
        2 * A * Literature.VandeheyDiff.bigM b P *
          Literature.VandeheyDiff.cP P (1 + α)) *
          (m : ℝ) ^ (α / (1 + α)) *
            (N : ℝ) ^ ((1 + γ + α * ν) / (1 + α)) * L +
      ((2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
          (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
            Literature.VandeheyDiff.cP P (1 - δ)) *
        (m : ℝ) ^ (-δ / (1 + α)) *
          (N : ℝ) ^
            (1 + ν + (1 + γ - ν) * δ / (1 + α)) * L := by
  dsimp only
  have hm : m ≠ 0 := by omega
  let m' := roundedDivisor m x
  let L := (1 + Real.log m) ^ r
  have hdata := rounded_step_data b m hb hm hbm P hP hsuppm x hx0 hx1
  dsimp only at hdata
  obtain ⟨-, -, -, hm'lower, hm'upper, -⟩ := hdata
  change (m : ℝ) ^ x ≤ (m' : ℝ) at hm'lower
  change (m' : ℝ) ≤ 2 * Literature.VandeheyDiff.primeProd P * (m : ℝ) ^ x at hm'upper
  have hm'pos : (0 : ℝ) < m' := by
    exact_mod_cast Nat.pos_of_ne_zero (roundedDivisor_ne_zero m x)
  have hQposNat : 0 < Literature.VandeheyDiff.primeProd P := by
    unfold Literature.VandeheyDiff.primeProd
    exact Finset.prod_pos fun p hp => (hP p hp).1.pos
  have hQpos : (0 : ℝ) < Literature.VandeheyDiff.primeProd P := by exact_mod_cast hQposNat
  have hL0 : 0 ≤ L := Real.rpow_nonneg (by
    have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    linarith) _
  have hthree := norm_power_sum_sq_le_three_terms b m N a hb hm2 hm hbm ha P hP hsuppm
    x hx0 hx1 A B α γ δ ν r hA hB hγ hν0 hr hα hδ hδ1 hν hN hm'QN hbound
  dsimp only at hthree
  have hround := rounded_three_terms_le_two_terms
    (m : ℝ) (m' : ℝ) (N : ℝ)
    (Literature.VandeheyDiff.bigM b P : ℝ)
    (Literature.VandeheyDiff.primeProd P : ℝ) (P.card : ℝ)
    A B (Literature.VandeheyDiff.cP P (1 + α))
    (Literature.VandeheyDiff.cP P (1 - δ))
    (Literature.VandeheyDiff.cP P α) (Literature.VandeheyDiff.cP P δ)
    α γ δ ν L x
    (by exact_mod_cast hm2) hm'pos (by exact_mod_cast hN) hQpos
    (by positivity) hA hB
    (cP_pos P (fun p hp => (hP p hp).1) (by linarith)).le
    (cP_pos P (fun p hp => (hP p hp).1) (by linarith)).le
    (cP_pos P (fun p hp => (hP p hp).1) hα).le
    (cP_pos P (fun p hp => (hP p hp).1) hδ).le
    hL0 hα hδ hx hm'lower hm'upper
  exact hthree.trans (by simpa only [Real.rpow_natCast] using hround)

/-- The nontrivial branch of Proposition 4.1 in its final, unsquared form. -/
theorem norm_power_sum_le_nontrivial
    (b m N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm2 : 2 ≤ m) (hbm : Nat.Coprime b m)
    (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (A B α γ δ ν r : ℝ)
    (hx : x = α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hν0 : 0 ≤ ν) (hr : 0 ≤ r)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) (hν : 1 ≤ ν)
    (hN : 1 ≤ N)
    (hm'QN : roundedDivisor m x ≤ 2 * Literature.VandeheyDiff.primeProd P * N)
    (hbound : ∀ (q : ℕ) (c : ℤ) (T : ℕ), q ≠ 0 → q ∣ m → T ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range T, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        (A * (q : ℝ) ^ α * (T : ℝ) ^ γ +
          B * (q : ℝ) ^ (-δ) * (T : ℝ) ^ ν) *
            (1 + Real.log q) ^ r) :
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤
      (Real.sqrt
          ((2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
              (B * Literature.VandeheyDiff.cP P δ +
                A * Literature.VandeheyDiff.cP P α) +
            2 * Literature.VandeheyDiff.primeProd P +
            2 * A * Literature.VandeheyDiff.bigM b P *
              Literature.VandeheyDiff.cP P (1 + α)) *
          (m : ℝ) ^ (α / (2 * (1 + α))) *
            (N : ℝ) ^ ((1 + γ + α * ν) / (2 * (1 + α))) +
        Real.sqrt
          ((2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
            (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
              Literature.VandeheyDiff.cP P (1 - δ)) *
          (m : ℝ) ^ (-δ / (2 * (1 + α))) *
            (N : ℝ) ^ ((1 + ν) / 2 +
              (1 + γ - ν) * δ / (2 * (1 + α)))) *
        (1 + Real.log m) ^ (r / 2) := by
  let C : ℝ :=
    (2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
        (B * Literature.VandeheyDiff.cP P δ + A * Literature.VandeheyDiff.cP P α) +
      2 * Literature.VandeheyDiff.primeProd P +
      2 * A * Literature.VandeheyDiff.bigM b P * Literature.VandeheyDiff.cP P (1 + α)
  let D : ℝ :=
    (2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
      (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
        Literature.VandeheyDiff.cP P (1 - δ)
  let W : ℝ := 1 + Real.log m
  let ap := α / (2 * (1 + α))
  let gp := (1 + γ + α * ν) / (2 * (1 + α))
  let dp := -δ / (2 * (1 + α))
  let vp := (1 + ν) / 2 + (1 + γ - ν) * δ / (2 * (1 + α))
  let t := r / 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
    have hCδ := (cP_pos P hP' hδ).le
    have hCα := (cP_pos P hP' hα).le
    have hC1 := (cP_pos P hP' (by linarith : 0 < 1 + α)).le
    positivity
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
    have hC2 := (cP_pos P hP' (by linarith : 0 < 1 - δ)).le
    positivity
  have hW : 0 < W := by
    dsimp [W]
    have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    linarith
  have hsq := norm_power_sum_sq_le_two_terms b m N a hb hm2 hbm ha P hP hsuppm
    x hx0 hx1 A B α γ δ ν r hx hA hB hγ hν0 hr hα hδ hδ1 hν hN hm'QN hbound
  dsimp only at hsq
  have hap : 2 * ap = α / (1 + α) := by dsimp [ap]; field_simp
  have hgp : 2 * gp = (1 + γ + α * ν) / (1 + α) := by dsimp [gp]; field_simp
  have hdp : 2 * dp = -δ / (1 + α) := by dsimp [dp]; field_simp
  have hvp : 2 * vp = 1 + ν + (1 + γ - ν) * δ / (1 + α) := by
    dsimp [vp]
    field_simp
  have ht : 2 * t = r := by dsimp [t]; ring
  have hsq' :
      ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ^ 2 ≤
        C * (m : ℝ) ^ (2 * ap) * (N : ℝ) ^ (2 * gp) * W ^ (2 * t) +
        D * (m : ℝ) ^ (2 * dp) * (N : ℝ) ^ (2 * vp) * W ^ (2 * t) := by
    dsimp [C, D, W]
    rw [hap, hgp, hdp, hvp, ht]
    exact hsq
  have hfinal := le_two_monomials_of_sq_le
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖
    C D (m : ℝ) (N : ℝ) W ap gp dp vp t
    (norm_nonneg _) hC0 hD0 (by positivity) (by positivity) hW hsq'
  simpa [C, D, W, ap, gp, dp, vp, t] using hfinal

/-- **Vandehey, Proposition 4.1**, in the form consumed by Theorem 5.1.
The hypothesis `1 ≤ B` removes the paper's redundant `max {sqrt …, 1}`:
for the recursive constants that square root is already at least one. -/
theorem norm_power_sum_le_step
    (b m N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm2 : 2 ≤ m) (hbm : Nat.Coprime b m)
    (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (A B α γ δ ν r : ℝ)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hν : 1 ≤ ν) (hν2 : ν ≤ 2) (hgap : ν ≤ 1 + γ)
    (hr : 0 ≤ r) (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 1 ≤ N)
    (hbound : ∀ (q : ℕ) (c : ℤ) (T : ℕ), q ≠ 0 → q ∣ m → T ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range T, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        (A * (q : ℝ) ^ α * (T : ℝ) ^ γ +
          B * (q : ℝ) ^ (-δ) * (T : ℝ) ^ ν) *
            (1 + Real.log q) ^ r) :
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤
      (Real.sqrt
          ((2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
              (B * Literature.VandeheyDiff.cP P δ +
                A * Literature.VandeheyDiff.cP P α) +
            2 * Literature.VandeheyDiff.primeProd P +
            2 * A * Literature.VandeheyDiff.bigM b P *
              Literature.VandeheyDiff.cP P (1 + α)) *
          (m : ℝ) ^ (α / (2 * (1 + α))) *
            (N : ℝ) ^ ((1 + γ + α * ν) / (2 * (1 + α))) +
        Real.sqrt
          ((2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
            (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
              Literature.VandeheyDiff.cP P (1 - δ)) *
          (m : ℝ) ^ (-δ / (2 * (1 + α))) *
            (N : ℝ) ^ ((1 + ν) / 2 +
              (1 + γ - ν) * δ / (2 * (1 + α)))) *
        (1 + Real.log m) ^ (r / 2) := by
  let C : ℝ :=
    (2 : ℝ) ^ ((P.card : ℝ) + 2) * Literature.VandeheyDiff.primeProd P *
        (B * Literature.VandeheyDiff.cP P δ + A * Literature.VandeheyDiff.cP P α) +
      2 * Literature.VandeheyDiff.primeProd P +
      2 * A * Literature.VandeheyDiff.bigM b P * Literature.VandeheyDiff.cP P (1 + α)
  let D : ℝ :=
    (2 : ℝ) ^ (1 + δ) * B * Literature.VandeheyDiff.bigM b P *
      (Literature.VandeheyDiff.primeProd P : ℝ) ^ δ *
        Literature.VandeheyDiff.cP P (1 - δ)
  let W : ℝ := 1 + Real.log m
  let ap := α / (2 * (1 + α))
  let gp := (1 + γ + α * ν) / (2 * (1 + α))
  let dp := -δ / (2 * (1 + α))
  let vp := (1 + ν) / 2 + (1 + γ - ν) * δ / (2 * (1 + α))
  let t := r / 2
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  obtain ⟨hsqrtC, hsqrtD⟩ := one_le_step_sqrt_constants b P hP' A B α δ
    hA hB hα hδ hδ1
  have hW : 1 ≤ W := by
    dsimp [W]
    have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    linarith
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hWt : 1 ≤ W ^ t := Real.one_le_rpow hW ht0
  have htrivial := norm_power_sum_range_le b m N a
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm2
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hgap0 : 0 ≤ 1 + γ - ν := by linarith
  by_cases hsize : (m : ℝ) ≤ (N : ℝ) ^ (1 + γ - ν)
  · have hmono := negative_step_monomial_ge_length (m : ℝ) (N : ℝ)
      α γ δ ν (by positivity) hNR hα hδ hν hsize
    have hBterm : (N : ℝ) ≤ Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp * W ^ t := by
      calc
        (N : ℝ) ≤ (m : ℝ) ^ dp * (N : ℝ) ^ vp := by
          simpa [dp, vp] using hmono
        _ = 1 * ((m : ℝ) ^ dp * (N : ℝ) ^ vp) * 1 := by ring
        _ ≤ Real.sqrt D * ((m : ℝ) ^ dp * (N : ℝ) ^ vp) * W ^ t := by gcongr
        _ = Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp * W ^ t := by ring
    calc
      ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤ (N : ℝ) := htrivial
      _ ≤ Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp * W ^ t := hBterm
      _ ≤ (Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp +
          Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp) * W ^ t := by
        have hfirst : 0 ≤ Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp := by
          positivity
        exact mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg (le_trans zero_le_one hW) t)
      _ = _ := by rfl
  · have hNm : (N : ℝ) ^ (1 + γ - ν) < m := lt_of_not_ge hsize
    let x : ℝ := α / (1 + α) +
      ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m)
    have hx : x = α / (1 + α) +
        ((1 + γ - ν) / (1 + α)) * (Real.log N / Real.log m) := rfl
    have hlogm : 0 < Real.log m := Real.log_pos hmR
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hlogNm : (1 + γ - ν) * Real.log N < Real.log m := by
      have hloglt := Real.log_lt_log (Real.rpow_pos_of_pos (by positivity) _) hNm
      rw [Real.log_rpow (by positivity)] at hloglt
      exact hloglt
    have hratio : (1 + γ - ν) * (Real.log N / Real.log m) < 1 := by
      calc
        (1 + γ - ν) * (Real.log N / Real.log m) =
            ((1 + γ - ν) * Real.log N) / Real.log m := by ring
        _ < 1 := (div_lt_one hlogm).2 hlogNm
    have hx1 : x < 1 := by
      dsimp [x]
      rw [show α / (1 + α) +
          (1 + γ - ν) / (1 + α) * (Real.log N / Real.log m) =
          (α + (1 + γ - ν) * (Real.log N / Real.log m)) / (1 + α) by field_simp]
      rw [div_lt_one (by linarith : 0 < 1 + α)]
      linarith
    by_cases hm'QN : roundedDivisor m x ≤
        2 * Literature.VandeheyDiff.primeProd P * N
    · exact norm_power_sum_le_nontrivial b m N a hb hm2 hbm ha P hP hsuppm
        x hx0 hx1 A B α γ δ ν r hx hA (le_trans zero_le_one hB) hγ
        (le_trans zero_le_one hν) hr hα hδ hδ1 hν hN
        hm'QN hbound
    · have hm'lt : 2 * Literature.VandeheyDiff.primeProd P * N < roundedDivisor m x :=
        Nat.lt_of_not_ge hm'QN
      have hdata := rounded_step_data b m hb (by omega) hbm P hP hsuppm x hx0 hx1
      dsimp only at hdata
      have hm'upper := hdata.2.2.2.2.1
      have hQpos : (0 : ℝ) < Literature.VandeheyDiff.primeProd P :=
        lt_of_lt_of_le zero_lt_one (one_le_primeProd P hP')
      have hNx : (N : ℝ) < (m : ℝ) ^ x := by
        have hm'ltR : (2 : ℝ) * Literature.VandeheyDiff.primeProd P * N <
            (roundedDivisor m x : ℝ) := by
          exact_mod_cast hm'lt
        have hfull : (2 : ℝ) * Literature.VandeheyDiff.primeProd P * N <
            2 * Literature.VandeheyDiff.primeProd P * (m : ℝ) ^ x :=
          hm'ltR.trans_le hm'upper
        have hfac : (0 : ℝ) < 2 * Literature.VandeheyDiff.primeProd P := by
          positivity
        exact lt_of_mul_lt_mul_left (by simpa [mul_assoc] using hfull) hfac.le
      have hmono := positive_step_monomial_ge_length (m : ℝ) (N : ℝ)
        α γ ν x hmR hNR hα hν hx hNx.le
      have hAterm : (N : ℝ) ≤ Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp * W ^ t := by
        calc
          (N : ℝ) ≤ (m : ℝ) ^ ap * (N : ℝ) ^ gp := by
            simpa [ap, gp] using hmono
          _ = 1 * ((m : ℝ) ^ ap * (N : ℝ) ^ gp) * 1 := by ring
          _ ≤ Real.sqrt C * ((m : ℝ) ^ ap * (N : ℝ) ^ gp) * W ^ t := by gcongr
          _ = Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp * W ^ t := by ring
      calc
        ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ≤ (N : ℝ) := htrivial
        _ ≤ Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp * W ^ t := hAterm
        _ ≤ (Real.sqrt C * (m : ℝ) ^ ap * (N : ℝ) ^ gp +
            Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp) * W ^ t := by
          have hsecond : 0 ≤ Real.sqrt D * (m : ℝ) ^ dp * (N : ℝ) ^ vp := by
            positivity
          exact mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (le_trans zero_le_one hW) t)
        _ = _ := by rfl

end NormalNumbers.VandeheyKorobov
