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

end NormalNumbers.VandeheyKorobov
