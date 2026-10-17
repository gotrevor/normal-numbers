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

end NormalNumbers.VandeheyKorobov
