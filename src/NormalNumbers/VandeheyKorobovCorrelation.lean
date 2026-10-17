/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovAggregation

/-!
# Correlation estimate in Vandehey's Proposition 4.1

This file connects the exact shifted-coefficient reduction to the sharp-cutoff
gcd-class aggregation.  It is the calculation on pp. 12--13 of Vandehey's
proof, before Claim 4.6 and the rounded-divisor estimates are substituted.
-/

namespace NormalNumbers.VandeheyKorobov

open Finset Erdos438.Fourier

/-- Replace a correlation length and its reduced modulus logarithm by the
ambient bounds `L ≤ N` and `q ∣ m`. -/
lemma two_term_bound_mono
    (z : ℂ) (q m L N : ℕ) (A B α γ δ ν r : ℝ)
    (hq : q ≠ 0) (hm : m ≠ 0) (hqdvd : q ∣ m) (hLN : L ≤ N)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (hz : ‖z‖ ≤
      (A * (q : ℝ) ^ α * (L : ℝ) ^ γ + B * (q : ℝ) ^ (-δ) * (L : ℝ) ^ ν) *
        (1 + Real.log q) ^ r) :
    ‖z‖ ≤
      A * (q : ℝ) ^ α * ((N : ℝ) ^ γ * (1 + Real.log m) ^ r) +
        B * (q : ℝ) ^ (-δ) * ((N : ℝ) ^ ν * (1 + Real.log m) ^ r) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hqm : q ≤ m := Nat.le_of_dvd hmpos hqdvd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqmR : (q : ℝ) ≤ m := by exact_mod_cast hqm
  have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hLpow : (L : ℝ) ^ γ ≤ (N : ℝ) ^ γ :=
    Real.rpow_le_rpow (by positivity) hLNR hγ
  have hNpow : (L : ℝ) ^ ν ≤ (N : ℝ) ^ ν :=
    Real.rpow_le_rpow (by positivity) hLNR hν
  have hlog : Real.log q ≤ Real.log m := Real.log_le_log hqR hqmR
  have hlogq0 : 0 ≤ 1 + Real.log q := by
    have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hqpos)
    linarith
  have hlogpow : (1 + Real.log q) ^ r ≤ (1 + Real.log m) ^ r :=
    Real.rpow_le_rpow hlogq0 (by linarith) hr
  calc
    ‖z‖ ≤
        (A * (q : ℝ) ^ α * (L : ℝ) ^ γ + B * (q : ℝ) ^ (-δ) * (L : ℝ) ^ ν) *
          (1 + Real.log q) ^ r := hz
    _ = A * (q : ℝ) ^ α * ((L : ℝ) ^ γ * (1 + Real.log q) ^ r) +
          B * (q : ℝ) ^ (-δ) * ((L : ℝ) ^ ν * (1 + Real.log q) ^ r) := by ring
    _ ≤ A * (q : ℝ) ^ α * ((N : ℝ) ^ γ * (1 + Real.log m) ^ r) +
          B * (q : ℝ) ^ (-δ) * ((N : ℝ) ^ ν * (1 + Real.log m) ^ r) := by
      gcongr

/-- The shifted correlations in Proposition 4.1, summed through the exact
ceiling cutoff and collapsed to the four divisor sums from Lemma 4.2.

The hypothesis `hbound` is the input exponential-sum estimate after replacing
the two correlation-length powers and the logarithmic factor by common
majorants `U` and `V`.  A later wrapper obtains it from Proposition 4.1's
display (9). -/
theorem shifted_correlation_sum_le
    (b m m' N : ℕ) (a : ℤ)
    (hb : 2 ≤ b) (hm : m ≠ 0) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m)
    (hsupp' : m'.primeFactors = m.primeFactors)
    (hfour : 4 ∣ m → 4 ∣ m') (ha : IsCoprime a (m : ℤ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsuppm : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (A B U V α δ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbound : ∀ (q : ℕ) (c : ℤ) (L : ℕ), q ≠ 0 → q ∣ m → L ≤ N →
      IsCoprime c (q : ℤ) →
      ‖∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1))‖ ≤
        A * (q : ℝ) ^ α * U + B * (q : ℝ) ^ (-δ) * V) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    let n := m / mbar
    (∑ i ∈ Ico 1 (N ⌈/⌉ τ),
        ‖∑ j ∈ range (N - i * τ),
          phase m (a * ((b : ℤ) ^ (i * τ) - 1))
            ((b : ℤ) ^ (j + 1))‖) ≤
      ((N : ℝ) / τ) / n *
          (A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
            B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ))) +
        (2 : ℝ) ^ P.card *
          (A * U * (Literature.VandeheyDiff.cP P α * (n : ℝ) ^ α) +
            B * V * Literature.VandeheyDiff.cP P δ) := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  let n := m / mbar
  have hm' : m' ≠ 0 := by
    intro hm'0
    subst m'
    simp only [zero_dvd_iff] at hm'dvd
    exact hm hm'dvd
  have hbm' : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτ : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b m').mpr hbm').isOfFinOrder
  have hmbar : mbar ≠ 0 := by
    dsimp [mbar]
    exact (Nat.gcd_pos_of_pos_right (b ^ τ - 1) (Nat.pos_of_ne_zero hm)).ne'
  have hmbardvd : mbar ∣ m := by
    dsimp [mbar]
    exact Nat.gcd_dvd_right _ _
  have hn : n ≠ 0 := by
    dsimp [n]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hmbardvd)
      (Nat.pos_of_ne_zero hmbar)).ne'
  have hndvd : n ∣ m := by
    dsimp [n]
    exact Nat.div_dvd_of_dvd hmbardvd
  have hsuppn : n.primeFactors ⊆ P := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    exact hsuppm p hpprime (hpn.trans hndvd)
  have hcard : n.primeFactors.card ≤ P.card := Finset.card_le_card hsuppn
  have hterm (i : ℕ) (hi : i ∈ Ico 1 (N ⌈/⌉ τ)) :
      ‖∑ j ∈ range (N - i * τ),
          phase m (a * ((b : ℤ) ^ (i * τ) - 1))
            ((b : ℤ) ^ (j + 1))‖ ≤
        A * ((n / Nat.gcd i n : ℕ) : ℝ) ^ α * U +
          B * ((n / Nat.gcd i n : ℕ) : ℝ) ^ (-δ) * V := by
    let d := Nat.gcd i n
    let q := n / d
    let c : ℤ := (a * ((b : ℤ) ^ (i * τ) - 1)) / (mbar * d : ℕ)
    let L := N - i * τ
    have hdvd : d ∣ n := by
      dsimp [d]
      exact Nat.gcd_dvd_right i n
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
    have hq : q ≠ 0 := by
      dsimp [q]
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdpos).ne'
    have hqdvd : q ∣ m := by
      have hqn : q ∣ n := by
        dsimp [q]
        exact Nat.div_dvd_of_dvd hdvd
      exact hqn.trans hndvd
    have hqeq : m / (mbar * d) = q := by
      dsimp [q, n]
      exact (Nat.div_div_eq_div_mul m mbar d).symm
    have hred (j : ℕ) :
        phase m (a * ((b : ℤ) ^ (i * τ) - 1)) ((b : ℤ) ^ (j + 1)) =
            phase q c ((b : ℤ) ^ (j + 1)) ∧
          IsCoprime c (q : ℤ) := by
      have h := shifted_phase_reduce b m m' a i j hb hm hm'dvd hbm hsupp' hfour ha
      dsimp only at h
      change
        phase m (a * ((b : ℤ) ^ (i * τ) - 1)) ((b : ℤ) ^ (j + 1)) =
            phase (m / (mbar * d))
              ((a * ((b : ℤ) ^ (i * τ) - 1)) / (mbar * d : ℕ))
              ((b : ℤ) ^ (j + 1)) ∧
          IsCoprime ((a * ((b : ℤ) ^ (i * τ) - 1)) / (mbar * d : ℕ))
            ((m / (mbar * d) : ℕ) : ℤ) at h
      rw [hqeq] at h
      simpa only [c] using h
    have hsum :
        (∑ j ∈ range L,
            phase m (a * ((b : ℤ) ^ (i * τ) - 1)) ((b : ℤ) ^ (j + 1))) =
          ∑ j ∈ range L, phase q c ((b : ℤ) ^ (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hred j).1
    rw [show N - i * τ = L by rfl, hsum]
    simpa only [q, d] using hbound q c L hq hqdvd (Nat.sub_le N (i * τ)) (hred 0).2
  have hsum :
      (∑ i ∈ Ico 1 (N ⌈/⌉ τ),
          ‖∑ j ∈ range (N - i * τ),
            phase m (a * ((b : ℤ) ^ (i * τ) - 1))
              ((b : ℤ) ^ (j + 1))‖) ≤
        ∑ i ∈ Ico 1 (N ⌈/⌉ τ),
          (A * ((n / Nat.gcd i n : ℕ) : ℝ) ^ α * U +
            B * ((n / Nat.gcd i n : ℕ) : ℝ) ^ (-δ) * V) := by
    exact Finset.sum_le_sum fun i hi => hterm i hi
  refine hsum.trans ?_
  exact sum_Ico_gcd_two_rpow_le_of_cutoff P hP hn hsuppn (N ⌈/⌉ τ) P.card hcard
    A B U V α δ ((N : ℝ) / τ) hA hB hU hV hα hδ hδ1
    (natCast_ceilDiv_sub_one_le_div N τ hτ)

end NormalNumbers.VandeheyKorobov
