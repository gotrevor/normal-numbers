/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsAnalytic
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Arithmetic input for literal pairs of Stoneham constants

This file develops the finite congruence machinery needed for the arithmetic half of the
Bailey--Borwein literal-pair theorem.  We work with ordinary integers rather than choosing an
element of `ℤ_[p]`: the compatible representatives `b^(p^K)` are the finite-level substitute for
the Teichmüller lift.
-/

namespace NormalNumbers.StonehamPairsNormal

open Finset

/-- If two integers agree modulo a prime and modulo `p^e`, taking their `p`-th powers gains one
power of `p`.  This is the finite lifting step behind the compatible Teichmüller representatives.

The geometric-sum factorization is important here: it avoids a binomial expansion and any API
for divisibility of intermediate binomial coefficients. -/
lemma prime_pow_succ_dvd_pow_sub_pow (p e : ℕ) (x y : ℤ)
    (hmod : (p : ℤ) ∣ x - y) (hpow : ((p : ℤ) ^ e) ∣ x - y) :
    ((p : ℤ) ^ (e + 1)) ∣ x ^ p - y ^ p := by
  let S : ℤ := ∑ i ∈ range p, x ^ i * y ^ (p - 1 - i)
  have hxy : x ≡ y [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨z, hz⟩ := hmod
    refine ⟨-z, ?_⟩
    rw [← neg_sub, hz]
    ring
  have hterm : ∀ i ∈ range p,
      x ^ i * y ^ (p - 1 - i) ≡ y ^ (p - 1) [ZMOD p] := by
    intro i hi
    have hip : i < p := mem_range.mp hi
    calc
      x ^ i * y ^ (p - 1 - i) ≡ y ^ i * y ^ (p - 1 - i) [ZMOD p] :=
        (hxy.pow i).mul Int.ModEq.rfl
      _ = y ^ (p - 1) := by rw [← pow_add]; congr; omega
  have hSmod : S ≡ 0 [ZMOD p] := by
    have hs := Int.ModEq.sum hterm
    dsimp only [S]
    calc
      (∑ i ∈ range p, x ^ i * y ^ (p - 1 - i))
          ≡ ∑ _i ∈ range p, y ^ (p - 1) [ZMOD p] := hs
      _ = (p : ℤ) * y ^ (p - 1) := by simp
      _ ≡ 0 [ZMOD p] := (dvd_mul_right (p : ℤ) (y ^ (p - 1))).modEq_zero_int
  have hS : (p : ℤ) ∣ S := Int.modEq_zero_iff_dvd.mp hSmod
  have hprod : (p : ℤ) * (p : ℤ) ^ e ∣ S * (x - y) := mul_dvd_mul hS hpow
  rw [show (p : ℤ) ^ (e + 1) = (p : ℤ) * (p : ℤ) ^ e by
    rw [pow_succ']]
  rw [← (Commute.all x y).geom_sum₂_mul]
  exact hprod

/-- Consecutive finite Teichmüller representatives are compatible: `b^(p^(K+1))` and
`b^(p^K)` agree modulo `p^(K+1)`.  No choice of a `p`-adic integer is needed downstream. -/
lemma teichmullerTower_dvd (p b K : ℕ) (hp : p.Prime) :
    ((p : ℤ) ^ (K + 1)) ∣
      (b : ℤ) ^ (p ^ (K + 1)) - (b : ℤ) ^ (p ^ K) := by
  induction K with
  | zero =>
      simpa using Int.prime_dvd_pow_self_sub hp (b : ℤ)
  | succ K ih =>
      have hmod : (p : ℤ) ∣
          (b : ℤ) ^ (p ^ (K + 1)) - (b : ℤ) ^ (p ^ K) :=
        (dvd_pow_self (p : ℤ) (by omega : K + 1 ≠ 0)).trans ih
      have hlift := prime_pow_succ_dvd_pow_sub_pow p (K + 1)
        ((b : ℤ) ^ (p ^ (K + 1))) ((b : ℤ) ^ (p ^ K)) hmod ih
      simpa only [pow_succ, pow_mul] using hlift

/-- Congruence form of `teichmullerTower_dvd`. -/
lemma teichmullerTower_modEq (p b K : ℕ) (hp : p.Prime) :
    (b : ℤ) ^ (p ^ (K + 1)) ≡ (b : ℤ) ^ (p ^ K) [ZMOD p ^ (K + 1)] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨z, hz⟩ := teichmullerTower_dvd p b K hp
  refine ⟨-z, ?_⟩
  rw [← neg_sub, hz]
  ring

/-- All later finite representatives reduce to the representative at level `K`. -/
lemma teichmullerTower_modEq_of_le (p b K J : ℕ) (hp : p.Prime) (hKJ : K ≤ J) :
    (b : ℤ) ^ (p ^ J) ≡ (b : ℤ) ^ (p ^ K) [ZMOD p ^ (K + 1)] := by
  induction J with
  | zero =>
      have : K = 0 := by omega
      subst K
      exact Int.ModEq.rfl
  | succ J ih =>
      by_cases htop : K = J + 1
      · subst K
        exact Int.ModEq.rfl
      · have hKJ' : K ≤ J := by omega
        have hstep := teichmullerTower_modEq p b J hp
        have hdiv : ((p : ℤ) ^ (K + 1)) ∣ (p : ℤ) ^ (J + 1) :=
          pow_dvd_pow (p : ℤ) (by omega)
        exact (hstep.of_dvd hdiv).trans (ih hKJ')

/-- The dyadic tower has one extra power of two.  This is the finite-level core of the special
`p = 2` clause in Lemma 3′: an odd base raised to `2^(K+1)` is `1` modulo `2^(K+3)`. -/
lemma twoTower_dvd (b K : ℕ) (hb : Odd b) :
    ((2 : ℤ) ^ (K + 3)) ∣ (b : ℤ) ^ (2 ^ (K + 1)) - 1 := by
  induction K with
  | zero =>
      have hbZ : Odd (b : ℤ) := by exact_mod_cast hb
      simpa using Int.eight_dvd_sq_sub_one_of_odd hbZ
  | succ K ih =>
      have hmod : (2 : ℤ) ∣ (b : ℤ) ^ (2 ^ (K + 1)) - 1 :=
        (dvd_pow_self (2 : ℤ) (by omega : K + 3 ≠ 0)).trans ih
      have hlift := prime_pow_succ_dvd_pow_sub_pow 2 (K + 3)
        ((b : ℤ) ^ (2 ^ (K + 1))) 1 hmod (by simpa using ih)
      convert hlift using 1
      · congr 1
      · rw [← pow_mul]
        congr 2

end NormalNumbers.StonehamPairsNormal
