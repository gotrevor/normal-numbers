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

/-! ### The exponent form of the finite Teichmüller congruence -/

/-- Raising compatible finite Teichmüller representatives to the same unit-part exponent
preserves their compatibility.  This is the form used after splitting a Stoneham exponent into
its `p`-power and prime-to-`p` parts. -/
lemma teichmullerTower_power_modEq_of_le (p b K J u : ℕ)
    (hp : p.Prime) (hKJ : K ≤ J) :
    (b : ℤ) ^ (p ^ J * u) ≡
      ((b : ℤ) ^ (p ^ K)) ^ u [ZMOD p ^ (K + 1)] := by
  simpa only [pow_mul] using (teichmullerTower_modEq_of_le p b K J hp hKJ).pow u

/-- Finite-level item (K) in the exact exponent shape of one Stoneham family.  If
`c = p^a u`, then at every later kick `j ≥ k`, the phase `b^(c^j)` is represented modulo
`p^(ak+1)` by the fixed level-`ak` representative raised to `u^j`.  No coprimality hypothesis on
`u` is needed for this congruence; downstream uses choose `a` to be the exact `p`-valuation. -/
lemma teichmullerPower_modEq_of_factor (p b c a u k j : ℕ)
    (hp : p.Prime) (hc : c = p ^ a * u) (hkj : k ≤ j) :
    (b : ℤ) ^ (c ^ j) ≡
      ((b : ℤ) ^ (p ^ (a * k))) ^ (u ^ j) [ZMOD p ^ (a * k + 1)] := by
  have hlevel : a * k ≤ a * j := Nat.mul_le_mul_left a hkj
  have hcj : c ^ j = p ^ (a * j) * u ^ j := by
    rw [hc, mul_pow, ← pow_mul]
  rw [hcj]
  exact teichmullerTower_power_modEq_of_le p b (a * k) (a * j) (u ^ j) hp hlevel

/-- The preceding congruence with mathlib's canonical `p`-part and complementary part of `c`.
This is the form downstream Stoneham arguments can invoke without first choosing a factorization. -/
lemma teichmullerPower_modEq (p b c k j : ℕ) (hp : p.Prime) (hkj : k ≤ j) :
    (b : ℤ) ^ (c ^ j) ≡
      ((b : ℤ) ^ (p ^ (c.factorization p * k))) ^ (ordCompl[p] c ^ j)
        [ZMOD p ^ (c.factorization p * k + 1)] := by
  exact teichmullerPower_modEq_of_factor p b c (c.factorization p) (ordCompl[p] c)
    k j hp (Nat.ordProj_mul_ordCompl_eq_self c p).symm hkj

/-- Dyadic item (K): an odd base raised to an exponent divisible by `2^K` is `1` modulo
`2^(K+2)`, for `K ≥ 1`. -/
lemma twoPower_modEq_one (b K u : ℕ) (hb : Odd b) (hK : 1 ≤ K) :
    (b : ℤ) ^ (2 ^ K * u) ≡ 1 [ZMOD 2 ^ (K + 2)] := by
  have hbase : (b : ℤ) ^ (2 ^ K) ≡ 1 [ZMOD 2 ^ (K + 2)] := by
    have hdiv := twoTower_dvd b (K - 1) hb
    rw [Int.modEq_iff_dvd]
    obtain ⟨z, hz⟩ := hdiv
    refine ⟨-z, ?_⟩
    rw [show K - 1 + 3 = K + 2 by omega,
      show K - 1 + 1 = K by omega] at hz
    rw [← neg_sub, hz]
    ring
  simpa only [pow_mul, one_pow] using hbase.pow u

/-- Dyadic item (K) specialized to a Stoneham exponent.  When `c = 2^a u` with `a,j ≥ 1`,
the phase `b^(c^j)` is `1` modulo the full `2^(aj+2)` precision supplied by lifting. -/
lemma twoPower_modEq_one_of_factor (b c a u j : ℕ)
    (hb : Odd b) (ha : 1 ≤ a) (hj : 1 ≤ j) (hc : c = 2 ^ a * u) :
    (b : ℤ) ^ (c ^ j) ≡ 1 [ZMOD 2 ^ (a * j + 2)] := by
  have hlevel : 1 ≤ a * j := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by omega) (by omega))
  have hcj : c ^ j = 2 ^ (a * j) * u ^ j := by
    rw [hc, mul_pow, ← pow_mul]
  rw [hcj]
  exact twoPower_modEq_one b (a * j) (u ^ j) hb hlevel

/-- Canonical-factorization form of the dyadic clause. -/
lemma twoPower_modEq_one_of_even (b c j : ℕ) (hb : Odd b) (hc0 : c ≠ 0)
    (hc : 2 ∣ c) (hj : 1 ≤ j) :
    (b : ℤ) ^ (c ^ j) ≡ 1 [ZMOD 2 ^ (c.factorization 2 * j + 2)] := by
  have ha : 1 ≤ c.factorization 2 :=
    ((by norm_num : Nat.Prime 2).dvd_iff_one_le_factorization hc0).mp hc
  exact twoPower_modEq_one_of_factor b c (c.factorization 2) (ordCompl[2] c) j hb ha hj
    (Nat.ordProj_mul_ordCompl_eq_self c 2).symm

/-- Polar-phase form of finite item (K).  Multiplying the entered phase `b^(n-c^j)` by its
finite Teichmüller representative recovers `b^n` modulo `p^(ak+1)`.  This avoids introducing an
inverse in `ℤ / p^(ak+1)ℤ`, which keeps the later cleared-numerator argument integral. -/
lemma stonehamPhase_mul_teichmuller_modEq_of_factor (p b c a u k j n : ℕ)
    (hp : p.Prime) (hc : c = p ^ a * u) (hkj : k ≤ j) (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) * ((b : ℤ) ^ (p ^ (a * k))) ^ (u ^ j) ≡
      (b : ℤ) ^ n [ZMOD p ^ (a * k + 1)] := by
  have hphase := (teichmullerPower_modEq_of_factor p b c a u k j hp hc hkj).symm
    |>.mul_left ((b : ℤ) ^ (n - c ^ j))
  calc
    (b : ℤ) ^ (n - c ^ j) * ((b : ℤ) ^ (p ^ (a * k))) ^ (u ^ j) ≡
        (b : ℤ) ^ (n - c ^ j) * (b : ℤ) ^ (c ^ j)
          [ZMOD p ^ (a * k + 1)] := hphase
    _ = (b : ℤ) ^ n := by rw [← pow_add]; congr; omega

/-- Canonical-factorization version of the integral polar-phase congruence. -/
lemma stonehamPhase_mul_teichmuller_modEq (p b c k j n : ℕ)
    (hp : p.Prime) (hkj : k ≤ j) (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) *
        ((b : ℤ) ^ (p ^ (c.factorization p * k))) ^ (ordCompl[p] c ^ j) ≡
      (b : ℤ) ^ n [ZMOD p ^ (c.factorization p * k + 1)] := by
  exact stonehamPhase_mul_teichmuller_modEq_of_factor p b c (c.factorization p)
    (ordCompl[p] c) k j n hp (Nat.ordProj_mul_ordCompl_eq_self c p).symm hkj hentered

/-- All entered phases can be compared using the *top-level* finite Teichmüller
representative.  Clearing the `j`-th denominator by `c^(K-j)` upgrades the
`p^(a*j+1)` phase congruence to the common numerator precision `p^(a*K+1)`.

This is the finite polar decomposition in the exact form needed for a full
Stoneham-family numerator: the representative is independent of `j`, while
the residual exponent `u^j` is eventually periodic modulo every finite order. -/
lemma stonehamPhase_mul_topTeichmuller_modEq_of_factor
    (p b c a u j K n : ℕ) (hp : p.Prime) (hc : c = p ^ a * u)
    (hjK : j ≤ K) (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) *
          ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ j) * (c : ℤ) ^ (K - j) ≡
      (b : ℤ) ^ n * (c : ℤ) ^ (K - j) [ZMOD p ^ (a * K + 1)] := by
  have hlevel : a * j ≤ a * K := Nat.mul_le_mul_left a hjK
  have hcj : c ^ j = p ^ (a * j) * u ^ j := by
    rw [hc, mul_pow, ← pow_mul]
  have hphase :
      (b : ℤ) ^ (n - c ^ j) *
          ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ j) ≡
        (b : ℤ) ^ n [ZMOD p ^ (a * j + 1)] := by
    have hrep := teichmullerTower_power_modEq_of_le
      p b (a * j) (a * K) (u ^ j) hp hlevel
    have hmul := hrep.mul_left ((b : ℤ) ^ (n - c ^ j))
    calc
      (b : ℤ) ^ (n - c ^ j) *
            ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ j) ≡
          (b : ℤ) ^ (n - c ^ j) * (b : ℤ) ^ (p ^ (a * j) * u ^ j)
            [ZMOD p ^ (a * j + 1)] := by simpa only [pow_mul] using hmul
      _ = (b : ℤ) ^ n := by
        rw [← hcj, ← pow_add, tsub_add_cancel_of_le hentered]
  rw [Int.modEq_iff_dvd] at hphase ⊢
  have hAK : a * K = a * j + a * (K - j) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hjK]
  rw [show a * K + 1 = (a * j + 1) + a * (K - j) by omega, pow_add]
  have hfactor : (p : ℤ) ^ (a * (K - j)) ∣ (c : ℤ) ^ (K - j) := by
    rw [hc]
    push_cast
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_right ((p : ℤ) ^ (a * (K - j))) ((u : ℤ) ^ (K - j))
  simpa only [sub_mul] using mul_dvd_mul hphase hfactor

/-- Canonical-factorization form of the common-precision polar congruence. -/
lemma stonehamPhase_mul_topTeichmuller_modEq
    (p b c j K n : ℕ) (hp : p.Prime) (hjK : j ≤ K) (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) *
          ((b : ℤ) ^ (p ^ (c.factorization p * K))) ^ (ordCompl[p] c ^ j) *
          (c : ℤ) ^ (K - j) ≡
      (b : ℤ) ^ n * (c : ℤ) ^ (K - j)
        [ZMOD p ^ (c.factorization p * K + 1)] := by
  exact stonehamPhase_mul_topTeichmuller_modEq_of_factor p b c
    (c.factorization p) (ordCompl[p] c) j K n hp
    (Nat.ordProj_mul_ordCompl_eq_self c p).symm hjK hentered

/-- Assemble the termwise polar congruences after multiplying the cleared
family numerator by a common factor `Q`.  The hypothesis `hQ` records the
factorization `Q = W_j R_j`, where `W_j` is the `j`-th polar unit.  Taking
`Q` to be the product of all `W_j` makes `R_j` the product with the `j`-th
factor deleted, and turns the right side into the finite periodic polar
coefficient used in Lemma 3′. -/
lemma stonehamClearedFamily_mul_polar_modEq_of_factor
    (p b c a u K n : ℕ) (Q : ℤ) (R : ℕ → ℤ)
    (hp : p.Prime) (hc : c = p ^ a * u)
    (hentered : ∀ j ∈ Icc 1 K, c ^ j ≤ n)
    (hQ : ∀ j ∈ Icc 1 K,
      Q = ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ j) * R j) :
    ∑ j ∈ Icc 1 K,
        (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) * Q ≡
      ∑ j ∈ Icc 1 K,
        (b : ℤ) ^ n * (c : ℤ) ^ (K - j) * R j
          [ZMOD p ^ (a * K + 1)] := by
  apply Int.ModEq.sum
  intro j hj
  have hterm := stonehamPhase_mul_topTeichmuller_modEq_of_factor
    p b c a u j K n hp hc (mem_Icc.mp hj).2 (hentered j hj)
  have hscaled := hterm.mul_right (R j)
  rw [hQ j hj]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Product specialization of `stonehamClearedFamily_mul_polar_modEq_of_factor`.
It supplies the common multiplier canonically, so no modular inverses or
division in `ZMod` remain in the later noncancellation argument. -/
lemma stonehamClearedFamily_mul_polarProduct_modEq_of_factor
    (p b c a u K n : ℕ) (hp : p.Prime) (hc : c = p ^ a * u)
    (hentered : ∀ j ∈ Icc 1 K, c ^ j ≤ n) :
    ∑ j ∈ Icc 1 K,
          (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) *
            (∏ t ∈ Icc 1 K,
              ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ t)) ≡
      ∑ j ∈ Icc 1 K,
          (b : ℤ) ^ n * (c : ℤ) ^ (K - j) *
            (∏ t ∈ (Icc 1 K).erase j,
              ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ t))
        [ZMOD p ^ (a * K + 1)] := by
  classical
  apply stonehamClearedFamily_mul_polar_modEq_of_factor p b c a u K n
    (∏ t ∈ Icc 1 K, ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ t))
    (fun j => ∏ t ∈ (Icc 1 K).erase j,
      ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ t)) hp hc hentered
  intro j hj
  exact (Finset.mul_prod_erase (Icc 1 K)
    (fun t => ((b : ℤ) ^ (p ^ (a * K))) ^ (u ^ t)) hj).symm

/-! ### The finite polar exponent and its eventual period -/

/-- Exponent of the full product of finite polar factors. -/
def stonehamPolarExponent (u K : ℕ) : ℕ :=
  ∑ t ∈ Icc 1 K, u ^ t

/-- Exponent of the common finite Teichmüller representative after deleting the
`j`-th polar factor.  This is the exponent hidden in the product on the right of
`stonehamClearedFamily_mul_polarProduct_modEq_of_factor`. -/
def stonehamPolarDeletedExponent (u K j : ℕ) : ℕ :=
  ∑ t ∈ (Icc 1 K).erase j, u ^ t

/-- The product-deleted polar factor is a single power.  Exposing this exponent
is what permits the finite periodicity argument, without choosing a root of
unity or introducing division in `ZMod`. -/
lemma stoneham_polarProduct_erase_eq_pow (w : ℤ) (u K j : ℕ) :
    ∏ t ∈ (Icc 1 K).erase j, w ^ (u ^ t) =
      w ^ stonehamPolarDeletedExponent u K j := by
  exact Finset.prod_pow_eq_pow_sum ((Icc 1 K).erase j) (fun t => u ^ t) w

/-- The common multiplier on the left side is likewise one explicit power. -/
lemma stoneham_polarProduct_eq_pow (w : ℤ) (u K : ℕ) :
    ∏ t ∈ Icc 1 K, w ^ (u ^ t) = w ^ stonehamPolarExponent u K := by
  exact Finset.prod_pow_eq_pow_sum (Icc 1 K) (fun t => u ^ t) w

/-- Restoring the deleted exponent gives the full geometric exponent sum. -/
lemma stonehamPolarDeletedExponent_add (u K j : ℕ) (hj : j ∈ Icc 1 K) :
    stonehamPolarDeletedExponent u K j + u ^ j = stonehamPolarExponent u K := by
  exact Finset.sum_erase_add (Icc 1 K) (fun t => u ^ t) hj

/-- Power-normalized version of the full-history polar congruence.  Both large
products have disappeared: the right side now visibly depends on `j` only
through `stonehamPolarDeletedExponent`, whose fixed top offsets are eventually
periodic by `exists_eventually_modEq_stonehamPolarDeletedExponent`. -/
lemma stonehamClearedFamily_mul_polarPower_modEq_of_factor
    (p b c a u K n : ℕ) (hp : p.Prime) (hc : c = p ^ a * u)
    (hentered : ∀ j ∈ Icc 1 K, c ^ j ≤ n) :
    ∑ j ∈ Icc 1 K,
          (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) *
            ((b : ℤ) ^ (p ^ (a * K))) ^ stonehamPolarExponent u K ≡
      ∑ j ∈ Icc 1 K,
          (b : ℤ) ^ n * (c : ℤ) ^ (K - j) *
            ((b : ℤ) ^ (p ^ (a * K))) ^ stonehamPolarDeletedExponent u K j
        [ZMOD p ^ (a * K + 1)] := by
  simpa only [← stoneham_polarProduct_eq_pow, ← stoneham_polarProduct_erase_eq_pow] using
    stonehamClearedFamily_mul_polarProduct_modEq_of_factor p b c a u K n hp hc hentered

/-- Powers and their running geometric sums are eventually periodic modulo any
positive modulus.  The pair is used rather than powers alone because deleting
one factor from the polar product leaves the running sum of all the others.

This is the finite, non-coprime form required by referee repair 2: no Euler
theorem is used, so the result includes the genuinely preperiodic case
`gcd u d > 1`. -/
lemma exists_eventually_modEq_pow_and_geomSum (u d : ℕ) (hd : 0 < d) :
    ∃ K₀ T : ℕ, 0 < T ∧ ∀ K, K₀ ≤ K →
      u ^ (K + T) ≡ u ^ K [MOD d] ∧
      (∑ t ∈ Icc 1 (K + T), u ^ t) ≡ (∑ t ∈ Icc 1 K, u ^ t) [MOD d] := by
  let state : Fin (d * d + 1) → Fin d × Fin d := fun K =>
    (⟨u ^ (K : ℕ) % d, Nat.mod_lt _ hd⟩,
      ⟨(∑ t ∈ Icc 1 (K : ℕ), u ^ t) % d, Nat.mod_lt _ hd⟩)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt state (by simp)
  have propagate : ∀ i j : ℕ, i < j →
      (u ^ i ≡ u ^ j [MOD d] ∧
        (∑ t ∈ Icc 1 i, u ^ t) ≡ (∑ t ∈ Icc 1 j, u ^ t) [MOD d]) →
      ∀ K, i ≤ K →
        u ^ (K + (j - i)) ≡ u ^ K [MOD d] ∧
        (∑ t ∈ Icc 1 (K + (j - i)), u ^ t) ≡
          (∑ t ∈ Icc 1 K, u ^ t) [MOD d] := by
    intro i j hij hstart K hiK
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hiK
    induction q with
    | zero =>
        have hji : i + (j - i) = j := by omega
        simpa only [Nat.add_zero, hji] using And.intro hstart.1.symm hstart.2.symm
    | succ q ih =>
        have ih' := ih (by omega)
        have hpow : u ^ (i + q + (j - i) + 1) ≡ u ^ (i + q + 1) [MOD d] := by
          rw [pow_succ, pow_succ]
          exact ih'.1.mul Nat.ModEq.rfl
        have hsum :
            (∑ t ∈ Icc 1 (i + (q + 1) + (j - i)), u ^ t) ≡
              (∑ t ∈ Icc 1 (i + (q + 1)), u ^ t) [MOD d] := by
          rw [show i + (q + 1) + (j - i) = (i + q + (j - i)) + 1 by omega,
            show i + (q + 1) = i + q + 1 by omega,
            sum_Icc_succ_top (by omega) (fun t => u ^ t),
            sum_Icc_succ_top (by omega) (fun t => u ^ t)]
          exact ih'.2.add hpow
        refine ⟨?_, hsum⟩
        rw [show i + (q + 1) + (j - i) = i + q + (j - i) + 1 by omega,
          show i + (q + 1) = i + q + 1 by omega]
        exact hpow
  have hstateEq :
      u ^ (i : ℕ) % d = u ^ (j : ℕ) % d ∧
        (∑ t ∈ Icc 1 (i : ℕ), u ^ t) % d =
          (∑ t ∈ Icc 1 (j : ℕ), u ^ t) % d := by
    simpa only [state, Prod.mk.injEq, Fin.mk.injEq] using heq
  have hstate :
      u ^ (i : ℕ) ≡ u ^ (j : ℕ) [MOD d] ∧
        (∑ t ∈ Icc 1 (i : ℕ), u ^ t) ≡
          (∑ t ∈ Icc 1 (j : ℕ), u ^ t) [MOD d] := hstateEq
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hgt
  · refine ⟨i, j - i, by omega, fun K hK => ?_⟩
    have h := propagate i j hlt hstate K hK
    exact h
  · refine ⟨j, i - j, by omega, fun K hK => ?_⟩
    have h := propagate j i hgt ⟨hstate.1.symm, hstate.2.symm⟩ K hK
    exact h

/-- Consequently, every fixed top offset of the product-deleted polar exponent
is eventually periodic modulo `d`, with one period working for all offsets.
The threshold grows only by the offset; this is the exact tail form used when
the Stoneham kicks are reindexed downwards from the top depth. -/
lemma exists_eventually_modEq_stonehamPolarDeletedExponent (u d : ℕ) (hd : 0 < d) :
    ∃ K₀ T : ℕ, 0 < T ∧ ∀ K s, K₀ + s ≤ K →
      stonehamPolarDeletedExponent u (K + T) (K + T - s) ≡
        stonehamPolarDeletedExponent u K (K - s) [MOD d] := by
  obtain ⟨K₀, T, hT, hperiod⟩ := exists_eventually_modEq_pow_and_geomSum u d hd
  refine ⟨K₀ + 1, T, hT, fun K s hKs => ?_⟩
  have hK₀K : K₀ ≤ K := by omega
  have hK₀sub : K₀ ≤ K - s := by omega
  have hsK : s ≤ K := by omega
  have hj : K - s ∈ Icc 1 K := mem_Icc.mpr ⟨by omega, Nat.sub_le K s⟩
  have hjT : K + T - s ∈ Icc 1 (K + T) :=
    mem_Icc.mpr ⟨by omega, Nat.sub_le (K + T) s⟩
  have hpow : u ^ (K + T - s) ≡ u ^ (K - s) [MOD d] := by
    have := (hperiod (K - s) hK₀sub).1
    simpa only [show K - s + T = K + T - s by omega] using this
  have hsum := (hperiod K hK₀K).2
  have hall :
      stonehamPolarDeletedExponent u (K + T) (K + T - s) + u ^ (K + T - s) ≡
        stonehamPolarDeletedExponent u K (K - s) + u ^ (K - s) [MOD d] := by
    rw [stonehamPolarDeletedExponent_add u (K + T) (K + T - s) hjT,
      stonehamPolarDeletedExponent_add u K (K - s) hj]
    exact hsum
  exact hpow.add_right_cancel hall

/-- Exponents congruent modulo `d` give congruent powers whenever the base is a
`d`-th root of unity modulo the ambient modulus.  This is the elementary bridge
from the eventual period of `stonehamPolarDeletedExponent` to the finite
Teichmüller evaluations used in the resultant argument. -/
lemma pow_modEq_pow_of_exponent_modEq (D d e₁ e₂ : ℕ) (w : ℤ)
    (hroot : w ^ d ≡ 1 [ZMOD D]) (hexp : e₁ ≡ e₂ [MOD d]) :
    w ^ e₁ ≡ w ^ e₂ [ZMOD D] := by
  rw [← ZMod.intCast_eq_intCast_iff] at hroot ⊢
  push_cast at hroot ⊢
  exact pow_eq_pow_of_modEq hexp hroot

/-- After fixing an approximate `d`-th root of unity, every top-offset
product-deleted polar factor is eventually periodic.  One threshold and period
work simultaneously for all offsets that have entered the tail. -/
lemma exists_eventually_modEq_polarDeletedPower
    (u d D : ℕ) (w : ℤ) (hd : 0 < d) (hroot : w ^ d ≡ 1 [ZMOD D]) :
    ∃ K₀ T : ℕ, 0 < T ∧ ∀ K s, K₀ + s ≤ K →
      w ^ stonehamPolarDeletedExponent u (K + T) (K + T - s) ≡
        w ^ stonehamPolarDeletedExponent u K (K - s) [ZMOD D] := by
  obtain ⟨K₀, T, hT, hperiod⟩ :=
    exists_eventually_modEq_stonehamPolarDeletedExponent u d hd
  exact ⟨K₀, T, hT, fun K s hKs =>
    pow_modEq_pow_of_exponent_modEq D d _ _ w hroot (hperiod K s hKs)⟩

/-- Reindex a positive-depth history by its offset below the top depth. -/
lemma sum_Icc_one_reflect {A : Type*} [AddCommMonoid A] (F : ℕ → A) (K : ℕ) :
    ∑ j ∈ Icc 1 K, F (K - j) = ∑ s ∈ range K, F s := by
  have hshift : ∀ (H : ℕ → A) (K : ℕ),
      ∑ j ∈ Icc 1 K, H j = ∑ k ∈ range K, H (k + 1) := by
    intro H K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [sum_Icc_succ_top (Nat.le_add_left 1 K), ih, sum_range_succ]
  rw [hshift]
  calc
    (∑ k ∈ range K, F (K - (k + 1))) =
        ∑ k ∈ range K, F (K - 1 - k) := by
          apply sum_congr rfl
          intro k hk
          congr 1
          omega
    _ = ∑ s ∈ range K, F s := sum_range_reflect F K

/-- The explicit numerator obtained by clearing the denominator `c^K` in one
Stoneham family (with the literal base exponent `m = 1`). -/
def stonehamClearedFamily (b c n K : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 K, (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j)

/-- Clearing by `c^K` gives exactly `stonehamClearedFamily`; this identifies
the modular polar calculation above with the numerator used by
`stonehamState`. -/
lemma stonehamFamily_eq_cleared_div (b c n K : ℕ) (hc0 : c ≠ 0) :
    ∑ j ∈ Icc 1 K,
        (b : ℚ) ^ (n - c ^ j) / (c : ℚ) ^ j =
      (stonehamClearedFamily b c n K : ℚ) / (c : ℚ) ^ K := by
  rw [eq_div_iff (pow_ne_zero _ (by exact_mod_cast hc0)),
    stonehamClearedFamily, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_pow, Int.cast_natCast]
  have hjK : j ≤ K := (mem_Icc.mp hj).2
  rw [show K = j + (K - j) by omega, pow_add]
  field_simp
  congr 2 <;> omega

/-- Dyadic polar-phase form of item (K).  At a positive dyadic depth the Teichmüller factor is
one, so an entered phase `b^(n-c^j)` agrees directly with `b^n`. -/
lemma twoStonehamPhase_modEq_of_factor (b c a u j n : ℕ)
    (hb : Odd b) (ha : 1 ≤ a) (hj : 1 ≤ j) (hc : c = 2 ^ a * u)
    (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) ≡ (b : ℤ) ^ n [ZMOD 2 ^ (a * j + 2)] := by
  have hphase := (twoPower_modEq_one_of_factor b c a u j hb ha hj hc).symm
    |>.mul_left ((b : ℤ) ^ (n - c ^ j))
  simpa only [mul_one, ← pow_add, tsub_add_cancel_of_le hentered] using hphase

/-- Canonical-factorization version of the dyadic polar-phase congruence. -/
lemma twoStonehamPhase_modEq (b c j n : ℕ) (hb : Odd b) (hc0 : c ≠ 0)
    (hc : 2 ∣ c) (hj : 1 ≤ j) (hentered : c ^ j ≤ n) :
    (b : ℤ) ^ (n - c ^ j) ≡
      (b : ℤ) ^ n [ZMOD 2 ^ (c.factorization 2 * j + 2)] := by
  have hphase := (twoPower_modEq_one_of_even b c j hb hc0 hc hj).symm
    |>.mul_left ((b : ℤ) ^ (n - c ^ j))
  simpa only [mul_one, ← pow_add, tsub_add_cancel_of_le hentered] using hphase

/-! ### The repaired top-digit noncancellation argument -/

/-- If every lower base-`g` digit has size at most `M < g`, then their total contribution is
strictly smaller than one top digit.  This division-free induction is the scalar inequality in
the referee's repaired "never silent" argument. -/
lemma mul_sum_range_pow_lt_pow (g M J : ℕ) (hMg : M < g) :
    M * (∑ s ∈ range J, g ^ s) < g ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, pow_succ]
      calc
        M * (∑ s ∈ range J, g ^ s + g ^ J) =
            M * (∑ s ∈ range J, g ^ s) + M * g ^ J := by ring
        _ < g ^ J + M * g ^ J := Nat.add_lt_add_right ih _
        _ = (M + 1) * g ^ J := by ring
        _ ≤ g * g ^ J := Nat.mul_le_mul_right (g ^ J) (by omega)
        _ = g ^ J * g := by ring

/-- A complex base-`g` polynomial cannot vanish when its top coefficient has norm at least one
and every lower coefficient has norm at most `M < g`.  The statement works simultaneously under
all cyclotomic embeddings, which is precisely what the literal-pair periodic tail needs. -/
lemma geom_weighted_sum_ne_zero_of_norm
    (g M J : ℕ) (hMg : M < g) (μ : ℕ → ℂ)
    (htop : 1 ≤ ‖μ J‖) (hbound : ∀ s ∈ range J, ‖μ s‖ ≤ M) :
    ∑ s ∈ range (J + 1), μ s * (g : ℂ) ^ s ≠ 0 := by
  intro hzero
  rw [sum_range_succ] at hzero
  have heq : μ J * (g : ℂ) ^ J = -∑ s ∈ range J, μ s * (g : ℂ) ^ s := by
    linear_combination hzero
  have hlead : ((g : ℝ) ^ J) ≤ ‖μ J * (g : ℂ) ^ J‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      (g : ℝ) ^ J = 1 * (g : ℝ) ^ J := by ring
      _ ≤ ‖μ J‖ * (g : ℝ) ^ J :=
        mul_le_mul_of_nonneg_right htop (by positivity)
  have hsum : ‖∑ s ∈ range J, μ s * (g : ℂ) ^ s‖ ≤
      (M : ℝ) * ∑ s ∈ range J, (g : ℝ) ^ s := by
    calc
      ‖∑ s ∈ range J, μ s * (g : ℂ) ^ s‖ ≤
          ∑ s ∈ range J, ‖μ s * (g : ℂ) ^ s‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ range J, (M : ℝ) * (g : ℝ) ^ s := by
        apply sum_le_sum
        intro s hs
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbound s hs) (by positivity)
      _ = (M : ℝ) * ∑ s ∈ range J, (g : ℝ) ^ s := by rw [mul_sum]
  have hdom : (M : ℝ) * ∑ s ∈ range J, (g : ℝ) ^ s < (g : ℝ) ^ J := by
    exact_mod_cast mul_sum_range_pow_lt_pow g M J hMg
  have hlt : ‖μ J * (g : ℂ) ^ J‖ < ‖μ J * (g : ℂ) ^ J‖ := calc
    ‖μ J * (g : ℂ) ^ J‖ = ‖∑ s ∈ range J, μ s * (g : ℂ) ^ s‖ := by
      rw [heq, norm_neg]
    _ ≤ (M : ℝ) * ∑ s ∈ range J, (g : ℝ) ^ s := hsum
    _ < (g : ℝ) ^ J := hdom
    _ ≤ ‖μ J * (g : ℂ) ^ J‖ := hlead
  exact (lt_irrefl _ hlt)

/-- The repaired noncancellation lemma for literal sums: coefficient norms at most two are
dominated in every base `g ≥ 3`. -/
lemma literalSum_tail_ne_zero (g J : ℕ) (hg : 3 ≤ g) (μ : ℕ → ℂ)
    (htop : 1 ≤ ‖μ J‖) (hbound : ∀ s ∈ range J, ‖μ s‖ ≤ 2) :
    ∑ s ∈ range (J + 1), μ s * (g : ℂ) ^ s ≠ 0 :=
  geom_weighted_sum_ne_zero_of_norm g 2 J (by omega) μ htop
    (fun s hs => by simpa using hbound s hs)

/-- The corresponding literal-difference lemma works already in base `g = 2`, since all
coefficient norms are at most one. -/
lemma literalDiff_tail_ne_zero (g J : ℕ) (hg : 2 ≤ g) (μ : ℕ → ℂ)
    (htop : 1 ≤ ‖μ J‖) (hbound : ∀ s ∈ range J, ‖μ s‖ ≤ 1) :
    ∑ s ∈ range (J + 1), μ s * (g : ℂ) ^ s ≠ 0 :=
  geom_weighted_sum_ne_zero_of_norm g 1 J (by omega) μ htop
    (fun s hs => by simpa using hbound s hs)

end NormalNumbers.StonehamPairsNormal
