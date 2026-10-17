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
