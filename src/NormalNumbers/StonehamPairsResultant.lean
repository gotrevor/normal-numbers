/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsArithmetic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant control for periodic Stoneham polar tails

The finite polar representative in `StonehamPairsArithmetic` is an approximate root of unity
modulo a growing prime power.  This file turns the repaired complex top-digit noncancellation
argument into the fixed integer obstruction needed to bound its p-adic cancellation.

The key point is integral and finite: if both `F(z)` and `G(z)` are divisible by `D`, then `D`
divides `Res(G,F)`.  For `G = X^d - 1`, the top-digit estimate proves this resultant is nonzero,
so its fixed p-adic valuation uniformly bounds that of `F(z)` whenever `z^d` agrees with one to
sufficient precision.
-/

namespace NormalNumbers.StonehamPairsNormal

open Polynomial

/-- The level-`K` finite Teichmüller representative is a `(p-1)`-st root of unity modulo
`p^(K+1)`.  This is Euler's theorem in the exact form consumed by the resultant bound below;
it also covers `p = 2`, when the exponent is one. -/
lemma teichmullerRepresentative_pow_pred_modEq_one
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p) :
    ((b : ℤ) ^ (p ^ K)) ^ (p - 1) ≡ 1 [ZMOD p ^ (K + 1)] := by
  have hcop : Nat.Coprime b (p ^ (K + 1)) := hbp.pow_right (K + 1)
  have heuler := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow_succ hp, pow_mul] at heuler
  exact_mod_cast heuler

/-- An integral finite polar tail.  The coefficient at depth `s` has its base-`g` weight built
in, while `e s` records the exponent of the finite root-of-unity representative. -/
noncomputable def polarTailPolynomial (g J : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (J + 1),
    Polynomial.C (a s * (g : ℤ) ^ s) * Polynomial.X ^ e s

/-- Integral evaluation of a polar-tail polynomial. -/
lemma eval_polarTailPolynomial_int (g J : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ)
    (w : ℤ) :
    (polarTailPolynomial g J a e).eval w =
      ∑ s ∈ Finset.range (J + 1), a s * (g : ℤ) ^ s * w ^ e s := by
  simp only [polarTailPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Terms at top offsets `s ≥ S` vanish modulo `p^N` once their built-in
`c^s` weight contains at least `N` copies of `p`.  This is the finite
truncation step that turns the growing Stoneham polar tail into a fixed-length
tail before periodicity and resultants are applied. -/
lemma polarTail_sum_modEq_truncate_of_factor
    (p c a u N S K : ℕ) (w : ℤ) (coeff : ℕ → ℤ) (e : ℕ → ℕ)
    (hc : c = p ^ a * u) (hSK : S ≤ K) (hNS : N ≤ a * S) :
    ∑ s ∈ Finset.range K, coeff s * (c : ℤ) ^ s * w ^ e s ≡
      ∑ s ∈ Finset.range S, coeff s * (c : ℤ) ^ s * w ^ e s
        [ZMOD p ^ N] := by
  rw [show K = S + (K - S) by omega, Finset.sum_range_add]
  have htail :
      ∑ x ∈ Finset.range (K - S),
          coeff (S + x) * (c : ℤ) ^ (S + x) * w ^ e (S + x) ≡ 0
            [ZMOD p ^ N] := by
    simpa only [Finset.sum_const_zero] using
      (Int.ModEq.sum fun x hx => (Int.modEq_zero_iff_dvd.mpr (by
        have hpow : (p : ℤ) ^ (a * (S + x)) ∣ (c : ℤ) ^ (S + x) := by
          rw [hc]
          push_cast
          rw [mul_pow, ← pow_mul]
          exact dvd_mul_right ((p : ℤ) ^ (a * (S + x))) ((u : ℤ) ^ (S + x))
        have hNSx : N ≤ a * (S + x) :=
          hNS.trans (Nat.mul_le_mul_left a (Nat.le_add_right S x))
        have hprec : (p : ℤ) ^ N ∣ (p : ℤ) ^ (a * (S + x)) :=
          pow_dvd_pow (p : ℤ) hNSx
        have hbase : (p : ℤ) ^ N ∣ (c : ℤ) ^ (S + x) := hprec.trans hpow
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_left hbase (coeff (S + x) * w ^ e (S + x)))))
  simpa using htail.add_left
    (∑ s ∈ Finset.range S, coeff s * (c : ℤ) ^ s * w ^ e s)

/-- Polynomial form of `polarTail_sum_modEq_truncate_of_factor`: a tail of
length `K` agrees modulo `p^N` with its first `S` top offsets.  The exponent
pattern is kept unchanged, ready to be frozen on an eventual period class. -/
lemma polarTailPolynomial_eval_modEq_truncate_of_factor
    (p c a u N S K : ℕ) (w : ℤ) (coeff : ℕ → ℤ) (e : ℕ → ℕ)
    (hc : c = p ^ a * u) (hS : 1 ≤ S) (hSK : S ≤ K) (hNS : N ≤ a * S) :
    (polarTailPolynomial c (K - 1) coeff e).eval w ≡
      (polarTailPolynomial c (S - 1) coeff e).eval w [ZMOD p ^ N] := by
  rw [eval_polarTailPolynomial_int, eval_polarTailPolynomial_int,
    show K - 1 + 1 = K by omega, show S - 1 + 1 = S by omega]
  exact polarTail_sum_modEq_truncate_of_factor p c a u N S K w coeff e hc hSK hNS

/-- If two exponent patterns agree modulo `d`, their polar-tail evaluations
agree at every approximate `d`-th root of unity. -/
lemma polarTailPolynomial_eval_modEq_of_exponents
    (D d g J : ℕ) (w : ℤ) (coeff : ℕ → ℤ) (e₁ e₂ : ℕ → ℕ)
    (hroot : w ^ d ≡ 1 [ZMOD D])
    (hexp : ∀ s ∈ Finset.range (J + 1), e₁ s ≡ e₂ s [MOD d]) :
    (polarTailPolynomial g J coeff e₁).eval w ≡
      (polarTailPolynomial g J coeff e₂).eval w [ZMOD D] := by
  rw [eval_polarTailPolynomial_int, eval_polarTailPolynomial_int]
  apply Int.ModEq.sum
  intro s hs
  exact (pow_modEq_pow_of_exponent_modEq D d (e₁ s) (e₂ s) w hroot
    (hexp s hs)).mul_left (coeff s * (g : ℤ) ^ s)

/-- A fixed-length top part of the actual Stoneham polar tail is eventually
periodic, as a polynomial evaluation, at every approximate root of unity.
This packages the finite-state reduction needed after truncation: one period
and threshold work for all `S` retained offsets simultaneously. -/
lemma exists_eventually_modEq_truncatedPolarTail
    (u d D c S : ℕ) (hS : 1 ≤ S) (hd : 0 < d) :
    ∃ K₀ T : ℕ, 0 < T ∧ ∀ K w, K₀ + S ≤ K → w ^ d ≡ 1 [ZMOD D] →
      (polarTailPolynomial c (S - 1) (fun _ => 1)
        (fun s => stonehamPolarDeletedExponent u (K + T) (K + T - s))).eval w ≡
      (polarTailPolynomial c (S - 1) (fun _ => 1)
        (fun s => stonehamPolarDeletedExponent u K (K - s))).eval w [ZMOD D] := by
  obtain ⟨K₀, T, hT, hperiod⟩ :=
    exists_eventually_modEq_stonehamPolarDeletedExponent u d hd
  refine ⟨K₀, T, hT, fun K w hKS hroot => ?_⟩
  apply polarTailPolynomial_eval_modEq_of_exponents D d c (S - 1) w
    (fun _ => 1) _ _ hroot
  intro s hs
  have hsS : s < S := by simpa [show S - 1 + 1 = S by omega] using Finset.mem_range.mp hs
  exact hperiod K s (by omega)

/-- Evaluation after embedding the integral polar tail in `ℂ` is the weighted geometric sum
used by `geom_weighted_sum_ne_zero_of_norm`. -/
lemma eval_map_polarTailPolynomial (g J : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ)
    (z : ℂ) :
    Polynomial.eval z ((polarTailPolynomial g J a e).map (Int.castRingHom ℂ)) =
      ∑ s ∈ Finset.range (J + 1),
        ((a s : ℂ) * z ^ e s) * (g : ℂ) ^ s := by
  rw [Polynomial.eval_map]
  change (Polynomial.eval₂RingHom (Int.castRingHom ℂ) z)
      (polarTailPolynomial g J a e) = _
  rw [polarTailPolynomial, map_sum]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_mul, map_pow]
  change ((a s : ℂ) * (g : ℂ) ^ s) * z ^ e s =
    ((a s : ℂ) * z ^ e s) * (g : ℂ) ^ s
  ring

/-- The product-deleted coefficient in the cleared Stoneham numerator is
literally a `polarTailPolynomial` evaluation after reindexing the history by
offsets below its top kick.  This removes the growing interval `Icc 1 K` from
the arithmetic expression and exposes the dominated base-`c` digits consumed
by the resultant bound. -/
lemma eval_polarTailPolynomial_stonehamDeleted (c u K : ℕ) (w : ℤ) (hK : 1 ≤ K) :
    (polarTailPolynomial c (K - 1) (fun _ => 1)
        (fun s => stonehamPolarDeletedExponent u K (K - s))).eval w =
      ∑ j ∈ Finset.Icc 1 K,
        (c : ℤ) ^ (K - j) * w ^ stonehamPolarDeletedExponent u K j := by
  rw [polarTailPolynomial]
  change (Polynomial.evalRingHom w)
      (∑ s ∈ Finset.range (K - 1 + 1),
        Polynomial.C (1 * (c : ℤ) ^ s) *
          Polynomial.X ^ stonehamPolarDeletedExponent u K (K - s)) = _
  rw [map_sum]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, one_mul]
  rw [show K - 1 + 1 = K by omega]
  rw [← sum_Icc_one_reflect
    (fun s => (c : ℤ) ^ s * w ^ stonehamPolarDeletedExponent u K (K - s)) K]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.sub_sub_self (Finset.mem_Icc.mp hj).2]

/-- The full right side of the polar congruence is a common `b^n` factor
times the preceding fixed-shape tail evaluation. -/
lemma stoneham_polarRhs_eq_eval (b c u K n : ℕ) (w : ℤ) (hK : 1 ≤ K) :
    ∑ j ∈ Finset.Icc 1 K,
        (b : ℤ) ^ n * (c : ℤ) ^ (K - j) *
          w ^ stonehamPolarDeletedExponent u K j =
      (b : ℤ) ^ n *
        (polarTailPolynomial c (K - 1) (fun _ => 1)
          (fun s => stonehamPolarDeletedExponent u K (K - s))).eval w := by
  rw [eval_polarTailPolynomial_stonehamDeleted c u K w hK, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual cleared one-family numerator, after multiplication by its
common polar unit, is congruent to a single dominated tail-polynomial
evaluation.  This is the direct interface between the full-history arithmetic
congruence and the fixed-resultant noncancellation machinery. -/
lemma stonehamClearedFamily_mul_polarPower_modEq_polarTail
    (p b c a u K n : ℕ) (hp : p.Prime) (hc : c = p ^ a * u)
    (hK : 1 ≤ K) (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    ∑ j ∈ Finset.Icc 1 K,
          (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) *
            ((b : ℤ) ^ (p ^ (a * K))) ^ stonehamPolarExponent u K ≡
      (b : ℤ) ^ n *
        (polarTailPolynomial c (K - 1) (fun _ => 1)
          (fun s => stonehamPolarDeletedExponent u K (K - s))).eval
            ((b : ℤ) ^ (p ^ (a * K))) [ZMOD p ^ (a * K + 1)] := by
  have hpolar := stonehamClearedFamily_mul_polarPower_modEq_of_factor
    p b c a u K n hp hc hentered
  rw [stoneham_polarRhs_eq_eval b c u K n ((b : ℤ) ^ (p ^ (a * K))) hK] at hpolar
  exact hpolar

/-- The complete cleared numerator already agrees, at any requested precision
`N ≤ a*K+1`, with a polar tail of the fixed length `S`, provided `a*S`
absorbs that precision.  Thus all dependence on earlier kicks has been removed;
only the first `S` top-offset exponents still have to be frozen by eventual
periodicity. -/
lemma stonehamClearedFamily_mul_polarPower_modEq_truncatedTail
    (p b c a u K n N S : ℕ) (hp : p.Prime) (hc : c = p ^ a * u)
    (hS : 1 ≤ S) (hSK : S ≤ K) (hNS : N ≤ a * S) (hNK : N ≤ a * K + 1)
    (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    ∑ j ∈ Finset.Icc 1 K,
          (b : ℤ) ^ (n - c ^ j) * (c : ℤ) ^ (K - j) *
            ((b : ℤ) ^ (p ^ (a * K))) ^ stonehamPolarExponent u K ≡
      (b : ℤ) ^ n *
        (polarTailPolynomial c (S - 1) (fun _ => 1)
          (fun s => stonehamPolarDeletedExponent u K (K - s))).eval
            ((b : ℤ) ^ (p ^ (a * K))) [ZMOD p ^ N] := by
  have hfull := stonehamClearedFamily_mul_polarPower_modEq_polarTail
    p b c a u K n hp hc (hS.trans hSK) hentered
  have hdrop := hfull.of_dvd (pow_dvd_pow (p : ℤ) hNK)
  have htrunc := polarTailPolynomial_eval_modEq_truncate_of_factor
    p c a u N S K ((b : ℤ) ^ (p ^ (a * K))) (fun _ => 1)
      (fun s => stonehamPolarDeletedExponent u K (K - s)) hc hS hSK hNS
  exact hdrop.trans (htrunc.mul_left ((b : ℤ) ^ n))

/-- A single Stoneham family has no `p`-adic cancellation at all in its
cleared numerator.  After the common polar multiplication, the newest kick
is a unit modulo `p`, while every older top-offset term carries a positive
power of `c` and hence vanishes modulo `p`.

This is the non-circular one-family endpoint of the truncation argument: no
resultant or cutoff depending on a prospective valuation bound is needed.
Resultants enter only after two same-class families have been aligned, where
their newest unit terms can genuinely cancel. -/
theorem not_dvd_stonehamClearedFamily_of_factor
    (p b c a u K n : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    (hc : c = p ^ a * u) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    ¬ (p : ℤ) ∣ stonehamClearedFamily b c n K := by
  let w : ℤ := (b : ℤ) ^ (p ^ (a * K))
  have hcong := stonehamClearedFamily_mul_polarPower_modEq_truncatedTail
    p b c a u K n 1 1 hp hc (by omega) hK (by simpa using ha)
      (by omega) hentered
  have hcong' :
      stonehamClearedFamily b c n K * w ^ stonehamPolarExponent u K ≡
        (b : ℤ) ^ n * w ^ stonehamPolarDeletedExponent u K K [ZMOD p] := by
    simpa [stonehamClearedFamily, w, eval_polarTailPolynomial_int,
      Finset.sum_mul, mul_assoc] using hcong
  intro hdvd
  have hleft : (p : ℤ) ∣
      stonehamClearedFamily b c n K * w ^ stonehamPolarExponent u K :=
    dvd_mul_of_dvd_left hdvd _
  have hright : (p : ℤ) ∣
      (b : ℤ) ^ n * w ^ stonehamPolarDeletedExponent u K K :=
    Int.modEq_zero_iff_dvd.mp (hcong'.symm.trans
      (Int.modEq_zero_iff_dvd.mpr hleft))
  have hpow : (p : ℤ) ∣
      (b : ℤ) ^ (n + p ^ (a * K) * stonehamPolarDeletedExponent u K K) := by
    simpa only [w, ← pow_mul, ← pow_add] using hright
  have hpb : ¬ p ∣ b := hp.coprime_iff_not_dvd.mp hbp.symm
  exact hpb (by simpa using Int.Prime.dvd_pow hp hpow)

/-- Valuation form of `not_dvd_stonehamClearedFamily_of_factor`. -/
theorem padicValInt_stonehamClearedFamily_eq_zero_of_factor
    (p b c a u K n : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    (hc : c = p ^ a * u) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    padicValInt p (stonehamClearedFamily b c n K) = 0 := by
  exact padicValInt.eq_zero_of_not_dvd
    (not_dvd_stonehamClearedFamily_of_factor
      p b c a u K n hp hbp hc ha hK hentered)

/-- Canonical-factorization form of the one-family unit theorem. -/
theorem not_dvd_stonehamClearedFamily
    (p b c K n : ℕ) (hp : p.Prime) (hc0 : c ≠ 0) (hpc : p ∣ c)
    (hcb : Nat.Coprime c b) (hK : 1 ≤ K)
    (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    ¬ (p : ℤ) ∣ stonehamClearedFamily b c n K := by
  have ha : 1 ≤ c.factorization p :=
    (hp.dvd_iff_one_le_factorization hc0).mp hpc
  have hbp : Nat.Coprime b p :=
    (Nat.Coprime.of_dvd_left hpc hcb).symm
  exact not_dvd_stonehamClearedFamily_of_factor p b c
    (c.factorization p) (ordCompl[p] c) K n hp hbp
      (Nat.ordProj_mul_ordCompl_eq_self c p).symm ha hK hentered

/-- Every prime divisor of `c` sees the one-family cleared numerator as a
unit.  This is the form used by the later distinct-class rate comparison. -/
theorem padicValInt_stonehamClearedFamily_eq_zero
    (p b c K n : ℕ) (hp : p.Prime) (hc0 : c ≠ 0) (hpc : p ∣ c)
    (hcb : Nat.Coprime c b) (hK : 1 ≤ K)
    (hentered : ∀ j ∈ Finset.Icc 1 K, c ^ j ≤ n) :
    padicValInt p (stonehamClearedFamily b c n K) = 0 := by
  exact padicValInt.eq_zero_of_not_dvd
    (not_dvd_stonehamClearedFamily p b c K n hp hc0 hpc hcb hK hentered)

/-- Elementary rate-separation lemma for two cleared families.  If the term
at the shallower `p`-depth has a unit coefficient, then adding any term at a
strictly deeper `p`-depth cannot change its valuation.  Together with
`padicValInt_stonehamClearedFamily_eq_zero`, this is the local algebraic
mechanism for two distinct primitive classes; the remaining global step is
to find a prime whose two depth slopes separate. -/
theorem padicValInt_unit_mul_pow_add_mul_pow_of_lt
    (p : ℕ) [Fact p.Prime] (A B : ℤ) (e f : ℕ)
    (hA : ¬ (p : ℤ) ∣ A) (hef : e < f) :
    padicValInt p (A * (p : ℤ) ^ e + B * (p : ℤ) ^ f) = e := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hpdvd : (p : ℤ) ∣ (p : ℤ) ^ (f - e) :=
    dvd_pow_self (p : ℤ) (by omega)
  have hterm : (p : ℤ) ∣ B * (p : ℤ) ^ (f - e) :=
    dvd_mul_of_dvd_right hpdvd B
  have hunit : ¬ (p : ℤ) ∣ A + B * (p : ℤ) ^ (f - e) := by
    intro hsum
    apply hA
    simpa using dvd_sub hsum hterm
  have hunit0 : A + B * (p : ℤ) ^ (f - e) ≠ 0 := by
    intro hz
    apply hunit
    simp [hz]
  have hpow0 : (p : ℤ) ^ e ≠ 0 := pow_ne_zero e hp0
  have hpowf : (p : ℤ) ^ f = (p : ℤ) ^ e * (p : ℤ) ^ (f - e) := by
    calc
      (p : ℤ) ^ f = (p : ℤ) ^ (e + (f - e)) := by congr 1; omega
      _ = (p : ℤ) ^ e * (p : ℤ) ^ (f - e) := pow_add _ _ _
  have hfactor :
      A * (p : ℤ) ^ e + B * (p : ℤ) ^ f =
        (p : ℤ) ^ e * (A + B * (p : ℤ) ^ (f - e)) := by
    rw [hpowf]
    ring
  rw [hfactor, padicValInt.mul hpow0 hunit0,
    padicValInt.eq_zero_of_not_dvd hunit, add_zero]
  rw [← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]

/-- The preceding separation applied to the actual common-denominator
numerator of two Stoneham families.  If the `c₁` family contributes at a
strictly shallower `p`-depth after cross multiplication, its cleared numerator
and the prime-to-`p` part of `c₂` form the required unit coefficient.  The
second family may have either literal sign (indeed, any integer coefficient).

This theorem isolates the complete local content of the distinct-class case.
What remains for that branch is the global arithmetic statement that
multiplicatively independent `c₁,c₂` admit a prime for which these depths
separate by a positive multiple of `log n`. -/
theorem padicValInt_pairCleared_eq_of_depth_lt
    (p b c₁ c₂ K₁ K₂ n : ℕ) (σ : ℤ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) (hpc₁ : p ∣ c₁)
    (hcb₁ : Nat.Coprime c₁ b) (hK₁ : 1 ≤ K₁)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hdepth : c₂.factorization p * K₂ < c₁.factorization p * K₁) :
    padicValInt p
        (stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
          σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁) =
      c₂.factorization p * K₂ := by
  letI : Fact p.Prime := ⟨hp⟩
  let A₁ := stonehamClearedFamily b c₁ n K₁
  let A₂ := stonehamClearedFamily b c₂ n K₂
  let u₁ : ℕ := ordCompl[p] c₁
  let u₂ : ℕ := ordCompl[p] c₂
  let e := c₂.factorization p * K₂
  let f := c₁.factorization p * K₁
  have hA₁ : ¬ (p : ℤ) ∣ A₁ := by
    exact not_dvd_stonehamClearedFamily p b c₁ K₁ n hp hc₁0 hpc₁
      hcb₁ hK₁ hentered₁
  have hu₂ : ¬ p ∣ u₂ := Nat.not_dvd_ordCompl hp hc₂0
  have hu₂Z : ¬ (p : ℤ) ∣ (u₂ : ℤ) ^ K₂ := by
    intro hdvd
    apply hu₂
    have hdvdNat : p ∣ u₂ ^ K₂ := by exact_mod_cast hdvd
    exact hp.dvd_of_dvd_pow hdvdNat
  have hunit : ¬ (p : ℤ) ∣ A₁ * (u₂ : ℤ) ^ K₂ := by
    intro hdvd
    rcases Int.Prime.dvd_mul' hp hdvd with h | h
    · exact hA₁ h
    · exact hu₂Z h
  have hc₁pow : (c₁ : ℤ) ^ K₁ =
      (p : ℤ) ^ f * (u₁ : ℤ) ^ K₁ := by
    calc
      (c₁ : ℤ) ^ K₁ =
          (((p : ℤ) ^ c₁.factorization p) * (u₁ : ℤ)) ^ K₁ := by
            congr 1
            exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self c₁ p).symm
      _ = (p : ℤ) ^ f * (u₁ : ℤ) ^ K₁ := by
        rw [mul_pow, ← pow_mul]
  have hc₂pow : (c₂ : ℤ) ^ K₂ =
      (p : ℤ) ^ e * (u₂ : ℤ) ^ K₂ := by
    calc
      (c₂ : ℤ) ^ K₂ =
          (((p : ℤ) ^ c₂.factorization p) * (u₂ : ℤ)) ^ K₂ := by
            congr 1
            exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self c₂ p).symm
      _ = (p : ℤ) ^ e * (u₂ : ℤ) ^ K₂ := by
        rw [mul_pow, ← pow_mul]
  have hshape :
      stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
          σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁ =
        (A₁ * (u₂ : ℤ) ^ K₂) * (p : ℤ) ^ e +
          (σ * A₂ * (u₁ : ℤ) ^ K₁) * (p : ℤ) ^ f := by
    rw [hc₁pow, hc₂pow]
    dsimp only [A₁, A₂]
    ring
  rw [hshape]
  exact padicValInt_unit_mul_pow_add_mul_pow_of_lt p
    (A₁ * (u₂ : ℤ) ^ K₂) (σ * A₂ * (u₁ : ℤ) ^ K₁) e f hunit hdepth

/-- For a literal sum at a common prime, unequal cleared depths make the
valuation exactly the smaller depth. -/
theorem padicValInt_pairCleared_add_eq_min_of_depth_ne
    (p b c₁ c₂ K₁ K₂ n : ℕ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) (hpc₁ : p ∣ c₁) (hpc₂ : p ∣ c₂)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 K₂, c₂ ^ j ≤ n)
    (hne : c₁.factorization p * K₁ ≠ c₂.factorization p * K₂) :
    padicValInt p
        (stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
          stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁) =
      min (c₁.factorization p * K₁) (c₂.factorization p * K₂) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := padicValInt_pairCleared_eq_of_depth_lt
      p b c₂ c₁ K₂ K₁ n 1 hp hc₂0 hc₁0 hpc₂ hcb₂ hK₂ hentered₂ hlt
    simpa [add_comm, Nat.min_eq_left hlt.le] using h
  · have h := padicValInt_pairCleared_eq_of_depth_lt
      p b c₁ c₂ K₁ K₂ n 1 hp hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hgt
    simpa [Nat.min_eq_right hgt.le] using h

/-- The same exact smaller-depth valuation for a literal difference. -/
theorem padicValInt_pairCleared_sub_eq_min_of_depth_ne
    (p b c₁ c₂ K₁ K₂ n : ℕ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) (hpc₁ : p ∣ c₁) (hpc₂ : p ∣ c₂)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 K₂, c₂ ^ j ≤ n)
    (hne : c₁.factorization p * K₁ ≠ c₂.factorization p * K₂) :
    padicValInt p
        (stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ -
          stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁) =
      min (c₁.factorization p * K₁) (c₂.factorization p * K₂) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := padicValInt_pairCleared_eq_of_depth_lt
      p b c₂ c₁ K₂ K₁ n (-1) hp hc₂0 hc₁0 hpc₂ hcb₂ hK₂ hentered₂ hlt
    calc
      padicValInt p
          (stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ -
            stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁) =
        padicValInt p
          (-(stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ -
            stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁)) := by
              simp only [padicValInt, Int.natAbs_neg]
      _ = c₁.factorization p * K₁ := by
        convert h using 1 <;> ring
      _ = min (c₁.factorization p * K₁) (c₂.factorization p * K₂) := by
        symm
        exact Nat.min_eq_left hlt.le
  · have h := padicValInt_pairCleared_eq_of_depth_lt
      p b c₁ c₂ K₁ K₂ n (-1) hp hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hgt
    simpa [Nat.min_eq_right hgt.le, sub_eq_add_neg] using h

/-- Exact common-denominator form of a literal two-family state.  This is the
rational bridge from the cleared integer whose valuation is controlled above
to the `stonehamState` consumed by the analytic engine. -/
theorem stonehamPairFamilies_eq_cleared_div
    (b c₁ c₂ n K₁ K₂ : ℕ) (σ : ℤ) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) :
    (∑ j ∈ Finset.Icc 1 K₁,
        (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
      (σ : ℚ) * (∑ j ∈ Finset.Icc 1 K₂,
        (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j) =
      ((stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
          σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁ : ℤ) : ℚ) /
        (((c₁ ^ K₁) * (c₂ ^ K₂) : ℕ) : ℚ) := by
  rw [stonehamFamily_eq_cleared_div b c₁ n K₁ hc₁0,
    stonehamFamily_eq_cleared_div b c₂ n K₂ hc₂0]
  push_cast
  field_simp [hc₁0, hc₂0]

/-- Every root-of-unity evaluation of a polar tail is nonzero when the top base-`g` digit
strictly dominates all lower digits.  The exponent pattern is completely arbitrary. -/
lemma polarTailPolynomial_eval_ne_zero
    (g M J : ℕ) (hMg : M < g) (a : ℕ → ℤ) (e : ℕ → ℕ)
    (htop : 1 ≤ ‖(a J : ℂ)‖)
    (hbound : ∀ s ∈ Finset.range J, ‖(a s : ℂ)‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ = 1) :
    Polynomial.eval z ((polarTailPolynomial g J a e).map (Int.castRingHom ℂ)) ≠ 0 := by
  rw [eval_map_polarTailPolynomial]
  apply geom_weighted_sum_ne_zero_of_norm g M J hMg
  · simpa [norm_mul, norm_pow, hz] using htop
  · intro s hs
    simpa [norm_mul, norm_pow, hz] using hbound s hs

/-- If a modulus divides the values of two integral polynomials at the same integer, it divides
their resultant.  This is the integral Bézout identity supplied by the Sylvester adjugate. -/
lemma dvd_resultant_of_dvd_eval
    (D z : ℤ) (f g : ℤ[X]) (hgdeg : g.natDegree ≠ 0)
    (hf : D ∣ f.eval z) (hg : D ∣ g.eval z) :
    D ∣ g.resultant f := by
  obtain ⟨u, v, -, -, huv⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant g f le_rfl le_rfl (Or.inl hgdeg)
  have heval := congrArg (Polynomial.eval z) huv
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at heval
  rw [← heval]
  exact dvd_add (Dvd.dvd.mul_right hg _) (Dvd.dvd.mul_right hf _)

/-- A nonzero fixed resultant bounds the p-adic valuation of `f(z)` whenever `g(z)` vanishes
to greater p-adic precision. -/
lemma padicValInt_eval_le_resultant
    (p N : ℕ) (z : ℤ) (f g : ℤ[X]) [Fact p.Prime]
    (hgdeg : g.natDegree ≠ 0) (hres : g.resultant f ≠ 0)
    (hroot : (p : ℤ) ^ N ∣ g.eval z)
    (hN : padicValInt p (g.resultant f) < N) :
    padicValInt p (f.eval z) ≤ padicValInt p (g.resultant f) := by
  let v := padicValInt p (f.eval z)
  have hvN : v < N := by
    by_contra hv
    have hNle : N ≤ v := Nat.le_of_not_gt hv
    have hfdvd : (p : ℤ) ^ N ∣ f.eval z :=
      (padicValInt_dvd_iff N (f.eval z)).mpr (Or.inr hNle)
    have hrdvd := dvd_resultant_of_dvd_eval
      ((p : ℤ) ^ N) z f g hgdeg hfdvd hroot
    have hNle' : N ≤ padicValInt p (g.resultant f) :=
      ((padicValInt_dvd_iff N (g.resultant f)).mp hrdvd).resolve_left hres
    omega
  have hgdvd : (p : ℤ) ^ v ∣ g.eval z :=
    (pow_dvd_pow (p : ℤ) (Nat.le_of_lt hvN)).trans hroot
  have hfdvd : (p : ℤ) ^ v ∣ f.eval z := padicValInt_dvd _
  have hrdvd := dvd_resultant_of_dvd_eval
    ((p : ℤ) ^ v) z f g hgdeg hfdvd hgdvd
  exact ((padicValInt_dvd_iff v (g.resultant f)).mp hrdvd).resolve_left hres

/-- An integral resultant is nonzero if the first polynomial has no complex root at which the
second polynomial vanishes. -/
lemma resultant_ne_zero_of_complex_root_nonvanishing
    (f g : ℤ[X]) (hg0 : g ≠ 0)
    (hroot : ∀ z : ℂ, (g.map (Int.castRingHom ℂ)).IsRoot z →
      (f.map (Int.castRingHom ℂ)).eval z ≠ 0) :
    g.resultant f ≠ 0 := by
  let gc : ℂ[X] := g.map (Int.castRingHom ℂ)
  let fc : ℂ[X] := f.map (Int.castRingHom ℂ)
  have hgc0 : gc ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hg0
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hgcdeg : gc.natDegree = g.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective hinj g
  have hfcdeg : fc.natDegree = f.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective hinj f
  have hprod : (gc.roots.map fc.eval).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp hzero
    exact hroot z (Polynomial.isRoot_of_mem_roots hz) hz0
  have hlead : gc.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgc0
  have hcres : gc.resultant fc ≠ 0 := by
    rw [Polynomial.resultant_eq_prod_eval gc fc fc.natDegree le_rfl
      (IsAlgClosed.splits gc)]
    exact mul_ne_zero (pow_ne_zero _ hlead) hprod
  intro hres
  apply hcres
  have hmap := Polynomial.resultant_map_map g f g.natDegree f.natDegree
    (Int.castRingHom ℂ)
  change gc.resultant fc gc.natDegree fc.natDegree = 0
  rw [hgcdeg, hfcdeg]
  simpa only [gc, fc, hres, map_zero] using hmap

/-- The cyclotomic resultant of a dominated polar tail is a fixed nonzero integer. -/
lemma polarTail_resultant_ne_zero
    (g M J d : ℕ) (hMg : M < g) (hd : d ≠ 0)
    (a : ℕ → ℤ) (e : ℕ → ℕ)
    (htop : 1 ≤ ‖(a J : ℂ)‖)
    (hbound : ∀ s ∈ Finset.range J, ‖(a s : ℂ)‖ ≤ M) :
    ((Polynomial.X ^ d - Polynomial.C 1 : ℤ[X]).resultant
      (polarTailPolynomial g J a e)) ≠ 0 := by
  apply resultant_ne_zero_of_complex_root_nonvanishing
  · exact Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hd) 1
  · intro z hz
    apply polarTailPolynomial_eval_ne_zero g M J hMg a e htop hbound z
    apply Complex.norm_eq_one_of_pow_eq_one _ hd
    rw [Polynomial.IsRoot.def] at hz
    have hz' : z ^ d - 1 = 0 := by simpa using hz
    exact sub_eq_zero.mp hz'

/-- Uniform p-adic loss bound for a literal periodic tail.  Once the approximate root of unity
has precision above the valuation of the fixed nonzero resultant, every evaluation loses at most
that fixed number of p-adic digits. -/
lemma padicValInt_polarTail_eval_le_resultant
    (p N g M J d : ℕ) (z : ℤ) [Fact p.Prime]
    (hMg : M < g) (hd : d ≠ 0)
    (a : ℕ → ℤ) (e : ℕ → ℕ)
    (htop : 1 ≤ ‖(a J : ℂ)‖)
    (hbound : ∀ s ∈ Finset.range J, ‖(a s : ℂ)‖ ≤ M)
    (hroot : (p : ℤ) ^ N ∣ z ^ d - 1)
    (hN : padicValInt p
      ((Polynomial.X ^ d - Polynomial.C 1 : ℤ[X]).resultant
        (polarTailPolynomial g J a e)) < N) :
    padicValInt p ((polarTailPolynomial g J a e).eval z) ≤
      padicValInt p
        ((Polynomial.X ^ d - Polynomial.C 1 : ℤ[X]).resultant
          (polarTailPolynomial g J a e)) := by
  apply padicValInt_eval_le_resultant p N z
    (polarTailPolynomial g J a e) (Polynomial.X ^ d - Polynomial.C 1)
  · rw [Polynomial.natDegree_X_pow_sub_C]
    exact hd
  · exact polarTail_resultant_ne_zero g M J d hMg hd a e htop hbound
  · simpa using hroot
  · exact hN

/-- The preceding bound specialized to the actual finite Teichmüller representative
`b^(p^K)`.  The only depth hypothesis is that `K+1` has passed the valuation of the fixed
resultant. -/
lemma padicValInt_polarTail_eval_teichmuller_le_resultant
    (p b K g M J : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    (hMg : M < g) (a : ℕ → ℤ) (e : ℕ → ℕ)
    (htop : 1 ≤ ‖(a J : ℂ)‖)
    (hbound : ∀ s ∈ Finset.range J, ‖(a s : ℂ)‖ ≤ M)
    (hK : padicValInt p
      ((Polynomial.X ^ (p - 1) - Polynomial.C 1 : ℤ[X]).resultant
        (polarTailPolynomial g J a e)) < K + 1) :
    padicValInt p
        ((polarTailPolynomial g J a e).eval ((b : ℤ) ^ (p ^ K))) ≤
      padicValInt p
        ((Polynomial.X ^ (p - 1) - Polynomial.C 1 : ℤ[X]).resultant
          (polarTailPolynomial g J a e)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply padicValInt_polarTail_eval_le_resultant
    p (K + 1) g M J (p - 1) ((b : ℤ) ^ (p ^ K)) hMg
      (by have := hp.two_le; omega) a e htop hbound
  · exact (teichmullerRepresentative_pow_pred_modEq_one p b K hp hbp).symm.dvd
  · exact hK

end NormalNumbers.StonehamPairsNormal
