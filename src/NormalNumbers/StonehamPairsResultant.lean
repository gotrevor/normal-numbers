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
