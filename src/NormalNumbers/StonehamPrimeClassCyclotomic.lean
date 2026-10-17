/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassAlgebra
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Cyclotomic relations for one prime Stoneham class

This file translates rational linear relations among selected powers of a primitive root into
divisibility of their relation polynomial by the corresponding cyclotomic polynomial.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset Polynomial

/-- The polynomial encoding a rational relation among powers of a root of unity. -/
noncomputable def relationPolynomial {r : ℕ} (m : Fin r → ℕ) (q : Fin r → ℚ) : ℚ[X] :=
  ∑ i, C (q i) * X ^ m i

/-- The integral relation polynomial obtained after rational coefficients have been cleared. -/
noncomputable def integerRelationPolynomial {r : ℕ} (m : Fin r → ℕ)
    (a : Fin r → ℤ) : ℤ[X] :=
  ∑ i, C (a i) * X ^ m i

@[simp] lemma map_integerRelationPolynomial {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ) :
    (integerRelationPolynomial m a).map (Int.castRingHom ℚ) =
      relationPolynomial m (fun i ↦ (a i : ℚ)) := by
  unfold integerRelationPolynomial relationPolynomial
  rw [Polynomial.map_sum]
  apply sum_congr rfl
  intro i hi
  simp

@[simp] lemma eval_integerRelationPolynomial {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ)
    (z : ℤ) :
    (integerRelationPolynomial m a).eval z = ∑ i, a i * z ^ m i := by
  unfold integerRelationPolynomial
  change Polynomial.eval₂ (RingHom.id ℤ) z (∑ i, C (a i) * X ^ m i) = _
  rw [eval₂_finsetSum]
  apply sum_congr rfl
  intro i hi
  simp

@[simp] lemma aeval_relationPolynomial {r : ℕ} (m : Fin r → ℕ) (q : Fin r → ℚ)
    (z : ℂ) :
    Polynomial.aeval z (relationPolynomial m q) = ∑ i, (q i : ℂ) * z ^ m i := by
  simp [relationPolynomial]

/-- A rational polynomial vanishes at a primitive complex `d`-th root exactly when it is
divisible by the `d`-th cyclotomic polynomial. -/
lemma cyclotomic_dvd_iff_aeval_eq_zero {d : ℕ} (hd : d ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (P : ℚ[X]) :
    cyclotomic d ℚ ∣ P ↔ Polynomial.aeval ζ P = 0 := by
  haveI : NeZero (d : ℚ) := ⟨by exact_mod_cast hd⟩
  rw [hζ.minpoly_eq_cyclotomic_of_irreducible
    (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hd))]
  exact minpoly.dvd_iff

/-- Gauss's lemma descends the complex vanishing criterion to divisibility of the cleared
integer relation polynomial. -/
lemma cyclotomic_int_dvd_integerRelationPolynomial_iff {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (m : Fin r → ℕ) (a : Fin r → ℤ) :
    cyclotomic d ℤ ∣ integerRelationPolynomial m a ↔
      Polynomial.aeval ζ (relationPolynomial m (fun i ↦ (a i : ℚ))) = 0 := by
  rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (cyclotomic.monic d ℤ).isPrimitive,
    map_cyclotomic, map_integerRelationPolynomial,
    cyclotomic_dvd_iff_aeval_eq_zero hd hζ]

/-- Once a cleared relation is cyclotomic-divisible, evaluation at any integer finite-level
representative preserves that divisibility. -/
lemma cyclotomic_eval_dvd_integerRelation_eval {d r : ℕ} (m : Fin r → ℕ)
    (a : Fin r → ℤ) (z : ℤ) (hdiv : cyclotomic d ℤ ∣ integerRelationPolynomial m a) :
    (cyclotomic d ℤ).eval z ∣ ∑ i, a i * z ^ m i := by
  rw [← eval_integerRelationPolynomial]
  exact Polynomial.eval₂_dvd _ _ hdiv

/-- Linear independence of the selected root powers is exactly the absence of a nonzero
coefficient vector whose relation polynomial is cyclotomic-divisible. -/
lemma linearIndependent_powers_iff_cyclotomic {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (m : Fin r → ℕ) :
    LinearIndependent ℚ (fun i ↦ ζ ^ m i) ↔
      ∀ q : Fin r → ℚ, cyclotomic d ℚ ∣ relationPolynomial m q → q = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h q hdiv
    funext i
    apply h q
    · simpa [Algebra.smul_def] using
        (cyclotomic_dvd_iff_aeval_eq_zero hd hζ _).mp hdiv
  · intro h q hsum
    have hdiv : cyclotomic d ℚ ∣ relationPolynomial m q := by
      apply (cyclotomic_dvd_iff_aeval_eq_zero hd hζ _).mpr
      rw [aeval_relationPolynomial]
      simpa [Algebra.smul_def] using hsum
    exact fun i => congrFun (h q hdiv) i

/-- The cyclotomic criterion exposes a concrete nonzero relation polynomial whenever the powers
are linearly dependent. -/
lemma not_linearIndependent_powers_iff_exists_cyclotomic {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (m : Fin r → ℕ) :
    ¬ LinearIndependent ℚ (fun i ↦ ζ ^ m i) ↔
      ∃ q : Fin r → ℚ, q ≠ 0 ∧ cyclotomic d ℚ ∣ relationPolynomial m q := by
  rw [linearIndependent_powers_iff_cyclotomic hd hζ]
  constructor
  · intro hn
    simp only [not_forall] at hn
    obtain ⟨q, hdiv, hq⟩ := hn
    exact ⟨q, hq, hdiv⟩
  · rintro ⟨q, hq, hdiv⟩ hall
    exact hq (hall q hdiv)

/-- Clearing the finitely many rational denominators turns dependence into a nonzero integral
relation divisible by the integral cyclotomic polynomial. -/
lemma not_linearIndependent_powers_iff_exists_integer_cyclotomic
    {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) (m : Fin r → ℕ) :
    ¬ LinearIndependent ℚ (fun i ↦ ζ ^ m i) ↔
      ∃ a : Fin r → ℤ, a ≠ 0 ∧ cyclotomic d ℤ ∣ integerRelationPolynomial m a := by
  classical
  constructor
  · intro hdep
    obtain ⟨q, hq, hdiv⟩ :=
      (not_linearIndependent_powers_iff_exists_cyclotomic hd hζ m).mp hdep
    let D : ℕ := ∏ i, (q i).den
    let a : Fin r → ℤ := fun i => (D / (q i).den : ℕ) * (q i).num
    have hDpos : 0 < D := by
      dsimp only [D]
      exact Finset.prod_pos fun i _ => (q i).pos
    have hden : ∀ i, (q i).den ∣ D := fun i => by
      dsimp only [D]
      exact Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
    have haq : ∀ i, (a i : ℚ) = (D : ℚ) * q i := by
      intro i
      have hmul := Nat.div_mul_cancel (hden i)
      have hmulQ : ((D / (q i).den : ℕ) : ℚ) * (q i).den = D := by
        exact_mod_cast hmul
      dsimp only [a]
      simp only [Int.cast_mul, Int.cast_natCast]
      rw [← Rat.den_mul_eq_num]
      push_cast
      rw [← mul_assoc, hmulQ]
    have ha : a ≠ 0 := by
      intro ha0
      apply hq
      funext i
      have hai : a i = 0 := congrFun ha0 i
      have hqi : (D : ℚ) * q i = 0 := by
        rw [← haq i, hai, Int.cast_zero]
      exact (mul_eq_zero.mp hqi).resolve_left (by exact_mod_cast hDpos.ne')
    refine ⟨a, ha, (cyclotomic_int_dvd_integerRelationPolynomial_iff hd hζ m a).mpr ?_⟩
    rw [aeval_relationPolynomial]
    have hzero := (cyclotomic_dvd_iff_aeval_eq_zero hd hζ _).mp hdiv
    rw [aeval_relationPolynomial] at hzero
    calc
      ∑ i, ((a i : ℚ) : ℂ) * ζ ^ m i =
          ((D : ℚ) : ℂ) * ∑ i, (q i : ℂ) * ζ ^ m i := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro i hi
            have hai : ((a i : ℚ) : ℂ) = ((D : ℚ) : ℂ) * (q i : ℂ) := by
              exact_mod_cast haq i
            rw [hai]
            ring
      _ = 0 := by rw [hzero, mul_zero]
  · rintro ⟨a, ha, hdiv⟩
    apply (not_linearIndependent_powers_iff_exists_cyclotomic hd hζ m).mpr
    refine ⟨fun i => (a i : ℚ), ?_, ?_⟩
    · intro hcast
      apply ha
      funext i
      have hi := congrFun hcast i
      simp only [Pi.zero_apply] at hi
      exact_mod_cast hi
    · apply (cyclotomic_dvd_iff_aeval_eq_zero hd hζ _).mpr
      exact (cyclotomic_int_dvd_integerRelationPolynomial_iff hd hζ m a).mp hdiv

/-- Rational independence of a fixed list of powers is independent of the chosen primitive
complex root of the same order. -/
lemma linearIndependent_powers_primitiveRoot_congr {d r : ℕ} (hd : d ≠ 0) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (hξ : IsPrimitiveRoot ξ d) (m : Fin r → ℕ) :
    LinearIndependent ℚ (fun i ↦ ζ ^ m i) ↔
      LinearIndependent ℚ (fun i ↦ ξ ^ m i) := by
  rw [linearIndependent_powers_iff_cyclotomic hd hζ,
    linearIndependent_powers_iff_cyclotomic hd hξ]

end NormalNumbers.StonehamPrimeClass
