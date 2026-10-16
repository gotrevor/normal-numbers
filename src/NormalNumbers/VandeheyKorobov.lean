/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandeheyDifferencing
import ErdosProblems.Erdos67b.PrimeGraphFourier

/-!
# Finite Fourier input for Vandehey's Korobov estimate

This file develops the Parseval--orbit mechanism used in rung 2 of the proof of Vandehey's
Theorem 5.1.  A twisted subgroup sum has constant norm on the multiplicative orbit of a unit.
The orbit has as many elements as the subgroup, while Parseval says that the total Fourier
mass is the modulus times the subgroup size.  The lemma below isolates the resulting square-root
bound from the later arithmetic verification of the orbit identity.
-/

open scoped BigOperators
open Finset
open Erdos67b

namespace NormalNumbers.VandeheyKorobov

noncomputable section

open Literature.VandeheyDiff

/-! ## Rung 1: the order lower bound -/

/-- **Vandehey, Lemma 2.1, consumed form (equation (5)).**  If every prime factor of `m`
belongs to `P`, then the multiplicative order of `b` modulo `m` is at least `m / M(P)`.

The remaining proof debt is the simultaneous prime-power lifting argument, including the
exceptional 2-adic case.  The statement is frozen here before that arithmetic is developed. -/
theorem div_bigM_le_orderOf
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b)
    (m : ℕ) (hm : 2 ≤ m) (hsupp : ∀ p, p.Prime → p ∣ m → p ∈ P)
    (hbm : Nat.Coprime b m) :
    m / bigM b P ≤ orderOf (b : ZMod m) := by
  sorry

/-! ## Rung 2: the Parseval--orbit mechanism -/

/-- **The Parseval--orbit square-root bound.**  Let `b` be a length-`H` sequence of unit-modulus
coefficients and take its unnormalised Fourier transform modulo `T`.  If `H` distinct frequencies
all have the same Fourier norm as the frequency `a`, then that norm is at most `sqrt T`.

For the twisted subgroup sum in Vandehey's Lemma 2.2, the coefficients are the values of the
subgroup character, and the `H` frequencies are the orbit `aH`. -/
theorem norm_blockFourier_le_sqrt_of_orbit {H T : ℕ} [NeZero H] [NeZero T]
    (b : Fin H → ℂ) (hb : ∀ j, ‖b j‖ = 1) (a : ℤ)
    (orbit : Fin H → ℕ) (horbit_lt : ∀ j, orbit j < T)
    (horbit_inj : Function.Injective orbit)
    (horbit_norm : ∀ j, ‖blockFourier T b (orbit j : ℤ)‖ = ‖blockFourier T b a‖) :
    ‖blockFourier T b a‖ ≤ Real.sqrt T := by
  classical
  let O : Finset ℕ := Finset.univ.image orbit
  have hOsub : O ⊆ Finset.range T := by
    intro t ht
    rcases Finset.mem_image.1 ht with ⟨j, -, rfl⟩
    exact Finset.mem_range.2 (horbit_lt j)
  have hOcard : O.card = H := by
    simp only [O, Finset.card_image_of_injective _ horbit_inj, Finset.card_univ, Fintype.card_fin]
  have hOrbitSum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) = H * ‖blockFourier T b a‖ ^ 2 := by
    rw [show O = Finset.univ.image orbit from rfl,
      Finset.sum_image (fun x _ y _ hxy ↦ horbit_inj hxy)]
    simp_rw [horbit_norm]
    simp
  have hParseval :
      (∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 : ℝ) = T * H := by
    have hHT : H ≤ T := by
      calc
        H = O.card := hOcard.symm
        _ ≤ (Finset.range T).card := Finset.card_le_card hOsub
        _ = T := Finset.card_range T
    rw [sum_blockFourier_norm_sq b hHT]
    simp_rw [hb]
    simp
  have hsubsum :
      (∑ t ∈ O, ‖blockFourier T b (t : ℤ)‖ ^ 2) ≤
        ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hOsub (fun _ _ _ ↦ sq_nonneg _)
  rw [hOrbitSum, hParseval] at hsubsum
  have hH : (0 : ℝ) < H := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  have hsq : ‖blockFourier T b a‖ ^ 2 ≤ T := by
    nlinarith
  have hsqrt : (Real.sqrt T) ^ 2 = T := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [norm_nonneg (blockFourier T b a), Real.sqrt_nonneg T]

end

end NormalNumbers.VandeheyKorobov
