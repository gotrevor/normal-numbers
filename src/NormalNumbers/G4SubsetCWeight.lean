/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightTW
import NormalNumbers.G4SubsetWeight

/-!
# The two axes together: `w_{c,S} = ω_S + excess_{c·1_S}`

`ω_S` (campaign A) and `w_c` (G5) are the two closed cases `c = 0` and `S = everything` of one
weight

  `w_{c,S}(m) = #{p ∈ S : p ∣ m} + ∑_{p ∣ m, p ∈ S} c_p (v_p(m) − 1)`,

whose transport correction is `ov(d,m) = ∑_{p ∣ d, p ∣ m, p ∈ S} (1 − c_p)` — signed, exactly as
for `w_c`.  This module fixes the definition, the integrality, the transport identity and the
`TWeight` instance; §4D (the junk/far budgets, where the `S`-restriction meets the `C`-factor)
is the open part.

The `c`-side is *not* re-proved: writing `c'_p = c_p·1_S(p)`, the excess of `w_{c,S}` **is**
`excess c'`, so `G4WeightInterface`'s `excess_mul` applies verbatim.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- The `S`-restricted coefficient vector. -/
def coeffOn (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) (p : ℕ) : ℕ := if S p then c p else 0

lemma coeffOn_le {S : ℕ → Prop} [DecidablePred S] {c : ℕ → ℕ} {C : ℕ} (hC : ∀ p, c p ≤ C)
    (p : ℕ) : coeffOn S c p ≤ C := by
  unfold coeffOn
  split_ifs
  · exact hC p
  · exact Nat.zero_le _

variable (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ)

/-- `w_{c,S} = ω_S + excess_{c·1_S}`. -/
noncomputable def weightSW (m : ℕ) : ℝ := omegaS S m + excess (coeffOn S c) m

/-- The same weight as a natural number. -/
def weightSN (m : ℕ) : ℕ :=
  omegaSN S m + ∑ p ∈ m.primeFactors, coeffOn S c p * (m.factorization p - 1)

/-- The constant under test, `∑_n w_{c,S}(n)/bⁿ`. -/
noncomputable def subsetWeightLambert (b : ℕ) : ℝ := ∑' n : ℕ, weightSW S c n / (b : ℝ) ^ n

theorem weightSW_eq_cast (m : ℕ) : weightSW S c m = (weightSN S c m : ℝ) := by
  have h := weightW_eq_cast (coeffOn S c) m
  unfold weightW at h
  unfold weightSW weightSN omegaS
  unfold weightN omegaR at h
  push_cast at h ⊢
  have homega : ((omegaSN S m : ℕ) : ℝ)
      = (ArithmeticFunction.cardDistinctFactors m : ℝ) - (omegaR m - (omegaSN S m : ℕ)) := by
    rw [omegaR]
    ring
  linarith [h]

/-- **Instance `c = 0`**: `w_{0,S} = ω_S`. -/
@[simp] theorem weightSW_zero (m : ℕ) : weightSW S (fun _ => (0 : ℕ)) m = omegaS S m := by
  unfold weightSW
  have h : coeffOn S (fun _ => (0 : ℕ)) = fun _ => (0 : ℕ) := by
    funext p; unfold coeffOn; split_ifs <;> rfl
  rw [h, excess_zero_coeff]
  ring

/-- **Instance `S = everything`**: `w_{c,univ} = w_c`. -/
theorem weightSW_univ (m : ℕ) : weightSW (fun _ => True) c m = weightW c m := by
  unfold weightSW weightW
  have h : coeffOn (fun _ => True) c = c := by funext p; unfold coeffOn; simp
  rw [h, omegaS, omegaSN_univ, omegaR]

/-- **Transport for `w_{c,S}`.** -/
theorem weightSW_mul {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    weightSW S c (d * m)
      = weightSW S c m + weightSW S c d
        - ((overlapS S d m : ℝ) - overlapW (coeffOn S c) d m) := by
  unfold weightSW
  rw [omegaS_mul_eq d m hd hm, excess_mul (coeffOn S c) hd hm]
  ring

variable {S c}

lemma weightSN_le_weightN {C : ℕ} (hC : ∀ p, c p ≤ C) (m : ℕ) :
    weightSW S c m ≤ weightW (coeffOn S c) m := by
  unfold weightSW weightW
  have h : omegaS S m ≤ omegaR m := by
    rw [omegaS, omegaR_eq]
    have : (m.primeFactors.filter S).card ≤ m.primeFactors.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    unfold omegaSN
    exact_mod_cast this
  linarith

/-- **`w_{c,S}` as a `TWeight`**, with the signed correction `ov = overlapS − overlapW`. -/
noncomputable def TWeight.weightS {C : ℕ} (hC : ∀ p, c p ≤ C) : TWeight where
  wN := weightSN S c
  ov := fun d m => (overlapS S d m : ℤ) - (overlapWN (coeffOn S c) d m : ℤ)
  ovB := fun d => max C 1 * d.primeFactors.card
  mul_eq := fun d m hd hm => by
    have hR := weightSW_mul S c hd hm
    rw [weightSW_eq_cast, weightSW_eq_cast, weightSW_eq_cast,
      ← overlapWN_cast (coeffOn S c)] at hR
    have : ((weightSN S c (d * m) : ℤ) : ℝ)
        + (((overlapS S d m : ℤ) - (overlapWN (coeffOn S c) d m : ℤ) : ℤ) : ℝ)
        = ((weightSN S c m : ℤ) : ℝ) + ((weightSN S c d : ℤ) : ℝ) := by
      push_cast
      push_cast at hR
      linarith
    exact_mod_cast this
  ov_le := fun d m => by
    have h1 : overlapS S d m ≤ d.primeFactors.card :=
      le_trans (overlapS_le (S := S) d m) (overlap_le d m)
    have h2 : overlapWN (coeffOn S c) d m ≤ C * d.primeFactors.card :=
      overlapWN_le (coeffOn_le hC) d m
    have h1' : (overlapS S d m : ℤ) ≤ (d.primeFactors.card : ℤ) := by exact_mod_cast h1
    have h2' : (overlapWN (coeffOn S c) d m : ℤ) ≤ (C : ℤ) * (d.primeFactors.card : ℤ) := by
      exact_mod_cast h2
    have hC1 : (1 : ℤ) ≤ ((max C 1 : ℕ) : ℤ) := by exact_mod_cast le_max_right C 1
    have hCC : (C : ℤ) ≤ ((max C 1 : ℕ) : ℤ) := by exact_mod_cast le_max_left C 1
    have hcard : (0 : ℤ) ≤ (d.primeFactors.card : ℤ) := by positivity
    rw [Nat.cast_mul, abs_le]
    constructor
    · nlinarith [Int.natCast_nonneg (overlapS S d m)]
    · nlinarith [Int.natCast_nonneg (overlapWN (coeffOn S c) d m)]
  ov_congr := fun d m m' h => by
    rw [overlapS_congr (S := S) d m m' h, overlapWN_congr (coeffOn S c) d m m' h]
  summable := fun b hb => by
    have hS := summable_weightW_div_pow hb (c := coeffOn S c) (C := (C : ℝ))
      (fun p => by exact_mod_cast coeffOn_le hC p) (by positivity)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS
    have h0 : (0 : ℝ) < (b : ℝ) ^ n := by
      have : (0 : ℝ) < b := by
        have : (2 : ℝ) ≤ b := by exact_mod_cast hb
        linarith
      positivity
    rw [div_le_div_iff_of_pos_right h0, ← weightSW_eq_cast]
    exact weightSN_le_weightN hC n

@[simp] lemma TWeight.weightS_wN {C : ℕ} (hC : ∀ p, c p ≤ C) (m : ℕ) :
    ((TWeight.weightS (S := S) hC).wN m : ℝ) = weightSW S c m := by rw [weightSW_eq_cast]; rfl

lemma TWeight.lambert_weightS {b C : ℕ} (hC : ∀ p, c p ≤ C) :
    (TWeight.weightS (S := S) hC).lambert b = subsetWeightLambert S c b := by
  unfold TWeight.lambert subsetWeightLambert
  exact tsum_congr fun n => by rw [TWeight.weightS_wN (S := S) hC]

end NormalNumbers.G4
