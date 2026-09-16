/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedTW

/-!
# The master additive weight `w_{a,c}(m) = ∑_{p ∣ m} (a_p + c_p(v_p(m) − 1))`

`G4WeightInterface` records why this is the exact class for which the affine transport identity
holds, and that everything proved so far takes `a_p = 1` (or `a = 1_S`), because §4C's Fourier
control is stated for the *indicator* small-prime vector.  This module builds the **arithmetic**
layer for a general bounded `a`: the weight, its integrality, the transport identity, and the
`TWeight` instance — none of which sees §4C.  What is left for the general `a` is exactly the
weighted small-prime vector of §4C, isolated in `G4WeightAVector`.

The arithmetic is free because `∑_{p ∣ m} a_p` is `PrimeLambert.omegaW a m`, whose transport
(`omegaW_mul`) and periodicity (`overlapW_congr`) are already proved for an arbitrary `a`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- **The master additive weight**, `w_{a,c} = ∑_{p∣m} a_p + ∑_{p∣m} c_p(v_p(m) − 1)`. -/
noncomputable def weightAW (a c : ℕ → ℕ) (m : ℕ) : ℝ := omegaW a m + excess c m

/-- The same weight as a natural number. -/
def weightAN (a c : ℕ → ℕ) (m : ℕ) : ℕ :=
  (∑ p ∈ m.primeFactors, a p) + ∑ p ∈ m.primeFactors, c p * (m.factorization p - 1)

/-- The constant under test, `∑_n w_{a,c}(n)/bⁿ`. -/
noncomputable def weightALambert (b : ℕ) (a c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, weightAW a c n / (b : ℝ) ^ n

theorem weightAW_eq_cast (a c : ℕ → ℕ) (m : ℕ) : weightAW a c m = (weightAN a c m : ℝ) := by
  unfold weightAW weightAN omegaW
  rw [excess_eq]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : 1 ≤ m.factorization p :=
    ((Nat.mem_primeFactors.1 hp).1.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hp).2.2).1
      (Nat.mem_primeFactors.1 hp).2.1
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- **Instance `a = 1`**: the campaign-B weight. -/
theorem weightAW_one (c : ℕ → ℕ) (m : ℕ) : weightAW (fun _ => 1) c m = weightW c m := by
  unfold weightAW weightW
  rw [omegaW_one_coeff]

/-- **Instance `a = 1_S`**: the merged subset weight. -/
theorem weightAW_indicator (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) (m : ℕ) :
    weightAW (fun p => if S p then 1 else 0) c m = omegaS S m + excess c m := by
  unfold weightAW omegaW omegaS omegaSN
  congr 1
  have : ∀ p, ((if S p then (1:ℕ) else 0 : ℕ) : ℝ) = if S p then (1:ℝ) else 0 := by
    intro p; split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp

/-- **Transport for `w_{a,c}`.** -/
theorem weightAW_mul (a c : ℕ → ℕ) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    weightAW a c (d * m)
      = weightAW a c m + weightAW a c d - (overlapW a d m - overlapW c d m) := by
  unfold weightAW
  rw [omegaW_mul a hd hm, excess_mul c hd hm]
  ring

/-- `∑_{p ∣ d, p ∣ m} a_p`, as a natural number. -/
lemma overlapWN_mono {a c : ℕ → ℕ} (h : ∀ p, a p ≤ c p) (d m : ℕ) :
    overlapWN a d m ≤ overlapWN c d m :=
  Finset.sum_le_sum fun p _ => h p

lemma weightAN_le {a c : ℕ → ℕ} {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (m : ℕ) :
    weightAN a c m ≤ (Ca + 1) * weightN c m := by
  unfold weightAN weightN
  have h1 : ∑ p ∈ m.primeFactors, a p ≤ Ca * m.primeFactors.card := by
    calc ∑ p ∈ m.primeFactors, a p ≤ ∑ _p ∈ m.primeFactors, Ca :=
          Finset.sum_le_sum fun p _ => hCa p
      _ = m.primeFactors.card * Ca := by rw [Finset.sum_const, smul_eq_mul]
      _ = Ca * m.primeFactors.card := by ring
  have h2 : m.primeFactors.card = ArithmeticFunction.cardDistinctFactors m := by
    rw [cardDistinctFactors_eq_card_primeFactors]
  rw [h2] at h1
  nlinarith [Nat.zero_le (∑ p ∈ m.primeFactors, c p * (m.factorization p - 1)),
    Nat.zero_le (ArithmeticFunction.cardDistinctFactors m)]

namespace TWeight

/-- **The master weight as a `TWeight`**, for bounded `a` and tame `c`. -/
noncomputable def weightA (a c : ℕ → ℕ) {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) {A : ℝ}
    (hT : Tame c A) : TWeight where
  wN := weightAN a c
  ov := fun d m => (overlapWN a d m : ℤ) - (overlapWN c d m : ℤ)
  ovB := fun d => Ca * d.primeFactors.card + ∑ p ∈ d.primeFactors, c p
  mul_eq := fun d m hd hm => by
    have hR := weightAW_mul a c hd hm
    rw [weightAW_eq_cast, weightAW_eq_cast, weightAW_eq_cast,
      ← overlapWN_cast a, ← overlapWN_cast c] at hR
    have : ((weightAN a c (d * m) : ℤ) : ℝ)
        + (((overlapWN a d m : ℤ) - (overlapWN c d m : ℤ) : ℤ) : ℝ)
        = ((weightAN a c m : ℤ) : ℝ) + ((weightAN a c d : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  ov_le := fun d m => by
    have h1 : (overlapWN a d m : ℤ) ≤ ((Ca * d.primeFactors.card : ℕ) : ℤ) := by
      exact_mod_cast overlapWN_le hCa d m
    have h2 : (overlapWN c d m : ℤ) ≤ ((∑ p ∈ d.primeFactors, c p : ℕ) : ℤ) := by
      exact_mod_cast overlapWN_le' c d m
    have h3 : (0 : ℤ) ≤ (overlapWN a d m : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (overlapWN c d m : ℤ) := Int.natCast_nonneg _
    rw [Nat.cast_add, abs_le]
    omega
  ov_congr := fun d m m' h => by
    rw [overlapWN_congr a d m m' h, overlapWN_congr c d m m' h]
  summable := fun b hb => by
    have hS := (summable_weightW_div_pow_tame hb hT).mul_left ((Ca : ℝ) + 1)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS
    have hb0 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have h0 : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    have hle : ((weightAN a c n : ℕ) : ℝ) ≤ ((Ca : ℝ) + 1) * weightW c n := by
      rw [weightW_eq_cast]
      have := weightAN_le hCa (c := c) n
      have hc : ((weightAN a c n : ℕ) : ℝ) ≤ (((Ca + 1) * weightN c n : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at hc
      linarith
    calc ((weightAN a c n : ℕ) : ℝ) / (b : ℝ) ^ n
        ≤ (((Ca : ℝ) + 1) * weightW c n) / (b : ℝ) ^ n := by gcongr
      _ = ((Ca : ℝ) + 1) * (weightW c n / (b : ℝ) ^ n) := by ring

@[simp] lemma weightA_wN (a c : ℕ → ℕ) {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) {A : ℝ} (hT : Tame c A)
    (m : ℕ) : (((weightA a c hCa hT).wN m : ℕ) : ℝ) = weightAW a c m := by
  rw [weightAW_eq_cast]; rfl

lemma lambert_weightA {b : ℕ} (a c : ℕ → ℕ) {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) {A : ℝ}
    (hT : Tame c A) : (weightA a c hCa hT).lambert b = weightALambert b a c := by
  unfold lambert weightALambert
  exact tsum_congr fun n => by rw [weightA_wN]

end TWeight

end NormalNumbers.G4
