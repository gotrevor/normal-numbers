/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetCWeight
import NormalNumbers.G4UnboundedTW

/-!
# Campaign B: the merged weight `w_{c,S}` for an *unbounded* tame `c`

`TWeight.weightS` (`G4SubsetCWeight`) needs a uniform bound `c ≤ C`, for the same two fields
the bounded `TWeight.weight` needed it: `ov_le` and `summable`.  Both are removed exactly as in
`G4UnboundedTW`:

* `ovB d = ω(d) + ∑_{p ∣ d} c_p` bounds both `overlapS ≤ ω(d)` and
  `overlapWN (coeffOn S c) ≤ ∑_{p ∣ d} c_p`, with no growth hypothesis;
* summability follows from `w_{c,S} ≤ w_c` pointwise and `summable_weightW_div_pow_tame`.

The pointwise domination `weightSN_le_weightN'` is also what lets the *unbounded* §4D far field
(`farAvgW_le_of_layer`, whose `hW` is an inequality since this lap) apply to `w_{c,S}`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

variable {S : ℕ → Prop} [DecidablePred S] {c : ℕ → ℕ}

/-- `Tame` is monotone in the coefficient vector. -/
lemma tame_mono {c c' : ℕ → ℕ} {A : ℝ} (hT : Tame c A) (h : ∀ p, c' p ≤ c p) : Tame c' A where
  one_le := hT.one_le
  tail := fun M => le_trans (Finset.sum_le_sum fun p hp => by
      have hprime := Nat.prime_of_mem_primesBelow hp
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
      have hcc : (c' p : ℝ) ≤ (c p : ℝ) := by exact_mod_cast h p
      have hp0 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      exact div_le_div_of_nonneg_right hcc hp0.le) (hT.tail M)
  pref := fun M => le_trans (Finset.sum_le_sum fun p _ => by exact_mod_cast h p) (hT.pref M)

/-- The `S`-restricted coefficients are pointwise below `c`. -/
lemma coeffOn_le_self (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) (p : ℕ) :
    coeffOn S c p ≤ c p := by
  unfold coeffOn; split_ifs; · exact le_rfl
  · exact Nat.zero_le _

lemma tame_coeffOn {A : ℝ} (hT : Tame c A) (S : ℕ → Prop) [DecidablePred S] :
    Tame (coeffOn S c) A := tame_mono hT (coeffOn_le_self S c)

/-- **`w_{c,S} ≤ w_c` pointwise**, with no hypothesis on `c`. -/
lemma weightSN_le_weightN' (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) (m : ℕ) :
    weightSN S c m ≤ weightN c m := by
  classical
  unfold weightSN weightN omegaSN
  refine Nat.add_le_add ?_ (Finset.sum_le_sum fun p _ =>
    Nat.mul_le_mul_right _ (coeffOn_le_self S c p))
  rw [cardDistinctFactors_eq_card_primeFactors]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma weightSW_le_weightW (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) (m : ℕ) :
    weightSW S c m ≤ weightW c m := by
  rw [weightSW_eq_cast, weightW_eq_cast]
  exact_mod_cast weightSN_le_weightN' S c m

namespace TWeight

/-- **The merged weight `w_{c,S}` as a `TWeight`**, for every tame `c` — no uniform bound. -/
noncomputable def weightSU (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) {A : ℝ}
    (hT : Tame c A) : TWeight where
  wN := weightSN S c
  ov := fun d m => (overlapS S d m : ℤ) - (overlapWN (coeffOn S c) d m : ℤ)
  ovB := fun d => d.primeFactors.card + ∑ p ∈ d.primeFactors, c p
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
    have h1 : (overlapS S d m : ℤ) ≤ (d.primeFactors.card : ℤ) := by
      exact_mod_cast le_trans (overlapS_le (S := S) d m) (overlap_le d m)
    have hmono : overlapWN (coeffOn S c) d m ≤ overlapWN c d m := by
      unfold overlapWN
      exact Finset.sum_le_sum fun p _ => coeffOn_le_self S c p
    have h2 : (overlapWN (coeffOn S c) d m : ℤ) ≤ ((∑ p ∈ d.primeFactors, c p : ℕ) : ℤ) := by
      exact_mod_cast le_trans hmono (overlapWN_le' c d m)
    have h3 : (0 : ℤ) ≤ (overlapS S d m : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (overlapWN (coeffOn S c) d m : ℤ) := Int.natCast_nonneg _
    have h5 : (0 : ℤ) ≤ (d.primeFactors.card : ℤ) := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ ((∑ p ∈ d.primeFactors, c p : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [Nat.cast_add, abs_le]
    omega
  ov_congr := fun d m m' h => by
    rw [overlapS_congr (S := S) d m m' h, overlapWN_congr (coeffOn S c) d m m' h]
  summable := fun b hb => by
    have hS := summable_weightW_div_pow_tame hb hT
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS
    have h0 : (0 : ℝ) < (b : ℝ) ^ n := by
      have hb0 : (2 : ℝ) ≤ b := by exact_mod_cast hb
      positivity
    have hle : ((weightSN S c n : ℕ) : ℝ) ≤ weightW c n := by
      rw [weightW_eq_cast]
      exact_mod_cast weightSN_le_weightN' S c n
    gcongr

@[simp] lemma weightSU_wN (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A)
    (m : ℕ) : (((weightSU S c hT).wN m : ℕ) : ℝ) = weightSW S c m := by
  rw [weightSW_eq_cast]; rfl

lemma weightSU_le (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A)
    (m : ℕ) : (((weightSU S c hT).wN m : ℕ) : ℝ) ≤ weightW c m := by
  rw [weightSU_wN]; exact weightSW_le_weightW S c m

lemma lambert_weightSU {b : ℕ} (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ) {A : ℝ}
    (hT : Tame c A) : (weightSU S c hT).lambert b = subsetWeightLambert S c b := by
  unfold lambert subsetWeightLambert
  exact tsum_congr fun n => by rw [weightSU_wN]

end TWeight

end NormalNumbers.G4
