/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightTW
import NormalNumbers.G4UnboundedJunk

/-!
# Campaign B: the unbounded coefficient weight as a `TWeight`

`TWeight.weight c C hC` needs `c ≤ C` for two of its fields: `ov_le` (through
`ovB d = max C 1 · ω(d)`) and `summable`.  Neither actually needs a *uniform* bound:

* B0 replaced `|ov d m| ≤ ovC·ω(d)` by a per-`d` bound `|ov d m| ≤ ovB d`, and
  `ov_c(d,m) = ∑_{p∣d,p∣m}(1−c_p)` is bounded by `ω(d) + ∑_{p∣d} c_p` — a finite quantity for
  *every* `c`, with no growth hypothesis at all;
* summability follows from `Tame`'s linear prefix bound (`weightW_le_tame`,
  `summable_weightW_div_pow_tame`).

So `TWeight.weightU c hT` exists for every tame `c`, and §4A/§4B/§4C are free for it — the
whole analytic route A–C was made weight-generic in campaign A.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- `∑_{p ∣ d, p ∣ m} c_p ≤ ∑_{p ∣ d} c_p` — the per-`d` bound B0 asks for. -/
lemma overlapWN_le' (c : ℕ → ℕ) (d m : ℕ) : overlapWN c d m ≤ ∑ p ∈ d.primeFactors, c p := by
  unfold overlapWN
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

namespace TWeight

/-- **The unbounded coefficient weight as a `TWeight`**, for every tame `c`. -/
noncomputable def weightU (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A) : TWeight where
  wN := weightN c
  ov := fun d m => (overlap d m : ℤ) - (overlapWN c d m : ℤ)
  ovB := fun d => d.primeFactors.card + ∑ p ∈ d.primeFactors, c p
  mul_eq := fun d m hd hm => by
    have hR : weightW c (d * m)
        = weightW c m + weightW c d - ((overlap d m : ℝ) - overlapW c d m) :=
      weightW_mul c hd hm
    rw [weightW_eq_cast, weightW_eq_cast, weightW_eq_cast, ← overlapWN_cast] at hR
    have : ((weightN c (d * m) : ℤ) : ℝ) + (((overlap d m : ℤ) - (overlapWN c d m : ℤ) : ℤ) : ℝ)
        = ((weightN c m : ℤ) : ℝ) + ((weightN c d : ℤ) : ℝ) := by push_cast; push_cast at hR
                                                                  linarith
    exact_mod_cast this
  ov_le := fun d m => by
    have h1 : (overlap d m : ℤ) ≤ (d.primeFactors.card : ℤ) := by
      exact_mod_cast overlap_le d m
    have h2 : (overlapWN c d m : ℤ) ≤ ((∑ p ∈ d.primeFactors, c p : ℕ) : ℤ) := by
      exact_mod_cast overlapWN_le' c d m
    have h3 : (0 : ℤ) ≤ (overlap d m : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (overlapWN c d m : ℤ) := Int.natCast_nonneg _
    have h5 : (0 : ℤ) ≤ (d.primeFactors.card : ℤ) := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ ((∑ p ∈ d.primeFactors, c p : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [Nat.cast_add, abs_le]
    omega
  ov_congr := fun d m m' h => by
    rw [overlap_congr d m m' h, overlapWN_congr c d m m' h]
  summable := fun b hb =>
    (summable_weightW_div_pow_tame hb hT).congr (fun n => by rw [weightW_eq_cast])

@[simp] lemma weightU_wN (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A) (m : ℕ) :
    ((weightU c hT).wN m : ℝ) = weightW c m := by rw [weightW_eq_cast]; rfl

lemma lambert_weightU {b : ℕ} (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A) :
    (weightU c hT).lambert b = weightLambert b c := by
  unfold lambert weightLambert
  exact tsum_congr fun n => by rw [weightU_wN]

/-- The bounded instance is the tame one: same `wN`, same `ov`, so the two `TWeight`s have the
same Lambert constant and the same §4A output. -/
lemma weightU_wN_eq_weight_wN (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C) {A : ℝ} (hT : Tame c A)
    (m : ℕ) : (weightU c hT).wN m = (weight c C hC).wN m := rfl

end TWeight

end NormalNumbers.G4
