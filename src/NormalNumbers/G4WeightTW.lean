/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TransportW
import NormalNumbers.G4WeightInterface

/-!
# The general coefficient weight `w_c = ω + excess c` as a `TWeight`

`w_c(m) = ω(m) + ∑_{p ∣ m} c_p (v_p(m) − 1)` for a bounded coefficient vector `c_p ≤ C`.
Its transport correction is

  `ov_c(d,m) = ∑_{p ∣ d, p ∣ m} (1 − c_p)`,

which is **negative** as soon as some shared prime carries `c_p ≥ 2` — the reason
`TWeight.ov` is `ℤ`-valued.  Its size constant is `C` (or `1`, whichever is larger), and it is
periodic in `m` modulo the primes of `d` because only the divisibility pattern enters.

This gives §4A/§4B/§4C for `w_c` for free from `G4TransportW`/`G4FrameW`; §4D is the part that
still has to pay for `C` (the junk term is `C` times the `Ω` one).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert

/-- `∑_{p ∣ d, p ∣ m} c_p`, as a natural number. -/
def overlapWN (c : ℕ → ℕ) (d m : ℕ) : ℕ := ∑ p ∈ d.primeFactors.filter (fun p => p ∣ m), c p

@[simp] lemma overlapWN_cast (c : ℕ → ℕ) (d m : ℕ) :
    ((overlapWN c d m : ℕ) : ℝ) = overlapW c d m := by
  unfold overlapWN overlapW
  push_cast
  rfl

lemma overlapWN_le {c : ℕ → ℕ} {C : ℕ} (hC : ∀ p, c p ≤ C) (d m : ℕ) :
    overlapWN c d m ≤ C * d.primeFactors.card := by
  calc overlapWN c d m ≤ ∑ p ∈ d.primeFactors.filter (fun p => p ∣ m), C :=
        Finset.sum_le_sum fun p _ => hC p
    _ = C * (d.primeFactors.filter (fun p => p ∣ m)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ C * d.primeFactors.card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.filter_subset _ _))

lemma overlapWN_congr (c : ℕ → ℕ) (d k k' : ℕ) (h : ∀ p ∈ d.primeFactors, k ≡ k' [MOD p]) :
    overlapWN c d k = overlapWN c d k' := by
  unfold overlapWN
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (Nat.ModEq.dvd_iff (h p hp) (dvd_refl p)).1 hk⟩
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (Nat.ModEq.dvd_iff (h p hp) (dvd_refl p)).2 hk⟩

namespace TWeight

/-- **The general coefficient weight as a `TWeight`**, for `c_p ≤ C`. -/
noncomputable def weight (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C) : TWeight where
  wN := weightN c
  ov := fun d m => (overlap d m : ℤ) - (overlapWN c d m : ℤ)
  ovC := max C 1
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
    have h1 : overlap d m ≤ d.primeFactors.card := overlap_le d m
    have h2 : overlapWN c d m ≤ C * d.primeFactors.card := overlapWN_le hC d m
    have h1' : (overlap d m : ℤ) ≤ (d.primeFactors.card : ℤ) := by exact_mod_cast h1
    have h2' : (overlapWN c d m : ℤ) ≤ (C : ℤ) * (d.primeFactors.card : ℤ) := by
      exact_mod_cast h2
    have hC1 : (1 : ℤ) ≤ (max C 1 : ℕ) := by exact_mod_cast le_max_right C 1
    have hCC : (C : ℤ) ≤ ((max C 1 : ℕ) : ℤ) := by exact_mod_cast le_max_left C 1
    have hcard : (0 : ℤ) ≤ (d.primeFactors.card : ℤ) := by positivity
    rw [abs_le]
    constructor
    · nlinarith [Int.natCast_nonneg (overlap d m)]
    · nlinarith [Int.natCast_nonneg (overlapWN c d m)]
  ov_congr := fun d m m' h => by
    rw [overlap_congr d m m' h, overlapWN_congr c d m m' h]
  summable := fun b hb =>
    (summable_weightW_div_pow hb (C := (C : ℝ)) (fun p => by exact_mod_cast hC p)
      (by positivity)).congr (fun n => by rw [weightW_eq_cast])

@[simp] lemma weight_wN (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C) (m : ℕ) :
    ((weight c C hC).wN m : ℝ) = weightW c m := by rw [weightW_eq_cast]; rfl

lemma lambert_weight {b : ℕ} (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C) :
    (weight c C hC).lambert b = weightLambert b c := by
  unfold lambert weightLambert
  exact tsum_congr fun n => by rw [weight_wN]

end TWeight

end NormalNumbers.G4
