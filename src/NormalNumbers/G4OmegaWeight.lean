/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TransportW
import NormalNumbers.G4WeightJunk

/-!
# G5: `Ω` as a `TWeight`, and the `ω`/`Ω` split the §4D budget must carry

`Ω(n)` — the number of prime factors **with multiplicity** — is *completely* additive, so its
§4A transport correction vanishes identically: `TWeight.cardFactors` is the `TWeight` with
`ov = 0`.  Everything §4A, §4B and §4C says about a frame carrying this weight therefore comes
for free from `G4TransportW` / `G4FrameW` (§4C never sees the weight: the small-prime vector is
the `ω`-vector on `smallPrimes R P₀`).

What is **not** free is §4D.  The frame's retained layer is the `ω`-vector, and
`Ω = ω + excess 1` with `excess 1 m = ∑_{p ∣ m} (v_p(m) − 1)`.  So the whole difference is one
more averaged remainder, and `G4WeightJunk` is where its size lives:
`excess 1 = frozenExcess P₀ + junk P₀`, the frozen part depending only on `m mod P₀` (hence
absorbable into the frame's translate `γ`) and the junk having a small sample mean at every
shift (`sum_junk_le`).

This module fixes the `TWeight` instance and the two elementary facts about the split that the
§4D port consumes.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert

namespace TWeight

/-- `Ω(n)/bⁿ` is summable for every base `b ≥ 2`. -/
lemma summable_cardFactors_div_pow {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun n : ℕ => ((Ω n : ℕ) : ℝ) / (b : ℝ) ^ n) := by
  have h := summable_weightW_div_pow (b := b) hb (c := fun _ => (1 : ℕ)) (C := 1)
    (fun _ => by norm_num) (by norm_num)
  exact h.congr (fun n => by rw [weightW_one])

/-- **`Ω` as a `TWeight`.**  Complete additivity makes the transport correction identically
zero, so `Ω`'s §4A is the degenerate case of `G4TransportW`. -/
def cardFactors : TWeight where
  wN := fun m => Ω m
  ov := fun _ _ => 0
  ovB := fun _ => 0
  mul_eq := fun d m hd hm => by
    simp only [add_zero]
    rw [ArithmeticFunction.cardFactors_mul hd hm]
    push_cast
    ring
  ov_le := fun _ _ => by simp
  ov_congr := fun _ _ _ _ => rfl
  summable := fun b hb => summable_cardFactors_div_pow hb

@[simp] lemma cardFactors_wN (m : ℕ) : (cardFactors.wN m : ℝ) = (Ω m : ℝ) := rfl

@[simp] lemma cardFactors_ov (d m : ℕ) : cardFactors.ov d m = 0 := rfl

lemma lambert_cardFactors {b : ℕ} :
    cardFactors.lambert b = weightLambert b (fun _ => (1 : ℕ)) := by
  rw [lambert, weightLambert]
  exact tsum_congr fun n => by rw [cardFactors_wN, weightW_one]

end TWeight

/-! ### The `ω`/`Ω` split: `Ω = ω + excess 1`

The three facts the §4D port needs, all pointwise. -/

/-- `Ω(m) = ω(m) + excess(m)` with unit coefficients — the split the remainder budget carries. -/
theorem cardFactors_eq_omegaR_add_excess (m : ℕ) :
    (Ω m : ℝ) = omegaR m + excess (fun _ => (1 : ℕ)) m := by
  rw [← weightW_one m, weightW]

/-- The excess is the integer `Ω − ω`. -/
theorem excess_one_eq_cast (m : ℕ) :
    excess (fun _ => (1 : ℕ)) m = ((Ω m - m.primeFactors.card : ℕ) : ℝ) := by
  have hle : m.primeFactors.card ≤ Ω m := by
    rw [ArithmeticFunction.cardFactors_apply, Nat.primeFactors]
    exact List.toFinset_card_le _
  have h := cardFactors_eq_omegaR_add_excess m
  rw [omegaR_eq] at h
  rw [Nat.cast_sub hle]
  linarith

end NormalNumbers.G4
