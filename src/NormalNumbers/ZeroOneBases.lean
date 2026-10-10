/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NormalNumbers.LiteratureDigitsOfPowers

/-!
# The 82000 lane: what the two-base pairs say

`/create` session 2026-10-09, third member of the digit family (`ZeroOneBases2to5`).

Write `A_b` for the integers with only `0/1` digits in base `b`; it has `≈ X^(log 2 / log b)`
elements below `X`.  Base 2 is automatic and `A₄ ⊂ A₂`, so the conjecture lives on bases 3, 4, 5.

* **Exponent counting alone cannot work** (`zeroOneIn_three_of_nine`, `threeNine_infinite`): the
  random-model exponent of `A₃ ∩ A₉` is `log₃ 2 + log₉ 2 − 1 ≈ −0.054 < 0`, yet the intersection
  is all of `A₉`, infinite.  Any mechanism must use the multiplicative independence of the bases
  (Furstenberg).  That is exactly Burrell–Yu's (`Literature.BurrellYuFourFive`, via
  Shmerkin–Wu): `|A₄ ∩ A₅ ∩ [1, n]| ≤ C_ε n^ε`.  Their proof never uses base 3.
* **The pair (4, 5) already carries the conjecture.**  Its exponent is `≈ −0.069`, and exact
  search (`experiments/zero-one-bases/joint.py`, a top-down base-4 tree with an exact
  "next 0/1 integer in base 5" prune) finds only `{0, 1, 5, 16400, 82000} + {0, 1, 5}`-type
  sums (OEIS A263684) through `4⁸³³⁹ ≈ 10⁵⁰²⁰`.  `ZeroOneFourFive` states that list is complete;
  `zeroOneBases2to5_of_zeroOneFourFive` wires it to the 82000 conjecture.
* **The supercritical pair (3, 4) is open the other way** (Burrell–Yu: "it is already
  interesting to see whether `S(n) > 0` for infinitely many `n`").  `ZeroOneThreeFourInfinite`.
  Measured counts by base-4 length reach 40 300 at 54 digits, with whole runs of empty lengths
  (their slope windows).  630 of the 1039 solutions below `4³⁰` are primitive (not a
  digit-disjoint sum of smaller ones), so no semigroup generation.  The natural construction
  `N = 4ᵏ + r` (`r ∈ A₄` short) needs a shift `4ᵏ mod 3ᵐ` that is good for a sparse sumset
  covering; good shifts are a positive proportion, but which ones `4ᵏ` hits is decided by the
  *middle* base-3 digits of `4ᵏ`, the Erdős-type unknown.  Recorded as the wall.
-/

namespace NormalNumbers.ZeroOneBases

open NormalNumbers.Literature.DigitsOfPowers

theorem zeroOneIn_iff {b n : ℕ} (hb : 2 ≤ b) :
    ZeroOneIn b n ↔ n = 0 ∨ (n % b ≤ 1 ∧ ZeroOneIn b (n / b)) := by
  unfold ZeroOneIn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' (by omega) hn]
    simp [hn.ne']

/-- Base-9 digits `0/1` force base-3 digits `0/1` (each base-9 digit `d ≤ 1` is the ternary
pair `0d`). -/
theorem zeroOneIn_three_of_nine (n : ℕ) (h : ZeroOneIn 9 n) : ZeroOneIn 3 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (zeroOneIn_iff (by norm_num)).mp h with rfl | ⟨hr, hq⟩
    · exact (zeroOneIn_iff (by norm_num)).mpr (Or.inl rfl)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (zeroOneIn_iff (by norm_num)).mpr (Or.inl rfl)
    refine (zeroOneIn_iff (by norm_num)).mpr (Or.inr ⟨by omega, ?_⟩)
    have h3 : n / 3 = 3 * (n / 9) := by omega
    rcases Nat.eq_zero_or_pos (n / 9) with h0 | hpos
    · exact (zeroOneIn_iff (by norm_num)).mpr (Or.inl (by omega))
    refine (zeroOneIn_iff (by norm_num)).mpr (Or.inr ⟨by omega, ?_⟩)
    rw [show n / 3 / 3 = n / 9 by omega]
    exact ih _ (by omega) hq

theorem zeroOneIn_nine_pow (k : ℕ) : ZeroOneIn 9 (9 ^ k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    refine (zeroOneIn_iff (by norm_num)).mpr (Or.inr ⟨by simp [pow_succ], ?_⟩)
    rwa [pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- **The dependent-base sibling.**  `A₃ ∩ A₉` is infinite although its random-model exponent
`log₃ 2 + log₉ 2 − 1` is negative: dimension counting alone proves nothing. -/
theorem threeNine_infinite : {n : ℕ | ZeroOneIn 3 n ∧ ZeroOneIn 9 n}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 9 ^ k) := Nat.pow_right_injective (by norm_num)
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  exact ⟨zeroOneIn_three_of_nine _ (zeroOneIn_nine_pow k), zeroOneIn_nine_pow k⟩

namespace Literature

/-- **Burrell–Yu, Theorem 1.2** (J. Number Theory 226 (2021), arXiv:1905.00832; tier S): integers
with `0/1` digits in bases 4 and 5 number `O_ε(n^ε)` up to `n`.  The bound is for `n ≥ 1`: the
count includes `0`, so at `n = 0` the left side is `1` while `C · 0^ε = 0`
(`Review.not_burrellYuFourFiveUnrestricted`). -/
def BurrellYuFourFive : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    (((Finset.range (n + 1)).filter fun k => ZeroOneIn 4 k ∧ ZeroOneIn 5 k).card : ℝ) ≤
      C * (n : ℝ) ^ ε

end Literature

/-- The nine known integers with `0/1` digits in bases 4 and 5 (OEIS A263684). -/
def fourFiveList : List ℕ := [0, 1, 5, 16400, 16401, 16405, 82000, 82001, 82005]

theorem fourFiveList_spec : ∀ n ∈ fourFiveList, ZeroOneIn 4 n ∧ ZeroOneIn 5 n := by
  decide +kernel

/-- **The pair conjecture** (open, 90%; exponent `≈ −0.069`; no other solution below `4⁸³³⁹`). -/
def ZeroOneFourFive : Prop := ∀ n, ZeroOneIn 4 n → ZeroOneIn 5 n → n ∈ fourFiveList

/-- The base-4/5 pair alone gives the 82000 conjecture: of the nine, only `0, 1, 82000` are `0/1`
in base 3. -/
theorem zeroOneBases2to5_of_zeroOneFourFive (h : ZeroOneFourFive) : ZeroOneBases2to5 := by
  intro n hn _ h3 h4 h5
  have hmem := h n h4 h5
  revert h3 hn
  simp only [fourFiveList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **Burrell–Yu's question** (open, 97% true): infinitely many integers have `0/1` digits in both
base 3 and base 4.  Supercritical (exponent `≈ +0.131`). -/
def ZeroOneThreeFourInfinite : Prop := {n : ℕ | ZeroOneIn 3 n ∧ ZeroOneIn 4 n}.Infinite

/-! ## What the base-3 restriction buys (2026-10-10, review challenge)

Measured on the exact top-down tree (`experiments/zero-one-bases/width.py`), base-4 lengths
200–1399: the fraction of lengths whose tree survives `d` digits decays per digit like `0.889` for
bases {4, 5} and `0.558` for {3, 4, 5}, matching the random-model rates `4^(−0.069) = 0.908` and
`4^(−0.438) = 0.545`.  Deepest survival 57 vs 10.  But the tree *width* (the integer shadow of
the Shmerkin–Wu covering number) stays `O(1)` for both (max 6 vs 2 through length 400), so base 3
does nothing for the `n^ε` step: the loss there is in the proof, not the sets
(`FourFiveBoundedPerLength`).  What base 3 adds is a second slope coordinate: lengths with a
solution need `(L log₃ 4, L log₅ 4) mod 1` in a target of measure `≈ 0.545^d` at depth `d`, a
two-dimensional shrinking target.  Using it needs the orbit to equidistribute in `𝕋²`, i.e.
`JointSlopeIndependence`, which we do not know how to prove (Schanuel-type; Burrell–Yu assume
Schanuel for their digit-special theorem). -/

/-- **Uniform covering, conjectured from the width data** (85%): a bounded number of integers with
`0/1` digits in bases 4 and 5 in each `[4ᴸ, 4ᴸ⁺¹)`.  A Shmerkin–Wu bound without the `ε` would
give it; base 3 is not needed. -/
def FourFiveBoundedPerLength : Prop :=
  ∃ C : ℕ, ∀ L : ℕ, ((Finset.Ico (4 ^ L) (4 ^ (L + 1))).filter
    fun k => ZeroOneIn 4 k ∧ ZeroOneIn 5 k).card ≤ C

/-- **What the base-3 coordinate needs**: `1, log₃ 4, log₅ 4` are linearly independent over `ℚ`,
so the length orbit `L ↦ (L log₃ 4, L log₅ 4)` equidistributes in `𝕋²` (status unknown to us;
a relation would be `p log 3 log 5 + q log 4 log 5 + r log 3 log 4 = 0`). -/
def JointSlopeIndependence : Prop :=
  ∀ p q r : ℤ, (p : ℝ) + q * (Real.log 4 / Real.log 3) + r * (Real.log 4 / Real.log 5) = 0 →
    p = 0 ∧ q = 0 ∧ r = 0

end NormalNumbers.ZeroOneBases
