/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyClassEquidist

/-!
# The parity split: equidistribution for a PERIODIC automaton

The Raney transducer of `x ↦ D·x` has `det (M · B_j) = − det M`, so the sign of the determinant
is a deterministic period-2 phase: `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)` for the
phase-corrected automaton `rplusDelta`, and `1[stateAt lrDelta … i = t]` is supported on ONE
parity of `i`.  The joint (window, state) frequency of `lrDelta` is therefore the joint frequency
of the **product automaton**

    `prodStep δ : S × ZMod 2 → ℕ → S × ZMod 2`,   `(s, ε) ↦ (δ s a, ε + 1)`

at the state `(ι^p t, p)`.  `probes/raney_parity_split.py` confirms the answer is half the
unsigned one; this file is the proof.

## Why the plain pin cannot do it

`stateHorizonIntegral (prodStep δ) A n (d,η) (t,p) τ = 1[η+n=p] · stateHorizonIntegral δ A n d t τ`
oscillates in `n` between `0` and `≈ c·γ(A)`, so **no** constant `c'` pins it and
`classEquidistribution_of_pin` is unusable — the period-2 wall of `VandeheyRaneyReach` reappears
at the product.  The window-only half of the statement (`Σ_{i<n} (−1)^i 1[w_i = q] = o(n)`, the CF
analogue of "normal to base `b` ⇒ normal to base `b²`") cannot be bootstrapped from the state
statistics either: summing the signed identity over states gives `0 = o(n)`.

## What does work

Only the **variance** bound needs the pin, and it needs less than the pin gives.  Writing
`sel η p k := 1[η + k = p]`, the product automaton's deviation function factors through the
ORIGINAL automaton's events,

    `devFun (prodStep δ) (d,η) (t,p) q L k y = sel η p k · 1[J_k] − L · 1[W_k]`,

so the two-point integral is the same four masses as before with `sel`-coefficients.  Taking the
reference constant `L := c/2` (half the pin's constant), the constant parts cancel EXACTLY and
what survives is

    `mean(k, k') = e(k') · R(k)`,   `e(k') = ±1` alternating,   `|R(k)| ≤ 1`,

with `R` depending on `k` alone.  In the variance double sum the inner sum of `e(k')` over a
contiguous range is `O(1)`, so the mean part contributes `O(K)` and not `O(K²)`: the alternating
factor performs the cancellation that a constant pin would have performed termwise.  Hence
`∫ devAvg² = O(1/K)` again, and `classEquidistribution_of_variance` finishes.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyState VandeheyTwo

namespace VandeheyPar

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The product automaton -/

/-- The automaton `δ` with a parity counter attached. -/
def prodStep (δ : S → ℕ → S) : S × ZMod 2 → ℕ → S × ZMod 2 := fun s a => (δ s.1 a, s.2 + 1)

lemma runState_prodStep (δ : S → ℕ → S) (s : S × ZMod 2) (w : List ℕ) :
    runState (prodStep δ) s w = (runState δ s.1 w, s.2 + (w.length : ZMod 2)) := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih =>
      rw [runState_cons, runState_cons, ih, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      simp only [prodStep, List.length_cons, Nat.cast_add, Nat.cast_one]
      push_cast
      ring

lemma stateAt_prodStep (δ : S → ℕ → S) (s : S × ZMod 2) (x : ℝ) (i : ℕ) :
    stateAt (prodStep δ) s x i = (stateAt δ s.1 x i, s.2 + (i : ZMod 2)) := by
  rw [stateAt, stateAt, runState_prodStep, cfWord_length]

/-- The parity selector: `1` when the parity counter, started at `η`, reads `p` after `k`
digits. -/
def sel (η p : ZMod 2) (k : ℕ) : ℝ := if η + (k : ZMod 2) = p then 1 else 0

/-- The `±1` version of the selector. -/
def selSign (η p : ZMod 2) (k : ℕ) : ℝ := if η + (k : ZMod 2) = p then 1 else -1

lemma sel_eq (η p : ZMod 2) (k : ℕ) : sel η p k = (1 + selSign η p k) / 2 := by
  rw [sel, selSign]; split <;> norm_num

lemma sel_nonneg (η p : ZMod 2) (k : ℕ) : 0 ≤ sel η p k := by rw [sel]; split <;> norm_num

lemma sel_le_one (η p : ZMod 2) (k : ℕ) : sel η p k ≤ 1 := by rw [sel]; split <;> norm_num

lemma abs_sel_le_one (η p : ZMod 2) (k : ℕ) : |sel η p k| ≤ 1 := by
  rw [abs_of_nonneg (sel_nonneg η p k)]; exact sel_le_one η p k

lemma abs_selSign (η p : ZMod 2) (k : ℕ) : |selSign η p k| = 1 := by
  rw [selSign]; split <;> norm_num

/-- One digit flips the parity. -/
lemma selSign_succ (η p : ZMod 2) (k : ℕ) :
    selSign η p (k + 1) = - selSign η p k := by
  have key : ∀ a b : ZMod 2, (a + 1 = b) ↔ ¬ (a = b) := by decide
  have h : ((k + 1 : ℕ) : ZMod 2) = (k : ZMod 2) + 1 := by push_cast; ring
  rw [selSign, selSign, h, ← add_assoc]
  by_cases hk : η + (k : ZMod 2) = p
  · rw [if_neg (fun hc => ((key _ p).mp hc) hk), if_pos hk]
  · rw [if_pos ((key _ p).mpr hk), if_neg hk]; ring

/-- The selector's sign is a pure alternation. -/
lemma selSign_eq_mul_pow (η p : ZMod 2) (k : ℕ) :
    selSign η p k = selSign η p 0 * (-1 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [selSign_succ, ih, pow_succ]; ring

/-- **The alternating cancellation.**  The sign sums to `O(1)` over any contiguous range — this is
the one property that replaces the pin's termwise decay. -/
lemma abs_sum_selSign_le (η p : ZMod 2) (a b : ℕ) :
    |∑ i ∈ Finset.Ico a b, selSign η p i| ≤ 1 := by
  have hgeom : ∀ n : ℕ, |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i| ≤ 1 := by
    intro n
    rw [neg_one_geom_sum]
    split <;> norm_num
  have hrw : ∑ i ∈ Finset.Ico a b, selSign η p i
      = selSign η p 0 * ∑ i ∈ Finset.Ico a b, (-1 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => selSign_eq_mul_pow η p i
  rw [hrw, abs_mul, abs_selSign, one_mul]
  rcases le_or_gt a b with hab | hab
  · have hsub : ∑ i ∈ Finset.Ico a b, (-1 : ℝ) ^ i
        = (∑ i ∈ Finset.range b, (-1 : ℝ) ^ i) - ∑ i ∈ Finset.range a, (-1 : ℝ) ^ i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun i => (-1 : ℝ) ^ i) (Nat.zero_le a) hab]
      ring
    rw [hsub]
    rw [neg_one_geom_sum, neg_one_geom_sum]
    split <;> split <;> norm_num
  · rw [Finset.Ico_eq_empty (by omega)]
    simp

end VandeheyPar

end NormalNumbers
