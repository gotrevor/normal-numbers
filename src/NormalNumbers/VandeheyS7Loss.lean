/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Word

/-!
# Exponential loss of memory, uniformly in the state

`VandeheyS7Merge` proved the two facts that make the Hilbert metric the right instrument here:
every two input digits give a state with strictly positive entries and determinant `1`, and its
Birkhoff coefficient is at most `3 − 2√2` **whatever the digits are**
(`gaussPair_birkhoffCoeff_le`).  `VandeheyS7Birkhoff.hdist_mob_le` then turned the coefficient into
an actual contraction of `hdist`.  This module assembles the two along a word:

`hdist_wordState_le` : after reading a word `w`, the Hilbert distance between the images of any two
points of `(0,∞)` is at most `(3 − 2√2)^⌊|w|/2⌋` times their original distance;

`hdist_runWord_le` : the same bound from **every** initial state, because a state is nonexpansive
(`mob_nonexpansive`), so the initial state can only shrink what the word produces.

That is asymptotic loss of memory with an explicit exponential rate, uniform over the (infinite)
state set — the replacement for the finite-chain merging Vandehey cites Saloff-Coste–Zúñiga for,
which `infinite_zPhi_abs_le_one` makes unavailable over `ℤ[φ]`.

## What it does and does not say

It bounds the DIAMETER of the image, uniformly in the initial state.  It never makes two
trajectories equal: pathwise merging is refuted here
(`conj_goldenRatio_integral_forces_diagonal`), and a bound on the image diameter is not a bound on
its LOCATION — that is the `no_window_function` trap, and it is the reason this lemma is an input to
a distributional argument and never a substitute for one.

## Guard rule

Content locator: `hdist_runWord_le_one_digit` — for a one-letter word the bound is trivial
(`(3−2√2)^0 = 1`), i.e. all the content sits in the pairing; and
`birkhoffCoeff_single_gaussBranch` (in `VandeheyS7Merge`) shows a single digit really does not
contract.  Degenerate cases: `kappa_pos` and `kappa_lt_one` pin `0 < 3 − 2√2 < 1`, so the bound
neither collapses to `0` (which would prove pathwise merging, refuted) nor is vacuous.
-/

namespace NormalNumbers.VandeheyS7

open Filter

lemma hdist_nonneg (x y : ℝ) : 0 ≤ hdist x y := abs_nonneg _

lemma kappa_pos : (0:ℝ) < 3 - 2 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

lemma kappa_lt_one : (3:ℝ) - 2 * Real.sqrt 2 < 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

namespace MobState

/-- The contraction of `VandeheyS7Birkhoff`, in `MobState` form. -/
theorem hdist_mob_state_le (s : MobState) (hapos : 0 < s.a) (hbpos : 0 < s.b) (hcpos : 0 < s.c)
    (hdet : 0 ≤ s.a * s.d - s.b * s.c) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hdist (s.mob x) (s.mob y) ≤ birkhoffCoeff s.a s.b s.c s.d * hdist x y :=
  hdist_mob_le hapos hbpos hcpos s.hd hdet hx hy

/-- **Exponential loss of memory along the input word.**  Each PAIR of digits contracts the Hilbert
metric by the universal factor `3 − 2√2`, so a word of length `n` contracts by `(3−2√2)^⌊n/2⌋`. -/
theorem hdist_wordState_le : ∀ (w : List ℕ) (x y : ℝ), 0 < x → 0 < y →
    hdist ((wordState w).mob x) ((wordState w).mob y)
      ≤ (3 - 2 * Real.sqrt 2) ^ (w.length / 2) * hdist x y
  | [], x, y, hx, hy => by
      simp only [List.length_nil, Nat.zero_div, pow_zero, one_mul]
      exact mob_nonexpansive _ hx hy
  | [_], x, y, hx, hy => by
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceDiv, pow_zero,
        one_mul]
      exact mob_nonexpansive _ hx hy
  | (a :: b :: rest), x, y, hx, hy => by
      have ih := hdist_wordState_le rest x y hx hy
      have hW : wordState (a :: b :: rest) = (gaussPair a b).comp (wordState rest) := by
        rw [wordState_cons, wordState_cons, gaussPair, comp_assoc]
      have hQx : 0 < (wordState rest).mob x := (wordState rest).mob_pos hx
      have hQy : 0 < (wordState rest).mob y := (wordState rest).mob_pos hy
      have hlen : (a :: b :: rest).length / 2 = rest.length / 2 + 1 := by
        simp only [List.length_cons]
        omega
      rw [hW, mob_comp _ _ hx.le, mob_comp _ _ hy.le, hlen, pow_succ]
      calc hdist ((gaussPair a b).mob ((wordState rest).mob x))
              ((gaussPair a b).mob ((wordState rest).mob y))
          ≤ birkhoffCoeff (gaussPair a b).a (gaussPair a b).b (gaussPair a b).c (gaussPair a b).d
              * hdist ((wordState rest).mob x) ((wordState rest).mob y) :=
            hdist_mob_state_le _ (gaussPair_a_pos a b) (gaussPair_b_pos a b) (gaussPair_c_pos a b)
              (by rw [gaussPair_det]; norm_num) hQx hQy
        _ ≤ (3 - 2 * Real.sqrt 2) * ((3 - 2 * Real.sqrt 2) ^ (rest.length / 2) * hdist x y) :=
            mul_le_mul (gaussPair_birkhoffCoeff_le a b) ih (hdist_nonneg _ _) kappa_pos.le
        _ = (3 - 2 * Real.sqrt 2) ^ (rest.length / 2) * (3 - 2 * Real.sqrt 2) * hdist x y := by
            ring

/-- **The same bound from every initial state.**  A state is nonexpansive, so it can only shrink
the spread the word produced: the contraction is a property of the input, not of the state. -/
theorem hdist_runWord_le (s : MobState) (w : List ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    hdist ((runWord s w).mob x) ((runWord s w).mob y)
      ≤ (3 - 2 * Real.sqrt 2) ^ (w.length / 2) * hdist x y := by
  refine le_trans ?_ (hdist_wordState_le w x y hx hy)
  rw [runWord_eq_comp]
  exact hdist_comp_le s _ hx hy

/-- Content locator: for a one-letter word the bound is `1`, so all the content of
`hdist_wordState_le` sits in the pairing of digits. -/
theorem hdist_runWord_le_one_digit (s : MobState) (a : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    hdist ((runWord s [a]).mob x) ((runWord s [a]).mob y) ≤ hdist x y := by
  have := hdist_runWord_le s [a] x y hx hy
  simpa using this

end MobState

/-- The rate: the contraction factor tends to `0` along the word length. -/
theorem tendsto_kappa_pow :
    Tendsto (fun k : ℕ => (3 - 2 * Real.sqrt 2) ^ k) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one kappa_pos.le kappa_lt_one

section Audit

#print axioms kappa_pos
#print axioms kappa_lt_one
#print axioms MobState.hdist_mob_state_le
#print axioms MobState.hdist_wordState_le
#print axioms MobState.hdist_runWord_le
#print axioms MobState.hdist_runWord_le_one_digit
#print axioms tendsto_kappa_pow

end Audit

end NormalNumbers.VandeheyS7
