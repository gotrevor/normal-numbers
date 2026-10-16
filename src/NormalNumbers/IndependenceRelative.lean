/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive
import NormalNumbers.AdderBaseG
import NormalNumbers.MahlerLowerBoundBackground
import Architect
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Independence-relative digit disjunctions

Ren, 2026-10-05, `/create`.  The two-track adder theorems
(`Adder.adder_sixfold_disjunction_universal`) hold for every pair not both rational: their carry
automaton *collapses* (every live component is a simple cycle).  Most families do not collapse.
A family that fails can still hold for every pair off finitely many rational lines: it is enough
that each non-cycle live component is **degenerate**, i.e. some combination `aX + bY` has an
eventually periodic digit stream on every path through it (`experiments/independence_relative.py`,
a product-with-carry-transducer phase check; known-answer controls in
`test_independence_relative.py`).  Of 3621 random base-3 families (three single-digit channels,
coefficients in `[-2, 2]`, seed 20261005), 1033 are of this kind and 131 have a witness line that
is not a channel direction (the rest restate "an irrational number has some digit").  The
universal engine certifies none of them.

This is the first place where the constants matter to the carry engine, and it is in the shape of
the `π + e` / `π e` theorem: for `(π, e)` the statement reads "a digit disjunction holds, **or**
`e − 2π` is rational", and both halves are open (`pi_e_disjunction`).

The cleanest member (hand-proved below in English, found by the probe):

> base 3: if `Y − 2X` is irrational, then `X` has the digit `2` infinitely often, or `Y` has `1`,
> or `Y − X` has `2`.

It fails on the line: `X` with digits in `{0, 1}` and `Y = 2X` satisfy all three avoidances
(`exists_counterexample_on_line`).  Read as Cantor-set arithmetic: if `a ∈ C₀₁`, `b ∈ C₀₂` and
`b − a ∈ C₀₁` (tails), then `b = 2a` up to a rational.
-/

namespace NormalNumbers.IndependenceRelative

open NormalNumbers

/-- Digit `d` occurs infinitely often in the base-`b` expansion of `x`. -/
def DigitIO (b : ℕ) (x : ℝ) (d : ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ OccursAt b x [d] n

/-- **The ternary line theorem.**  Confidence 90% (statement faithfulness to the hand proof;
the hand proof itself is short and checked against the automaton verdict).

English proof.  Suppose all three avoidances hold past some position.  Then the tails have
`xᵢ ∈ {0,1}`, `yᵢ = 2uᵢ` with `uᵢ ∈ {0,1}`.  Subtract digitwise: `eᵢ = 2uᵢ − xᵢ ∈ {−1,0,1,2}`,
and the digits of `Y − X` come from `eᵢ + cᵢ₊₁` with borrows `c ∈ {−1, 0}` flowing from deep to
shallow.  Avoiding the digit `2` forbids `(e, c) = (2, 0), (0, −1), (−1, 0)`.  So `c = 0` forces
`e ∈ {0,1}` and the next shallower borrow `0`; `c = −1` forces `e ∈ {−1, 1, 2}`, staying at `−1`
only on `e = −1`.  A `0` borrow therefore propagates to every shallower position.  If borrows are
eventually `−1`, then `e ≡ −1`, i.e. `x ≡ 1`, `u ≡ 0`, and `X, Y` are rational, so `Y − 2X` is
too.  Otherwise the borrow is `0` throughout the tail and `eᵢ ∈ {0,1}`, which forces `uᵢ = xᵢ`:
the tails of `Y` and `2X` agree with no carries, so `Y − 2X` is rational.  Contradiction. -/
@[blueprint (title := "Ternary line theorem: X has 2, Y has 1, or Y - X has 2, unless Y - 2X is rational")]
theorem ternary_line (X Y : ℝ) (h : Irrational (Y - 2 * X)) :
    DigitIO 3 X 2 ∨ DigitIO 3 Y 1 ∨ DigitIO 3 (Y - X) 2 := by
  by_contra havoid
  push Not at havoid
  obtain ⟨hXio, hYio, hZio⟩ := havoid
  unfold DigitIO at hXio hYio hZio
  push Not at hXio hYio hZio
  obtain ⟨NX, hX⟩ := hXio
  obtain ⟨NY, hY⟩ := hYio
  obtain ⟨NZ, hZ⟩ := hZio
  let N := max NX (max NY NZ)
  have hX' : ∀ m, N ≤ m → ¬ OccursAt 3 X [2] m := by
    intro m hm
    exact hX m (le_trans (le_max_left _ _) hm)
  have hY' : ∀ m, N ≤ m → ¬ OccursAt 3 Y [1] m := by
    intro m hm
    exact hY m (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hm))
  have hZ' : ∀ m, N ≤ m → ¬ OccursAt 3 (Y - X) [2] m := by
    intro m hm
    exact hZ m (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hm))
  have hdigit {L : ℝ} {d m : ℕ} (hm : ¬ OccursAt 3 L [d] m) :
      (Adder.gdigit 3 L m).toNat ≠ d := by
    intro heq
    apply hm
    rw [Adder.occursAt_iff_winListG 3 (by norm_num)]
    simpa using heq
  let B : ℕ → ℤ := Adder.carryTG 3 (-1) 1 X Y
  have hBbounds (m : ℕ) : -1 ≤ B m ∧ B m ≤ 0 := by
    exact ⟨Adder.carryTG_nonneg' 3 (-1) 1 X Y m,
      Adder.carryTG_le' 3 (-1) 1 X Y m (by norm_num)⟩
  have hminus_next (m : ℕ) (hm : N ≤ m) (hb : B m = -1) : B (m + 1) = -1 := by
    have hx0 := Adder.gdigit_nonneg 3 (by norm_num) X m
    have hx1 := Adder.gdigit_lt 3 (by norm_num) X m
    have hy0 := Adder.gdigit_nonneg 3 (by norm_num) Y m
    have hy1 := Adder.gdigit_lt 3 (by norm_num) Y m
    have hz0 := Adder.gdigit_nonneg 3 (by norm_num) (Y - X) m
    have hz1 := Adder.gdigit_lt 3 (by norm_num) (Y - X) m
    have hxn := hdigit (hX' m hm)
    have hyn := hdigit (hY' m hm)
    have hzn := hdigit (hZ' m hm)
    have hb' := hBbounds (m + 1)
    have hcol := Adder.carryG_column 3 (-1) 1 X Y m
    norm_num at hcol
    rw [show -X + Y = Y - X by ring] at hcol
    change Adder.carryTG 3 (-1) 1 X Y m = -1 at hb
    change (-1 : ℤ) ≤ Adder.carryTG 3 (-1) 1 X Y (m + 1) ∧
      Adder.carryTG 3 (-1) 1 X Y (m + 1) ≤ 0 at hb'
    change Adder.carryTG 3 (-1) 1 X Y (m + 1) = -1
    have hxnZ : Adder.gdigit 3 X m ≠ 2 := by intro heq; apply hxn; omega
    have hynZ : Adder.gdigit 3 Y m ≠ 1 := by intro heq; apply hyn; omega
    have hznZ : Adder.gdigit 3 (Y - X) m ≠ 2 := by intro heq; apply hzn; omega
    omega
  have htarget_const (m : ℕ) (hm : N ≤ m) (s : ℤ)
      (hs : s = -1 ∨ s = 0) (h0 : B m = s) (h1 : B (m + 1) = s)
      (h2 : B (m + 2) = s) (h3 : B (m + 3) = s) :
      Adder.gdigit 3 (Y - 2 * X) (m + 1) = Adder.gdigit 3 (Y - 2 * X) m := by
    have hm1 : N ≤ m + 1 := by omega
    have hm2 : N ≤ m + 2 := by omega
    have hx0 := Adder.gdigit_nonneg 3 (by norm_num) X m
    have hx1 := Adder.gdigit_lt 3 (by norm_num) X m
    have hy0 := Adder.gdigit_nonneg 3 (by norm_num) Y m
    have hy1 := Adder.gdigit_lt 3 (by norm_num) Y m
    have hz0 := Adder.gdigit_nonneg 3 (by norm_num) (Y - X) m
    have hz1 := Adder.gdigit_lt 3 (by norm_num) (Y - X) m
    have hx0' := Adder.gdigit_nonneg 3 (by norm_num) X (m + 1)
    have hx1' := Adder.gdigit_lt 3 (by norm_num) X (m + 1)
    have hy0' := Adder.gdigit_nonneg 3 (by norm_num) Y (m + 1)
    have hy1' := Adder.gdigit_lt 3 (by norm_num) Y (m + 1)
    have hz0' := Adder.gdigit_nonneg 3 (by norm_num) (Y - X) (m + 1)
    have hz1' := Adder.gdigit_lt 3 (by norm_num) (Y - X) (m + 1)
    have hx0'' := Adder.gdigit_nonneg 3 (by norm_num) X (m + 2)
    have hx1'' := Adder.gdigit_lt 3 (by norm_num) X (m + 2)
    have hy0'' := Adder.gdigit_nonneg 3 (by norm_num) Y (m + 2)
    have hy1'' := Adder.gdigit_lt 3 (by norm_num) Y (m + 2)
    have hz0'' := Adder.gdigit_nonneg 3 (by norm_num) (Y - X) (m + 2)
    have hz1'' := Adder.gdigit_lt 3 (by norm_num) (Y - X) (m + 2)
    have hxn := hdigit (hX' m hm)
    have hyn := hdigit (hY' m hm)
    have hzn := hdigit (hZ' m hm)
    have hxn' := hdigit (hX' (m + 1) hm1)
    have hyn' := hdigit (hY' (m + 1) hm1)
    have hzn' := hdigit (hZ' (m + 1) hm1)
    have hxn'' := hdigit (hX' (m + 2) hm2)
    have hyn'' := hdigit (hY' (m + 2) hm2)
    have hzn'' := hdigit (hZ' (m + 2) hm2)
    have hbc := Adder.carryG_column 3 (-1) 1 X Y m
    have hbc' := Adder.carryG_column 3 (-1) 1 X Y (m + 1)
    have hbc'' := Adder.carryG_column 3 (-1) 1 X Y (m + 2)
    have hc0 := Adder.carryTG_nonneg' 3 (-2) 1 X Y m
    have hc1 := Adder.carryTG_le' 3 (-2) 1 X Y m (by norm_num)
    have hc0' := Adder.carryTG_nonneg' 3 (-2) 1 X Y (m + 1)
    have hc1' := Adder.carryTG_le' 3 (-2) 1 X Y (m + 1) (by norm_num)
    have hc0'' := Adder.carryTG_nonneg' 3 (-2) 1 X Y (m + 2)
    have hc1'' := Adder.carryTG_le' 3 (-2) 1 X Y (m + 2) (by norm_num)
    have hc0''' := Adder.carryTG_nonneg' 3 (-2) 1 X Y (m + 3)
    have hc1''' := Adder.carryTG_le' 3 (-2) 1 X Y (m + 3) (by norm_num)
    have hw0 := Adder.gdigit_nonneg 3 (by norm_num) (Y - 2 * X) m
    have hw1 := Adder.gdigit_lt 3 (by norm_num) (Y - 2 * X) m
    have hw0' := Adder.gdigit_nonneg 3 (by norm_num) (Y - 2 * X) (m + 1)
    have hw1' := Adder.gdigit_lt 3 (by norm_num) (Y - 2 * X) (m + 1)
    have hw0'' := Adder.gdigit_nonneg 3 (by norm_num) (Y - 2 * X) (m + 2)
    have hw1'' := Adder.gdigit_lt 3 (by norm_num) (Y - 2 * X) (m + 2)
    have hcc := Adder.carryG_column 3 (-2) 1 X Y m
    have hcc' := Adder.carryG_column 3 (-2) 1 X Y (m + 1)
    have hcc'' := Adder.carryG_column 3 (-2) 1 X Y (m + 2)
    norm_num at hbc hbc' hbc'' hcc hcc' hcc'' hc0 hc1 hc0' hc1' hc0'' hc1'' hc0''' hc1'''
    rw [show m + 1 + 1 = m + 2 by omega] at hbc' hcc'
    rw [show m + 2 + 1 = m + 3 by omega] at hbc'' hcc''
    rw [show -X + Y = Y - X by ring] at hbc hbc' hbc''
    rw [show -(2 * X) + Y = Y - 2 * X by ring] at hcc hcc' hcc''
    change Adder.carryTG 3 (-1) 1 X Y m = s at h0
    change Adder.carryTG 3 (-1) 1 X Y (m + 1) = s at h1
    change Adder.carryTG 3 (-1) 1 X Y (m + 2) = s at h2
    change Adder.carryTG 3 (-1) 1 X Y (m + 3) = s at h3
    have hxnZ : Adder.gdigit 3 X m ≠ 2 := by intro heq; apply hxn; omega
    have hynZ : Adder.gdigit 3 Y m ≠ 1 := by intro heq; apply hyn; omega
    have hznZ : Adder.gdigit 3 (Y - X) m ≠ 2 := by intro heq; apply hzn; omega
    have hxnZ' : Adder.gdigit 3 X (m + 1) ≠ 2 := by intro heq; apply hxn'; omega
    have hynZ' : Adder.gdigit 3 Y (m + 1) ≠ 1 := by intro heq; apply hyn'; omega
    have hznZ' : Adder.gdigit 3 (Y - X) (m + 1) ≠ 2 := by intro heq; apply hzn'; omega
    have hxnZ'' : Adder.gdigit 3 X (m + 2) ≠ 2 := by intro heq; apply hxn''; omega
    have hynZ'' : Adder.gdigit 3 Y (m + 2) ≠ 1 := by intro heq; apply hyn''; omega
    have hznZ'' : Adder.gdigit 3 (Y - X) (m + 2) ≠ 2 := by intro heq; apply hzn''; omega
    have hc_cases : Adder.carryTG 3 (-2) 1 X Y m = -2 ∨
        Adder.carryTG 3 (-2) 1 X Y m = -1 ∨ Adder.carryTG 3 (-2) 1 X Y m = 0 := by omega
    have hc_cases' : Adder.carryTG 3 (-2) 1 X Y (m + 1) = -2 ∨
        Adder.carryTG 3 (-2) 1 X Y (m + 1) = -1 ∨
          Adder.carryTG 3 (-2) 1 X Y (m + 1) = 0 := by omega
    have hc_cases'' : Adder.carryTG 3 (-2) 1 X Y (m + 2) = -2 ∨
        Adder.carryTG 3 (-2) 1 X Y (m + 2) = -1 ∨
          Adder.carryTG 3 (-2) 1 X Y (m + 2) = 0 := by omega
    rcases hs with rfl | rfl
    · have ha : -(2 * Adder.gdigit 3 X m) + Adder.gdigit 3 Y m = -2 := by omega
      have ha' : -(2 * Adder.gdigit 3 X (m + 1)) +
          Adder.gdigit 3 Y (m + 1) = -2 := by omega
      have ha'' : -(2 * Adder.gdigit 3 X (m + 2)) +
          Adder.gdigit 3 Y (m + 2) = -2 := by omega
      have heq : -2 + Adder.carryTG 3 (-2) 1 X Y (m + 1) =
          Adder.gdigit 3 (Y - 2 * X) m + 3 * Adder.carryTG 3 (-2) 1 X Y m := by
        omega
      have heq' : -2 + Adder.carryTG 3 (-2) 1 X Y (m + 2) =
          Adder.gdigit 3 (Y - 2 * X) (m + 1) +
            3 * Adder.carryTG 3 (-2) 1 X Y (m + 1) := by omega
      rcases hc_cases with hc | hc | hc <;>
        rcases hc_cases' with hc' | hc' | hc' <;>
        rcases hc_cases'' with hc'' | hc'' | hc'' <;> omega
    · have ha : -(2 * Adder.gdigit 3 X m) + Adder.gdigit 3 Y m = 0 := by omega
      have ha' : -(2 * Adder.gdigit 3 X (m + 1)) +
          Adder.gdigit 3 Y (m + 1) = 0 := by omega
      have ha'' : -(2 * Adder.gdigit 3 X (m + 2)) +
          Adder.gdigit 3 Y (m + 2) = 0 := by omega
      have heq : Adder.carryTG 3 (-2) 1 X Y (m + 1) =
          Adder.gdigit 3 (Y - 2 * X) m + 3 * Adder.carryTG 3 (-2) 1 X Y m := by
        omega
      have heq' : Adder.carryTG 3 (-2) 1 X Y (m + 2) =
          Adder.gdigit 3 (Y - 2 * X) (m + 1) +
            3 * Adder.carryTG 3 (-2) 1 X Y (m + 1) := by omega
      rcases hc_cases with hc | hc | hc <;>
        rcases hc_cases' with hc' | hc' | hc' <;>
        rcases hc_cases'' with hc'' | hc'' | hc'' <;> omega
  by_cases hex : ∃ k, N ≤ k ∧ B k = -1
  · obtain ⟨k, hkN, hk⟩ := hex
    have htail : ∀ m, k ≤ m → B m = -1 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hk
      | succ m hkm ih => exact hminus_next m (le_trans hkN hkm) ih
    exact (Adder.not_irrational_of_periodic_digits_g 3 (by norm_num)
      (Y - 2 * X) k 1 one_pos (fun m hm => by
        rw [Adder.digitOf_g_fract 3 (by norm_num), Adder.digitOf_g_fract 3 (by norm_num)]
        rw [htarget_const m (le_trans hkN hm) (-1) (Or.inl rfl)
          (htail m hm) (htail (m + 1) (by omega)) (htail (m + 2) (by omega))
          (htail (m + 3) (by omega))])) h
  · push Not at hex
    have hzero : ∀ m, N ≤ m → B m = 0 := by
      intro m hm
      have hb := hBbounds m
      have hn := hex m hm
      omega
    exact (Adder.not_irrational_of_periodic_digits_g 3 (by norm_num)
      (Y - 2 * X) N 1 one_pos (fun m hm => by
        rw [Adder.digitOf_g_fract 3 (by norm_num), Adder.digitOf_g_fract 3 (by norm_num)]
        rw [htarget_const m hm 0 (Or.inr rfl)
          (hzero m hm) (hzero (m + 1) (by omega)) (hzero (m + 2) (by omega))
          (hzero (m + 3) (by omega))])) h

/-- **The line is a real obstruction.**  Confidence 90%.  Take `X = Σ 3^{-k!}` (digits in
`{0,1}`, irrational: not eventually periodic) and `Y = 2X` (digits in `{0,2}`, no carries).
Then `Y − X = X` has digits in `{0,1}`.  None of the three digits recurs. -/
theorem exists_counterexample_on_line :
    ∃ X Y : ℝ, Irrational X ∧ Irrational Y ∧ Y = 2 * X ∧
      ¬ DigitIO 3 X 2 ∧ ¬ DigitIO 3 Y 1 ∧ ¬ DigitIO 3 (Y - X) 2 := by
  let X := Mahler.bgLiouville 3 0 1
  let Y := 2 * X
  have hcertX := Mahler.mahler_lower_bound_bg_digit 3 0 1 1 2 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro m hm; norm_num [Mahler.repunit]; omega)
    (by intro m hm d hd hd1; interval_cases m <;> interval_cases d <;>
      norm_num [Mahler.bgResidue, Mahler.repunit])
    (by intro m hm; norm_num)
  have hcertY := Mahler.mahler_lower_bound_bg_digit 3 0 2 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro m hm; norm_num [Mahler.repunit]; omega)
    (by intro m hm d hd hd1; interval_cases m <;> interval_cases d <;>
      norm_num [Mahler.bgResidue, Mahler.repunit])
    (by intro m hm; norm_num)
  have hYX : Y - X = X := by simp only [Y]; ring
  have hYbg : Y = Mahler.bgLiouville 3 0 2 := by
    simp only [Y, X, Mahler.bgLiouville]
    ring
  refine ⟨X, Y, hcertX.1, ?_, rfl, ?_, ?_, ?_⟩
  · exact hcertX.1.natCast_mul (by norm_num)
  · intro hio
    obtain ⟨N, hN⟩ := hcertX.2 1 le_rfl le_rfl
    obtain ⟨n, hn, hocc⟩ := hio N
    exact hN n hn (by simpa [X] using hocc)
  · intro hio
    obtain ⟨N, hN⟩ := hcertY.2 1 le_rfl le_rfl
    obtain ⟨n, hn, hocc⟩ := hio N
    exact hN n hn (by simpa [hYbg] using hocc)
  · intro hio
    obtain ⟨N, hN⟩ := hcertX.2 1 le_rfl le_rfl
    obtain ⟨n, hn, hocc⟩ := hio N
    exact hN n hn (by simpa [hYX, X] using hocc)

/-- **The `π + e` shape.**  Either `e − 2π` is rational, or ternary `π` has infinitely many `2`s,
or ternary `e` has infinitely many `1`s, or ternary `e − π` has infinitely many `2`s.  Every
disjunct is open.  Proved from `ternary_line`. -/
@[blueprint (title := "e - 2 pi is rational, or a ternary digit disjunction holds for pi, e")]
theorem pi_e_disjunction :
    (∃ q : ℚ, Real.exp 1 - 2 * Real.pi = q) ∨
      DigitIO 3 Real.pi 2 ∨ DigitIO 3 (Real.exp 1) 1 ∨ DigitIO 3 (Real.exp 1 - Real.pi) 2 := by
  by_cases h : Irrational (Real.exp 1 - 2 * Real.pi)
  · exact Or.inr (ternary_line _ _ h)
  · left
    unfold Irrational at h
    push Not at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq.symm⟩

/-- `S` is a **relative product block** in base `g`: for every pair with `1, X, Y` linearly
independent over `ℚ`, some combination `aX + bY`, `(a, b) ∈ S`, has every digit infinitely
often.  The two-track, independence-relative analogue of `Adder.IsProductBlock` (C2's `{2, 11}`
is a single-track block). -/
def IsRelativeBlock (g : ℕ) (S : List (ℤ × ℤ)) : Prop :=
  ∀ X Y : ℝ, (∀ c₀ c₁ c₂ : ℚ, (c₁ : ℝ) * X + c₂ * Y = c₀ → c₁ = 0 ∧ c₂ = 0) →
    ∃ p ∈ S, ∀ d < g, DigitIO g ((p.1 : ℝ) * X + p.2 * Y) d

/-- **No small relative block in base 3.**  Confidence 65%.

Evidence (`independence_relative.py blocksearch`, 2026-10-05): every direction set with at most
four directions and coefficients in `[-2, 2]` (2500 sets), at most three with coefficients in
`[-3, 3]` (5984), and every pair with coefficients in `[-6, 6]` (7140) has an assignment of
avoided digits whose live automaton keeps a component not certified degenerate.  Negating a
direction complements digits, so all-nonpositive directions add nothing.  Why it is only 65%: a
live component is a set of real avoiding pairs, but "not certified degenerate" is a failure of a
sound, incomplete phase test with witness coefficients up to 3, not a proof of positive
dimension off every line.  Reading: product-block counterexamples are two-dimensional (X and Y
vary separately), and a relative certificate only discards one-dimensional failure loci. -/
theorem not_isRelativeBlock_small (S : List (ℤ × ℤ)) (hlen : S.length ≤ 4)
    (hco : ∀ p ∈ S, |p.1| ≤ 2 ∧ |p.2| ≤ 2) : ¬ IsRelativeBlock 3 S := by
  sorry

end NormalNumbers.IndependenceRelative
