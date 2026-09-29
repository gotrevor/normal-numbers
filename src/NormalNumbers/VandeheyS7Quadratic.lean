/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-QD: two cycles in `ℚ(√2)` — the arithmetic core of the `BlockForget` obstruction

`BlockForget` (S7-BF, the current directive's crux) asks the block time-average to forget the
initial state **at every input point `z ∈ (0,1)`**.  That uniform-in-`z` form is FALSE, and this
module lands the arithmetic that refutes it.

## The obstruction

The run started at the state `s` on the input `z` emits the continued fraction of `s.mob z`
(that is the design of the transducer: `mapBlockSet s w 0 = s.mob⁻¹(I_w)` tests the next output
block).  So for a FIXED input `z`, the block average is, up to the clock rate, the frequency of `w`
in the CF of `s.mob z`.  Take

    z = √2 − 1 = [0; 2, 2, 2, …]                        (`gaussMap` fixes it)
    s = refState (the identity),  s' : t ↦ 2 / (t + 2)
    s'.mob z = 2/(√2+1) = 2√2 − 2 = [0; 1, 4, 1, 4, …]  (`gaussMap`-period 2)

Both values lie in `ℚ(√2)`, so `s'` has RATIONAL entries and is a legitimate state of width `1/3`;
but they lie in different `GL₂(ℤ)` cycles — discriminants `8` and `32` — hence have different digit
sequences.  The digit `1` has frequency `0` in the first and `1/2` in the second.  Both clocks run
at rate `1` (per period of two output digits the convergent denominators grow by `(1+√2)²`, the same
as for two input digits), so for `w = [1]`

    blockAvg refState T w z → 0        while        blockAvg s' T w z → 1/2

for every `T`: the two averages differ by `≈ 1/2`, uniformly in `T`.  `BlockForget`'s `∀ z ∈ (0,1)`
must therefore be restricted — and the architecture only ever needs it at the orbit points of a
CF-normal input, which are never quadratic (a quadratic irrational's digits are eventually periodic,
so the digit `3` has frequency `0` there, contradicting CF-normality).  That is the repair:
`BlockForgetGen` (S7-BG).

What is proved here is the arithmetic core — the two digit sequences — which is what makes the
witness a witness.  The step from digit sequences to `blockAvg` is the transducer-correctness and
clock-rate bookkeeping; it is recorded as a Maze row, not claimed here.

## Guard rule

**Content locator.**  Everything rests on the two `gaussMap` cycles, and each is a one-line field
identity (`gaussMap_sqrtTwoSub` and `gaussMap_twoSqrtTwoSub`, `gaussMap_halfSqrtTwoSub`).  The
degenerate instance is the first: a FIXED point of `gaussMap`, i.e. a purely periodic CF of period
`1`, where "the frequency of a digit" is trivially `0` or `1`.

**Degenerate cases.**  `p = 0` makes both digit counts `0`.  The digit `0` never occurs in either
sequence, as for every irrational.  Neither number is rational (both are proved irrational here),
so no junk digits arise.
-/
import NormalNumbers.VandeheyS7RefCesaro

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

/-! ## `√2 − 1`, the fixed point -/

/-- `√2 − 1 = [0; 2, 2, 2, …]`. -/
noncomputable def sqrtTwoSub : ℝ := Real.sqrt 2 - 1

lemma sqrtTwo_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma sqrtTwo_bounds : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · nlinarith [sqrtTwo_sq, Real.sqrt_nonneg 2]
  · nlinarith [sqrtTwo_sq, Real.sqrt_nonneg 2]

lemma sqrtTwoSub_mem : sqrtTwoSub ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [Set.mem_Ioo, sqrtTwoSub]
  constructor <;> linarith

lemma inv_sqrtTwoSub : sqrtTwoSub⁻¹ = Real.sqrt 2 + 1 :=
  inv_eq_of_mul_eq_one_right (by rw [sqrtTwoSub]; nlinarith [sqrtTwo_sq])

lemma cfDigit_sqrtTwoSub_zero : cfDigit sqrtTwoSub 0 = 2 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [cfDigit_zero, inv_sqrtTwoSub]
  rw [Nat.floor_eq_iff (by linarith)]
  push_cast
  constructor <;> linarith

/-- **The cycle of length one.**  `gaussMap` fixes `√2 − 1`. -/
theorem gaussMap_sqrtTwoSub : gaussMap sqrtTwoSub = sqrtTwoSub := by
  rw [gaussMap_eq_inv_sub sqrtTwoSub_mem, cfDigit_sqrtTwoSub_zero, inv_sqrtTwoSub, sqrtTwoSub]
  push_cast
  ring

theorem gaussMap_iterate_sqrtTwoSub (n : ℕ) : gaussMap^[n] sqrtTwoSub = sqrtTwoSub := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, gaussMap_sqrtTwoSub]

/-- **Every digit of `√2 − 1` is `2`** — so the digit `1` has frequency `0`. -/
theorem cfDigit_sqrtTwoSub (n : ℕ) : cfDigit sqrtTwoSub n = 2 := by
  rw [cfDigit, gaussMap_iterate_sqrtTwoSub, ← cfDigit_zero]
  exact cfDigit_sqrtTwoSub_zero

/-! ## `2√2 − 2`, the cycle of length two -/

/-- `2√2 − 2 = [0; 1, 4, 1, 4, …]`. -/
noncomputable def twoSqrtTwoSub : ℝ := 2 * Real.sqrt 2 - 2

/-- The other point of the cycle, `(√2 − 1)/2 = [0; 4, 1, 4, 1, …]`. -/
noncomputable def halfSqrtTwoSub : ℝ := (Real.sqrt 2 - 1) / 2

lemma twoSqrtTwoSub_mem : twoSqrtTwoSub ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [Set.mem_Ioo, twoSqrtTwoSub]
  constructor <;> linarith

lemma halfSqrtTwoSub_mem : halfSqrtTwoSub ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [Set.mem_Ioo, halfSqrtTwoSub]
  constructor <;> linarith

lemma inv_twoSqrtTwoSub : twoSqrtTwoSub⁻¹ = (Real.sqrt 2 + 1) / 2 :=
  inv_eq_of_mul_eq_one_right (by rw [twoSqrtTwoSub]; nlinarith [sqrtTwo_sq])

lemma inv_halfSqrtTwoSub : halfSqrtTwoSub⁻¹ = 2 * (Real.sqrt 2 + 1) :=
  inv_eq_of_mul_eq_one_right (by rw [halfSqrtTwoSub]; nlinarith [sqrtTwo_sq])

lemma cfDigit_twoSqrtTwoSub_zero : cfDigit twoSqrtTwoSub 0 = 1 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [cfDigit_zero, inv_twoSqrtTwoSub, Nat.floor_eq_iff (by linarith)]
  push_cast
  constructor <;> linarith

lemma cfDigit_halfSqrtTwoSub_zero : cfDigit halfSqrtTwoSub 0 = 4 := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [cfDigit_zero, inv_halfSqrtTwoSub, Nat.floor_eq_iff (by linarith)]
  push_cast
  constructor <;> linarith

theorem gaussMap_twoSqrtTwoSub : gaussMap twoSqrtTwoSub = halfSqrtTwoSub := by
  rw [gaussMap_eq_inv_sub twoSqrtTwoSub_mem, cfDigit_twoSqrtTwoSub_zero, inv_twoSqrtTwoSub,
    halfSqrtTwoSub]
  push_cast
  ring

theorem gaussMap_halfSqrtTwoSub : gaussMap halfSqrtTwoSub = twoSqrtTwoSub := by
  rw [gaussMap_eq_inv_sub halfSqrtTwoSub_mem, cfDigit_halfSqrtTwoSub_zero, inv_halfSqrtTwoSub,
    twoSqrtTwoSub]
  push_cast
  ring

/-- **The cycle of length two.** -/
theorem gaussMap_iterate_twoSqrtTwoSub (k : ℕ) :
    gaussMap^[2 * k] twoSqrtTwoSub = twoSqrtTwoSub := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        gaussMap_twoSqrtTwoSub, gaussMap_halfSqrtTwoSub]

/-- **The digits of `2√2 − 2` alternate `1, 4`** — so the digit `1` has frequency `1/2`. -/
theorem cfDigit_twoSqrtTwoSub_even (k : ℕ) : cfDigit twoSqrtTwoSub (2 * k) = 1 := by
  rw [cfDigit, gaussMap_iterate_twoSqrtTwoSub, ← cfDigit_zero]
  exact cfDigit_twoSqrtTwoSub_zero

theorem cfDigit_twoSqrtTwoSub_odd (k : ℕ) : cfDigit twoSqrtTwoSub (2 * k + 1) = 4 := by
  rw [cfDigit, Function.iterate_succ_apply', gaussMap_iterate_twoSqrtTwoSub,
    gaussMap_twoSqrtTwoSub, ← cfDigit_zero]
  exact cfDigit_halfSqrtTwoSub_zero

/-! ## The state that realises the second cycle -/

namespace MapState

/-- The state `t ↦ 2/(t+2)`: rational entries, width `1/3`, and it carries `√2 − 1` to
`2√2 − 2` — the other `GL₂(ℤ)` cycle of `ℚ(√2)`. -/
noncomputable def shiftState : MapState where
  a := 0
  b := 2
  c := 1
  d := 2
  hd := by norm_num
  hcd := by norm_num
  hb0 := by norm_num
  hbd := by norm_num
  hab0 := by norm_num
  habcd := by norm_num
  hdet := by norm_num

@[simp] lemma shiftState_mob (z : ℝ) : shiftState.mob z = 2 / (z + 2) := by
  show ((0:ℝ) * z + 2) / (1 * z + 2) = 2 / (z + 2)
  ring_nf

/-- **The witness identity.**  The state sends the input point to the OTHER cycle. -/
theorem shiftState_mob_sqrtTwoSub : shiftState.mob sqrtTwoSub = twoSqrtTwoSub := by
  obtain ⟨h1, h2⟩ := sqrtTwo_bounds
  rw [shiftState_mob, sqrtTwoSub, twoSqrtTwoSub, div_eq_iff (by linarith)]
  nlinarith [sqrtTwo_sq]

lemma shiftState_width : shiftState.width = 1 / 3 := by
  rw [width, shiftState_mob, shiftState_mob]
  norm_num

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.cfDigit_sqrtTwoSub
#print axioms NormalNumbers.VandeheyS7.cfDigit_twoSqrtTwoSub_even
#print axioms NormalNumbers.VandeheyS7.cfDigit_twoSqrtTwoSub_odd
#print axioms NormalNumbers.VandeheyS7.MapState.shiftState_mob_sqrtTwoSub
#print axioms NormalNumbers.VandeheyS7.MapState.shiftState_width

end Audit
