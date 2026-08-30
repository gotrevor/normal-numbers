/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# True digits and true carries of a linear form (module 1 of the adder wing)

Brief: `BRIEF-adder-disjunction-formalization.md` §"Carry identity".

For a real `w`, `rdigit w i` is its `i`-th binary digit read off with floors
of `w` itself (digit index `i` = floor index `i+1`); it agrees with the
repo's `digitOf 2 (Int.fract w) i` (`rdigit_eq_digitOf`), so integer parts
are irrelevant throughout.

For a channel `(a, b)` and reals `X, Y`, the **true carry** at floor
position `n` is

  `carryT a b X Y n = ⌊(a·X + b·Y)·2^n⌋ - a·⌊X·2^n⌋ - b·⌊Y·2^n⌋`.

Elementary floor arithmetic gives the two facts the automaton needs:
* bounds `0 ≤ carryT ≤ a + b - 1` (`carryT_nonneg`, `carryT_le`);
* the **column identity** `a·xᵢ + b·yᵢ + T(i+1) = dᵢ(z) + 2·T(i)`
  (`carry_column`), i.e. `T` really is the carry of column addition, flowing
  from deep (large index) to shallow.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The `i`-th binary digit of `w` (digit index: `i = 0` is the first digit
after the point), computed from floors of `w` itself. -/
noncomputable def rdigit (w : ℝ) (i : ℕ) : ℤ := ⌊w * 2 ^ (i + 1)⌋ - 2 * ⌊w * 2 ^ i⌋

/-- Generic bit extraction: `⌊2u⌋ - 2⌊u⌋ ∈ {0, 1}`. -/
theorem floor_two_mul_sub (u : ℝ) : ⌊2 * u⌋ - 2 * ⌊u⌋ = 0 ∨ ⌊2 * u⌋ - 2 * ⌊u⌋ = 1 := by
  have h1 : (2 * ⌊u⌋ : ℤ) ≤ ⌊2 * u⌋ := by
    apply Int.le_floor.2
    push_cast
    nlinarith [Int.floor_le u]
  have h2 : ⌊2 * u⌋ < 2 * ⌊u⌋ + 2 := by
    apply Int.floor_lt.2
    push_cast
    nlinarith [Int.lt_floor_add_one u]
  omega

theorem rdigit_nonneg (w : ℝ) (i : ℕ) : 0 ≤ rdigit w i := by
  have := floor_two_mul_sub (w * 2 ^ i)
  unfold rdigit
  rw [show w * 2 ^ (i + 1) = 2 * (w * 2 ^ i) by ring]
  omega

theorem rdigit_le_one (w : ℝ) (i : ℕ) : rdigit w i ≤ 1 := by
  have := floor_two_mul_sub (w * 2 ^ i)
  unfold rdigit
  rw [show w * 2 ^ (i + 1) = 2 * (w * 2 ^ i) by ring]
  omega

/-- The floor of a fractional part after scaling by `2^k`:
`⌊fract w · 2^k⌋ = ⌊w·2^k⌋ - ⌊w⌋·2^k`. -/
theorem floor_fract_mul_pow (w : ℝ) (k : ℕ) :
    ⌊Int.fract w * 2 ^ k⌋ = ⌊w * 2 ^ k⌋ - ⌊w⌋ * 2 ^ k := by
  rw [Int.fract, sub_mul]
  rw [show (⌊w⌋ : ℝ) * 2 ^ k = ((⌊w⌋ * 2 ^ k : ℤ) : ℝ) by push_cast; ring]
  rw [Int.floor_sub_intCast]

/-- The repo's digit map agrees with `rdigit`: integer parts drop out. -/
theorem rdigit_eq_digitOf (w : ℝ) (i : ℕ) :
    (digitOf 2 (Int.fract w) i : ℤ) = rdigit w i := by
  have hcast : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
  have hnn : 0 ≤ ⌊Int.fract w * ((2:ℕ):ℝ) ^ (i + 1)⌋ :=
    Int.floor_nonneg.2 (by positivity)
  have hfl : ⌊Int.fract w * ((2:ℕ):ℝ) ^ (i + 1)⌋
      = ⌊w * 2 ^ (i + 1)⌋ - ⌊w⌋ * 2 ^ (i + 1) := by
    rw [hcast]; exact floor_fract_mul_pow w (i + 1)
  have hd0 := rdigit_nonneg w i
  have hd1 := rdigit_le_one w i
  have h2 : (2 : ℤ) ∣ ⌊w⌋ * 2 ^ (i + 1) := ⟨⌊w⌋ * 2 ^ i, by ring⟩
  unfold digitOf
  rw [hcast] at hnn hfl
  push_cast
  rw [Int.toNat_of_nonneg hnn, hfl]
  unfold rdigit at *
  omega

/-- The **true carry** of the column addition for `z = a·X + b·Y` at floor
position `n`. -/
noncomputable def carryT (a b : ℕ) (X Y : ℝ) (n : ℕ) : ℤ :=
  ⌊(a * X + b * Y) * 2 ^ n⌋ - a * ⌊X * 2 ^ n⌋ - b * ⌊Y * 2 ^ n⌋

theorem carryT_nonneg (a b : ℕ) (X Y : ℝ) (n : ℕ) : 0 ≤ carryT a b X Y n := by
  unfold carryT
  have hle : ((a * ⌊X * 2 ^ n⌋ + b * ⌊Y * 2 ^ n⌋ : ℤ) : ℝ) ≤ (a * X + b * Y) * 2 ^ n := by
    push_cast
    have hX := Int.floor_le (X * 2 ^ n)
    have hY := Int.floor_le (Y * 2 ^ n)
    have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
    have hb : (0:ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith
  have := Int.le_floor.2 hle
  omega

theorem carryT_le (a b : ℕ) (X Y : ℝ) (n : ℕ) (hab : 1 ≤ a + b) :
    carryT a b X Y n ≤ a + b - 1 := by
  unfold carryT
  have hlt : (a * X + b * Y) * 2 ^ n
      < ((a * ⌊X * 2 ^ n⌋ + b * ⌊Y * 2 ^ n⌋ + a + b : ℤ) : ℝ) := by
    push_cast
    have hX := Int.lt_floor_add_one (X * 2 ^ n)
    have hY := Int.lt_floor_add_one (Y * 2 ^ n)
    -- one of the coefficients is positive; its side is strict, the other weak
    rcases Nat.lt_or_ge 0 a with ha1 | ha0
    · have haR : (0:ℝ) < a := by exact_mod_cast ha1
      have h1 : (a:ℝ) * (X * 2 ^ n) < a * (⌊X * 2 ^ n⌋ + 1) :=
        mul_lt_mul_of_pos_left hX haR
      have h2 : (b:ℝ) * (Y * 2 ^ n) ≤ b * (⌊Y * 2 ^ n⌋ + 1) :=
        mul_le_mul_of_nonneg_left hY.le (Nat.cast_nonneg b)
      nlinarith
    · have hb1 : 1 ≤ b := by omega
      have hbR : (0:ℝ) < b := by exact_mod_cast hb1
      have h1 : (b:ℝ) * (Y * 2 ^ n) < b * (⌊Y * 2 ^ n⌋ + 1) :=
        mul_lt_mul_of_pos_left hY hbR
      have h2 : (a:ℝ) * (X * 2 ^ n) ≤ a * (⌊X * 2 ^ n⌋ + 1) :=
        mul_le_mul_of_nonneg_left hX.le (Nat.cast_nonneg a)
      nlinarith
  have := Int.floor_lt.2 hlt
  omega

/-- **The column identity**: at digit index `i` (floor column `i+1`),
`a·xᵢ + b·yᵢ + T(i+1) = dᵢ(z) + 2·T(i)` — the carry `T(i+1)` flows in from
the deeper column, the digit `dᵢ(z)` is emitted, and `T(i)` flows out
shallower. -/
theorem carry_column (a b : ℕ) (X Y : ℝ) (i : ℕ) :
    a * rdigit X i + b * rdigit Y i + carryT a b X Y (i + 1)
      = rdigit (a * X + b * Y) i + 2 * carryT a b X Y i := by
  unfold rdigit carryT
  ring

end NormalNumbers.Adder
