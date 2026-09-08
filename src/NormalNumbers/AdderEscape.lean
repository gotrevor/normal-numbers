/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerMultiplier
import NormalNumbers.AdderBaseG
import NormalNumbers.Bridge

/-!
# The adder machine, escape direction: true carries 🧮

The signed engine (`AdderBaseG.lean`) proves COLLAPSE: a passing certificate
shows every irrational's channel run dies, so some channel word occurs.  The
exact Mahler values of `experiments/mahler_exact_M.py` are the other
direction — ESCAPE: a strongly connected set of live states from which the
word can be avoided forever.  Turning that into a kernel fact needs a real
number whose channel digits follow a chosen path, and the obstacle is the
carry: for channel `m` the digit at depth `i` of `m·x` is determined by the
digit of `x` there and the **true carry** `⌊m·{gⁱ⁺¹x}⌋` from the tail, which
depends on the whole future of the digit string.

This file lays the arithmetic bricks:

* `carry g x m i = ⌊m · orbit g x i⌋` — the true carry, in `[0, m)`;
* `carry_recursion` — `carry i = (m·aᵢ + carry (i+1)) / g` with `aᵢ` the
  `i`-th digit of `x`: the carries satisfy the adder recursion exactly;
* `digitOf_mul` — the `i`-th digit of `m·x` is `(m·aᵢ + carry (i+1)) % g`.

So a channel run of the automaton that agrees with the true carries reads
off the digits of `m·x` exactly; the remaining work (next bricks) is to pin
the true carries from tail intervals of the certificate's language.
-/

namespace NormalNumbers.Adder

open NormalNumbers NormalNumbers.Mahler

/-- The **true carry** of channel `m` at depth `i`: `⌊m · {gⁱ x}⌋`. -/
noncomputable def carry (g : ℕ) (x : ℝ) (m i : ℕ) : ℕ :=
  (⌊(m : ℝ) * orbit g x i⌋).toNat

theorem carry_lt (g : ℕ) (x : ℝ) (m i : ℕ) (hm : 1 ≤ m) : carry g x m i < m := by
  unfold carry
  have h := orbit_mem_Ico g x i
  have hlt : ⌊(m : ℝ) * orbit g x i⌋ < m := by
    apply Int.floor_lt.2
    push_cast
    have : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith [h.2]
  omega

theorem carry_cast (g : ℕ) (x : ℝ) (m i : ℕ) :
    (carry g x m i : ℤ) = ⌊(m : ℝ) * orbit g x i⌋ := by
  unfold carry
  apply Int.toNat_of_nonneg
  apply Int.floor_nonneg.2
  exact mul_nonneg (by positivity) (orbit_mem_Ico g x i).1

/-- The `i`-th digit of `x` is `⌊g · orbit g x i⌋`. -/
theorem digitOf_eq_floor_orbit (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (i : ℕ) :
    (digitOf g (Int.fract x) i : ℤ) = ⌊(g : ℝ) * orbit g x i⌋ := by
  have h1 : digitOf g (Int.fract x) i = digitOf g (orbit g (Int.fract x) i) 0 := by
    rw [digitOf_orbit g hg (Int.fract x) (Int.fract_nonneg x) i 0, Nat.add_zero]
  rw [h1, orbit_fract]
  unfold digitOf
  simp only [zero_add, pow_one]
  have hmem := orbit_mem_Ico g x i
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hnn : 0 ≤ ⌊orbit g x i * (g : ℝ)⌋ :=
    Int.floor_nonneg.2 (mul_nonneg hmem.1 hg0.le)
  have hlt : ⌊orbit g x i * (g : ℝ)⌋ < g := by
    apply Int.floor_lt.2
    push_cast
    nlinarith [hmem.2]
  have hmod : (⌊orbit g x i * (g : ℝ)⌋).toNat % g = (⌊orbit g x i * (g : ℝ)⌋).toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod, Int.toNat_of_nonneg hnn, mul_comm]

/-- `g · orbit g x i = aᵢ + orbit g x (i+1)`. -/
theorem orbit_split (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (i : ℕ) :
    (g : ℝ) * orbit g x i = (digitOf g (Int.fract x) i : ℝ) + orbit g x (i + 1) := by
  rw [orbit_succ]
  have h := digitOf_eq_floor_orbit g hg x i
  have h' : ((digitOf g (Int.fract x) i : ℤ) : ℝ) = (⌊(g : ℝ) * orbit g x i⌋ : ℝ) := by
    exact_mod_cast h
  rw [Int.cast_natCast] at h'
  rw [h', Int.fract]; ring

/-- Integer division absorbs a fractional part: `⌊(K + f)/g⌋ = K / g`. -/
theorem floor_add_fract_div (K : ℤ) (f : ℝ) (g : ℕ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    ⌊((K : ℝ) + f) / (g : ℝ)⌋ = K / (g : ℤ) := by
  have h0 : ⌊f⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hf0, hf1⟩
  rw [Int.floor_div_natCast, Int.floor_intCast_add, h0, add_zero]

/-- **The carry recursion.**  `carry i = (m·aᵢ + carry (i+1)) / g`. -/
theorem carry_recursion (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (m i : ℕ) :
    carry g x m i = (m * digitOf g (Int.fract x) i + carry g x m (i + 1)) / g := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hsplit := orbit_split g hg x i
  -- `m · orbit i = (m aᵢ + m · orbit (i+1)) / g`
  have hc : (carry g x m (i + 1) : ℝ) = ((⌊(m : ℝ) * orbit g x (i + 1)⌋ : ℤ) : ℝ) := by
    exact_mod_cast carry_cast g x m (i + 1)
  have h1' : (m : ℝ) * orbit g x i * (g : ℝ)
      = (((m * digitOf g (Int.fract x) i + carry g x m (i + 1) : ℕ) : ℤ) : ℝ)
        + Int.fract ((m : ℝ) * orbit g x (i + 1)) := by
    have hf : Int.fract ((m : ℝ) * orbit g x (i + 1))
        = (m : ℝ) * orbit g x (i + 1) - (⌊(m : ℝ) * orbit g x (i + 1)⌋ : ℝ) :=
      (Int.self_sub_floor _).symm
    push_cast
    rw [hc, hf]
    linear_combination (m : ℝ) * hsplit
  have h1 : (m : ℝ) * orbit g x i
      = ((((m * digitOf g (Int.fract x) i + carry g x m (i + 1) : ℕ) : ℤ) : ℝ)
        + Int.fract ((m : ℝ) * orbit g x (i + 1))) / (g : ℝ) := by
    rw [eq_div_iff hg0.ne']; exact h1'
  have h2 : ⌊(m : ℝ) * orbit g x i⌋
      = ((m * digitOf g (Int.fract x) i + carry g x m (i + 1) : ℕ) : ℤ) / (g : ℤ) := by
    rw [h1]
    exact floor_add_fract_div _ _ g (Int.fract_nonneg _) (Int.fract_lt_one _)
  have h3 := carry_cast g x m i
  rw [h2, ← Int.natCast_div] at h3
  exact_mod_cast h3

/-- **The digit of a multiple.**  The `i`-th digit of `m·x` is
`(m·aᵢ + carry (i+1)) % g`. -/
theorem digitOf_mul (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (m i : ℕ) :
    digitOf g (Int.fract ((m : ℝ) * x)) i
      = (m * digitOf g (Int.fract x) i + carry g x m (i + 1)) % g := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  -- both sides as integers: the digit of `m x` via `gdigit`
  have hL : (digitOf g (Int.fract ((m : ℝ) * x)) i : ℤ) = gdigit g ((m : ℝ) * x) i :=
    gdigit_eq_digitOf g hg _ i
  have hx : (digitOf g (Int.fract x) i : ℤ) = gdigit g x i := gdigit_eq_digitOf g hg _ i
  -- `⌊m x g^(i+1)⌋ = m ⌊x g^(i+1)⌋ + carry (i+1)`
  have hfl : ⌊(m : ℝ) * x * (g : ℝ) ^ (i + 1)⌋
      = m * ⌊x * (g : ℝ) ^ (i + 1)⌋ + carry g x m (i + 1) := by
    have hc := carry_cast g x m (i + 1)
    have e : (m : ℝ) * x * (g : ℝ) ^ (i + 1)
        = ((m * ⌊x * (g : ℝ) ^ (i + 1)⌋ : ℤ) : ℝ) + (m : ℝ) * orbit g x (i + 1) := by
      unfold orbit; push_cast; rw [Int.fract]; ring
    rw [e, Int.floor_intCast_add, ← hc]
  -- reduce mod `g`
  have hmod : (digitOf g (Int.fract ((m : ℝ) * x)) i : ℤ)
      ≡ (m : ℤ) * digitOf g (Int.fract x) i + carry g x m (i + 1) [ZMOD g] := by
    rw [hL, hx]
    unfold gdigit
    rw [hfl]
    refine (Int.modEq_iff_dvd.2 ?_)
    refine ⟨⌊(m : ℝ) * x * (g : ℝ) ^ i⌋ - (m : ℤ) * ⌊x * (g : ℝ) ^ i⌋, ?_⟩
    ring
  have hlt : (digitOf g (Int.fract ((m : ℝ) * x)) i : ℤ) < g := by
    exact_mod_cast Nat.mod_lt _ (by omega : 0 < g)
  have h0 : (0 : ℤ) ≤ digitOf g (Int.fract ((m : ℝ) * x)) i := by positivity
  have := hmod.symm
  unfold Int.ModEq at this
  rw [Int.emod_eq_of_lt h0 hlt] at this
  exact_mod_cast this.symm

end NormalNumbers.Adder
