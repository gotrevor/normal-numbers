/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ErdosTriples

/-!
# Gap triples die in whole 3-adic exponent classes

`/create` session 2026-10-08, lane "uniform extinction for the imitators" of `ErdosTriples`.

**The move.**  `Survives [M₁, M₂] d` reads only `Mᵢ mod 3^(d+1)`, and `4` has order `3ᵈ` mod
`3^(d+1)`, so the depth-`d` test of `C(1, 4ᵃ, 4ᵃ⁺ᵇ)` depends only on `(a mod 3ᵈ, b mod 3ᵈ)`.  One
death certificate at depth `d` therefore proves `TripleTrivial a b` for a whole residue class, i.e.
for infinitely many integer pairs at once (`tripleTrivial_of_class`).

* `tripleTrivial_of_mod_nine`: every `(a, b)` with `a, b, a + b ∉ {0, ±1} (mod 9)` is trivial, by
  depth 2.  The "danger" residues are exactly the exponent differences of the degenerate and
  golden-mean triples (`4⁰ = 1`, `4^{±1}`).
* `aliveClasses_two`, `aliveClasses_three`: only 49 of 81 classes mod 9 and 367 of 729 mod 27
  survive; measured on: 2749/3⁸, 20761/3¹⁰, 158269/3¹², 1214503/3¹⁴ (alive fraction 25% at depth 7,
  `experiments/erdos-triples/classtree.py`).

**Why this cannot close the conjecture uniformly (the kill).**  As `α ↦ 4^α x` is a bijection onto
the units `≡ 1 (mod 3)`, the alive (class, point) pairs number exactly `8ᵈ`
(`AliveClassBound`), so the bad exponent set `B∞ = {(α, β) ∈ ℤ₃² : C(1, 4^α, 4^(α+β)) ≠ {0}}` is
the closed set `{(log₄(y/x), log₄(z/y)) : x, y, z ∈ Σ*}` of dimension `≤ log₃ 8 ≈ 1.89`.  It is
not contained in the danger lines: `x = 1, y = 10 = (101)₃, z = 28 = (1001)₃` gives a point with
`α ≡ 3, β ≡ 6 (mod 9)` and `α + β = log₄ 28 ≠ 0, ±1`.  So class certificates cover a density
tending to `1` but never everything; `GapTwoTriples` is exactly the statement that the integer
pairs with `a, b ≥ 2` avoid the fractal `B∞`.  The counting is the two-variable form of Lagarias's
Theorem 1.4 (arXiv:math/0512006, `2` a primitive root mod `3ᵏ`).
-/

namespace NormalNumbers.ErdosTriples.Classes

open NormalNumbers.ErdosTriples

theorem lowZeroOne_mod_mul_iff {d M x : ℕ} :
    LowZeroOne d (M % 3 ^ (d + 1) * x) ↔ LowZeroOne d (M * x) := by
  rw [← lowZeroOne_mod_iff, ← @lowZeroOne_mod_iff d (M * x), Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod]

/-- The depth-`d` test reads each multiplier only mod `3^(d+1)`. -/
theorem survives_map_mod (Ms : List ℕ) (d : ℕ) :
    Survives Ms d ↔ Survives (Ms.map (· % 3 ^ (d + 1))) d := by
  unfold Survives
  simp only [List.forall_mem_map, lowZeroOne_mod_mul_iff]

/-- `4^(3ᵈ) ≡ 1 (mod 3^(d+1))`. -/
theorem four_pow_three_pow (d : ℕ) : 4 ^ 3 ^ d ≡ 1 [MOD 3 ^ (d + 1)] := by
  induction d with
  | zero => decide
  | succ d ih =>
    have hle : 1 ≤ 4 ^ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp ih.symm
    have hu : 4 ^ 3 ^ d = 1 + 3 ^ (d + 1) * k := by omega
    have : 4 ^ 3 ^ (d + 1) = 1 + 3 ^ (d + 2) * (k + 3 ^ (d + 1) * k ^ 2 + 3 ^ (2 * d + 1) * k ^ 3) := by
      rw [pow_succ 3 d, pow_mul, hu]; ring
    rw [this]
    exact (Nat.add_mul_mod_self_left 1 _ _).trans (by rfl)

theorem pow_four_mod (d n : ℕ) : 4 ^ n % 3 ^ (d + 1) = 4 ^ (n % 3 ^ d) % 3 ^ (d + 1) := by
  have := ((four_pow_three_pow d).pow (n / 3 ^ d)).mul_right (4 ^ (n % 3 ^ d))
  rwa [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at this

/-- **Class certificates.**  A death at depth `d` for the residues `(a mod 3ᵈ, b mod 3ᵈ)` proves
`C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}` for every pair in the class. -/
theorem tripleTrivial_of_class (d a b : ℕ)
    (h : ¬ Survives [4 ^ (a % 3 ^ d) % 3 ^ (d + 1), 4 ^ ((a + b) % 3 ^ d) % 3 ^ (d + 1)] d) :
    TripleTrivial a b := by
  refine ⟨d, fun hs => h ?_⟩
  rw [survives_map_mod] at hs
  simp only [List.map_cons, List.map_nil] at hs
  rwa [pow_four_mod d a, pow_four_mod d (a + b)] at hs

/-- **Every pair off the danger residues mod 9 is trivial** (death by depth 2). -/
theorem tripleTrivial_of_mod_nine (a b : ℕ) (ha : a % 9 ∉ ({0, 1, 8} : Finset ℕ))
    (hb : b % 9 ∉ ({0, 1, 8} : Finset ℕ)) (hab : (a + b) % 9 ∉ ({0, 1, 8} : Finset ℕ)) :
    TripleTrivial a b := by
  have key : ∀ r : Fin 9, ∀ s : Fin 9, r.val ∉ ({0, 1, 8} : Finset ℕ) →
      s.val ∉ ({0, 1, 8} : Finset ℕ) → (r.val + s.val) % 9 ∉ ({0, 1, 8} : Finset ℕ) →
      ¬ Survives [4 ^ r.val % 27, 4 ^ ((r.val + s.val) % 9) % 27] 2 := by decide
  apply tripleTrivial_of_class 2
  have h := key ⟨a % 9, Nat.mod_lt _ (by norm_num)⟩ ⟨b % 9, Nat.mod_lt _ (by norm_num)⟩ ha hb
    (by rwa [← Nat.add_mod])
  rwa [← Nat.add_mod] at h

/-- Exactly 49 of the 81 classes mod 9 survive depth 2. -/
theorem aliveClasses_two :
    ((Finset.range 9 ×ˢ Finset.range 9).filter
      fun p => Survives [4 ^ p.1 % 27, 4 ^ ((p.1 + p.2) % 9) % 27] 2).card = 49 := by
  decide +kernel

/-- Exactly 367 of the 729 classes mod 27 survive depth 3. -/
theorem aliveClasses_three :
    ((Finset.range 27 ×ˢ Finset.range 27).filter
      fun p => Survives [4 ^ p.1 % 81, 4 ^ ((p.1 + p.2) % 27) % 81] 3).card = 367 := by
  decide +kernel

/-- **The kill, at depth 8.**  The integer pair `(1227, 6261)` (both `≥ 2`) lies in the class of
the 3-adic point `(log₄ 10, log₄ (28/10))` of `B∞` (`4¹²²⁷ ≡ 10`, `4⁷⁴⁸⁸ ≡ 28 (mod 3⁹)`, and
`1, 10 = (101)₃, 28 = (1001)₃` have `0/1` digits), so it survives depth 8 although none of
`a, b, a + b` is `0, ±1 (mod 3⁸)`.  The same construction works at every depth: no finite set of
danger lines carries `B∞`. -/
theorem survives_offLine_eight :
    Survives [4 ^ 1227, 4 ^ (1227 + 6261)] 8 ∧
      1227 % 3 ^ 8 ∉ ({0, 1, 3 ^ 8 - 1} : Finset ℕ) ∧
      6261 % 3 ^ 8 ∉ ({0, 1, 3 ^ 8 - 1} : Finset ℕ) ∧
      (1227 + 6261) % 3 ^ 8 ∉ ({0, 1, 3 ^ 8 - 1} : Finset ℕ) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [survives_map_mod]
  have h1 : 4 ^ 1227 % 3 ^ (8 + 1) = 10 := by decide +kernel
  have h2 : 4 ^ (1227 + 6261) % 3 ^ (8 + 1) = 28 := by decide +kernel
  simp only [List.map_cons, List.map_nil, h1, h2]
  exact ⟨1, by simp, rfl, by decide, by decide⟩

/-- The alive classes mod `3ᵈ` number at most `8ᵈ` (99%; the two-variable form of Lagarias's
Theorem 1.4: for a fixed unit witness `x`, `α ↦ 4^α x mod 3^(d+1)` is injective on classes
mod `3ᵈ`, so the classes inject into the `2ᵈ · 2ᵈ · 2ᵈ` triples of 0/1 unit prefixes).  Hence the
nontrivial pairs `(a, b) ∈ [0, X)²` number `O(X^(log₃ 8))`, density zero. -/
def AliveClassBound : Prop :=
  ∀ d, ((Finset.range (3 ^ d) ×ˢ Finset.range (3 ^ d)).filter fun p =>
    Survives [4 ^ p.1 % 3 ^ (d + 1), 4 ^ ((p.1 + p.2) % 3 ^ d) % 3 ^ (d + 1)] d).card ≤ 8 ^ d

end NormalNumbers.ErdosTriples.Classes
