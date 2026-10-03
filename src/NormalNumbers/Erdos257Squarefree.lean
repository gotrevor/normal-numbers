/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Disjunctive

/-!
# Erdős #257 for squarefree and `k`-free `A`: an audit, not a new result

Audit of `docs/OPEN-PROBLEMS-SWEEP-2026-10-03.md` §4 (2026-10-03).  Two verdicts, both recorded
as `Maze` rows.

**1. Irrationality is prior art.**  For `A` = the squarefree integers,
`Σ_{n∈A} 1/(2ⁿ−1) = Σ_m 2^{ω(m)} 2^{-m}`, and the Chowla–Erdős "kill" (CRT puts `j+1`
primes exactly dividing `n+j` for `j < k`, so `2^{j+1} ∣ 2^{ω(n+j)}`; the tail is below the
divisor-function tail since `2^ω ≤ τ`) proves it irrational with no prime-distribution input.
That is exactly Duverney–Tachiya, *Refinement of the Chowla–Erdős method and linear independence
of certain Lambert series*, Forum Math. 31 (2019), no. 6, 1557–1566, doi:10.1515/forum-2018-0299,
Corollary 1.2 and Example 1.1 (p. 4 of the author preprint): for `F_s(P)` = the integers whose
prime exponents are all `< s` (squarefree at `s = 2`, cubefree at `s = 3`), and `|q| ≤ s`, the
numbers `1, Σ_{n∈F_s} 1/(q^{jn} − 1)` (`j = 1, …, h`) are linearly independent over `ℚ`.
W. Cook's #257 paper (Plectis, `erdos257-mersenne-reasoning-surface.md`, Remark 6 and the note
after Prop. 274) cites the same result.  `DuverneyTachiya2019KFree` states it, weakened to
irrationality.  Semiprime `A` is *not* covered by that theorem, and the kill does not transfer:
the incidence `C(ω(m), 2)` is not divisible by a fixed power of two when the cofactor's `ω` is
uncontrolled.

**2. The disjunctive form needs one exact-`ω` survivor per `1`-bit.**  The joint-Lambert /
Campbell construction for `E = Σ τ(m) 2^{-m}` reads the target word off one survivor `n + r`
whose coefficient `τ(n+r) = 2a` is arbitrary even (`EvenEncoding`).  With coefficient `2^{ω}` the
survivor value `2^{ω(n+r)} / 2^{r+1}` has fractional part `0` or `2^{-t}`
(`fract_two_pow_div_two_pow`): one survivor writes one bit, so the single-survivor encoding hits no
interval inside `(1/2, 1)` (`not_powTwoEncoding`).  A word with `ℓ` ones needs `ℓ` positions
with *exactly* prescribed `ω` along one CRT progression, which is a prime-tuple / joint
local-Erdős–Kac input (simultaneous exact values of `ω` at two shifts), not something the repo's
engines or the cited literature supply.  `SqfreeBinaryDisjunctive` records the open target.
-/

namespace NormalNumbers.Erdos257Squarefree

/-- `n` is `k`-free: no prime `k`-th power divides it.  At `k = 2` this is `Squarefree`
(`kFree_two_iff`), and `{n > 0 : KFree s n}` is Duverney–Tachiya's `F_s(P)`. -/
def KFree (k n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n

theorem kFree_two_iff (n : ℕ) : KFree 2 n ↔ Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  simp only [KFree, pow_two]

/-- **Duverney–Tachiya 2019, Corollary 1.2** (Forum Math. 31, 1557–1566), at `ℓ = 1`,
`E = P` the primes, `s = k`, and a positive base `q` with `q ≤ s` (their hypothesis
`|q|^{lcm(1,…,ℓ)} ≤ s`), weakened from linear independence of `1` and the `h` series to
irrationality of each series.  Cited, not proved here. -/
def DuverneyTachiya2019KFree : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ q : ℕ, 2 ≤ q → q ≤ k → ∀ j : ℕ, 1 ≤ j →
    Irrational (∑' n : {n : ℕ // 0 < n ∧ KFree k n},
      (1 : ℝ) / ((q : ℝ) ^ (j * (n : ℕ)) - 1))

/-- The squarefree subsums at every base `2^j` (Duverney–Tachiya's Example 1.1, weakened). -/
theorem erdos257_squarefree_pow_of_literature (hDT : DuverneyTachiya2019KFree)
    (j : ℕ) (hj : 1 ≤ j) :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ Squarefree n},
      (1 : ℝ) / ((2 : ℝ) ^ (j * (n : ℕ)) - 1)) := by
  have h := hDT 2 le_rfl 2 le_rfl le_rfl j hj
  let e : {n : ℕ // 0 < n ∧ KFree 2 n} ≃ {n : ℕ // 0 < n ∧ Squarefree n} :=
    Equiv.subtypeEquivRight fun n => and_congr_right' (kFree_two_iff n)
  have hsum : (∑' n : {n : ℕ // 0 < n ∧ KFree 2 n},
      (1 : ℝ) / (((2 : ℕ) : ℝ) ^ (j * (n : ℕ)) - 1)) =
      ∑' n : {n : ℕ // 0 < n ∧ Squarefree n}, (1 : ℝ) / ((2 : ℝ) ^ (j * (n : ℕ)) - 1) := by
    rw [← e.tsum_eq]
    rfl
  rwa [hsum] at h

/-- **Erdős #257 for the squarefree integers**, from the cited Duverney–Tachiya theorem. -/
theorem erdos257_squarefree_of_literature (hDT : DuverneyTachiya2019KFree) :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ Squarefree n}, (1 : ℝ) / (2 ^ (n : ℕ) - 1)) := by
  simpa using erdos257_squarefree_pow_of_literature hDT 1 le_rfl

/-- **Erdős #257 for the `k`-free integers** (`k ≥ 2`), base 2, from the same citation. -/
theorem erdos257_kFree_of_literature (hDT : DuverneyTachiya2019KFree) (k : ℕ) (hk : 2 ≤ k) :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ KFree k n}, (1 : ℝ) / (2 ^ (n : ℕ) - 1)) := by
  simpa using hDT k hk 2 le_rfl hk 1 le_rfl

/-- **Open target** (the sweep's §4.4 draft, kept as a statement): the binary expansion of the
squarefree #257 sum is disjunctive.  Not known; see the module doc for the missing input. -/
def SqfreeBinaryDisjunctive : Prop :=
  IsDisjunctive 2 (∑' n : {n : ℕ // 0 < n ∧ Squarefree n}, (1 : ℝ) / (2 ^ (n : ℕ) - 1))

/-- **One survivor reads one bit.**  A power of two over a power of two has fractional part `0`
or `2^{-t}` with `t ≥ 1`. -/
theorem fract_two_pow_div_two_pow (e s : ℕ) :
    Int.fract ((2 : ℝ) ^ e / 2 ^ s) = 0 ∨
      ∃ t : ℕ, 1 ≤ t ∧ Int.fract ((2 : ℝ) ^ e / 2 ^ s) = 1 / 2 ^ t := by
  rcases le_or_gt s e with hse | hes
  · left
    have h : (2 : ℝ) ^ e / 2 ^ s = ((2 ^ (e - s) : ℕ) : ℝ) := by
      rw [div_eq_iff (by positivity), Nat.cast_pow, Nat.cast_ofNat, ← pow_add,
        Nat.sub_add_cancel hse]
    rw [h, Int.fract_natCast]
  · right
    refine ⟨s - e, by omega, ?_⟩
    have h : (2 : ℝ) ^ e / 2 ^ s = 1 / 2 ^ (s - e) := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add,
        Nat.add_sub_cancel' hes.le]
    rw [h, Int.fract_eq_self]
    have h1 : (2 : ℝ) ≤ 2 ^ (s - e) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (s - e) := pow_le_pow_right₀ (by norm_num) (by omega)
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]
    linarith

/-- The `EvenEncoding` interface of `JointLambertStatement.lean` at the single base `2`, with
the survivor count `2a` restricted to the values `2^e` that `2^{ω}` can take. -/
def PowTwoEncoding : Prop :=
  ∀ lo hi : ℝ, 0 ≤ lo → lo < hi → hi ≤ 1 →
    ∃ s e : ℕ, 2 ≤ s ∧ lo < Int.fract ((2 : ℝ) ^ e / 2 ^ s) ∧
      Int.fract ((2 : ℝ) ^ e / 2 ^ s) < hi

/-- **The single-survivor encoding fails for squarefree `A` at base 2**: no survivor lands in
`(5/8, 3/4)`, the cylinder of the binary word `101`. -/
theorem not_powTwoEncoding : ¬ PowTwoEncoding := by
  intro h
  obtain ⟨s, e, -, hlo, -⟩ := h (5 / 8) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  rcases fract_two_pow_div_two_pow e s with h0 | ⟨t, ht, hf⟩
  · rw [h0] at hlo; norm_num at hlo
  · rw [hf] at hlo
    have h2 : (2 : ℝ) ≤ 2 ^ t := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) ht
    have : (1 : ℝ) / 2 ^ t ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith

end NormalNumbers.Erdos257Squarefree
