/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Stoneham

/-!
# The Stoneham Rosetta stone: base-6 `α₂,₃` reads out `3^a mod 2^c` (N2) 🪨

Companion to `docs/new-conjectures-2026-08-29.md` §N2 and the probe
`experiments/stoneham6_readout.py` (identity verified to machine precision: the per-block
maximum error equals the next-term prediction exactly).  `Stoneham.lean` proved
`isNormal_two_stoneham23` by reading the base-2 orbit of `α = Σ_{m ≥ 1} 1/(3ᵐ·2^(3ᵐ))`
through the integer state `c_M(n) mod 3^M`.  This module does the same for base **6**,
where Bailey–Borwein 2012 proved `α` is NOT normal, and finds the mechanism is a *readout of
powers of `3`*:

For `n ≥ 3` let `j* = jstar n = min {j : n < 3^(j+1)}` (the block of `n`), `a = n − (j*+1)`
and `c = 3^(j*+1) − n`.  Scaling the series by `6ⁿ`, every term before block `j*` is an
integer, the block term is exactly `3^a/2^c`, and the rest is a tail below the next term
twice over.  Hence (`stoneham_base6_readout`)

  `(3^a mod 2^c)/2^c < fract (6ⁿ·α) ≤ (3^a mod 2^c)/2^c + 2·3^(a−1)/2^(3^(j*+2) − n)`,

an error that is `2^{−Θ(3^{j*+1})}`-small across the whole block.  So within block `j*` the
base-6 digits of `α` replay the base-6 expansion of the single dyadic rational
`3^a/2^c ≡ 6ⁿ/(3^(j*+1)·2^(3^(j*+1))) (mod 1)`, i.e. the binary digits of `3^a mod 2^c`:
the base-6 expansion of `α₂,₃` is a **transcript of the powers of `3` in `ℤ₂`** — the very
object (`3^a mod 2^c`) that is collatz-moonshot's native coordinate.  Bailey–Borwein's
zero-runs are the coarse shadow: the segments where `3^a < 2^c/6`.

Everything here is proved; trust triple.  `jstar`/`readout` are computable (`Nat.find`), and
the anchor `readout 10 = 2187` (`3^7 mod 2^17`) is checked by `decide`.

**Node still to freeze** (`PowersOfThreeReadoutDense`, N2): "every base-6 word occurs in the
readout window of infinitely many blocks" ⟺ `α₂,₃` is 6-disjunctive.  Freezing it needs the
window margin pinned (digit agreement between `fract (6ⁿ α)` and `(3^a mod 2^c)/2^c` holds
until the error can carry, i.e. for word lengths below `≈ 3^{j*+1}·log₆ 2` positions from the
block end) and the quantifier-degeneracy probe run first; deliberately not done here.
-/
namespace NormalNumbers

/-! ### The block index -/

theorem exists_lt_three_pow (n : ℕ) : ∃ j : ℕ, n < 3 ^ (j + 1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
    (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- `jstar n = min {j : n < 3^(j+1)}`: the index of the first Stoneham term
`1/(3^(j+1)·2^(3^(j+1)))` whose dyadic denominator exceeds `2ⁿ` — the block of `n`. -/
def jstar (n : ℕ) : ℕ := Nat.find (exists_lt_three_pow n)

theorem lt_three_pow_jstar (n : ℕ) : n < 3 ^ (jstar n + 1) :=
  Nat.find_spec (exists_lt_three_pow n)

theorem three_pow_le_of_lt_jstar {n j : ℕ} (hj : j < jstar n) : 3 ^ (j + 1) ≤ n := by
  have := Nat.find_min (exists_lt_three_pow n) hj
  push Not at this
  exact this

theorem one_le_jstar {n : ℕ} (hn : 3 ≤ n) : 1 ≤ jstar n := by
  by_contra h
  push Not at h
  have h0 : jstar n = 0 := by omega
  have := lt_three_pow_jstar n
  rw [h0] at this
  omega

theorem three_pow_jstar_le {n : ℕ} (hn : 3 ≤ n) : 3 ^ (jstar n) ≤ n := by
  have h1 := one_le_jstar hn
  have := three_pow_le_of_lt_jstar (n := n) (j := jstar n - 1) (by omega)
  rwa [show jstar n - 1 + 1 = jstar n by omega] at this

theorem jstar_add_two_le {n : ℕ} (hn : 3 ≤ n) : jstar n + 2 ≤ n := by
  have h1 := one_le_jstar hn
  have h2 := three_pow_jstar_le hn
  have h3 : jstar n + 2 ≤ 3 ^ jstar n := by
    have : ∀ j : ℕ, 1 ≤ j → j + 2 ≤ 3 ^ j := by
      intro j hj
      induction j with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; norm_num
        · have := ih hk
          rw [pow_succ]; omega
    exact this _ h1
  omega

/-- The readout exponents at block `j* = jstar n`: `a = n − (j*+1)`, `c = 3^(j*+1) − n`. -/
def sA (n : ℕ) : ℕ := n - (jstar n + 1)
def sC (n : ℕ) : ℕ := 3 ^ (jstar n + 1) - n

/-- The readout state `3^a mod 2^c`. -/
def readout (n : ℕ) : ℕ := 3 ^ sA n % 2 ^ sC n

theorem sC_pos (n : ℕ) : 0 < sC n := by
  unfold sC; have := lt_three_pow_jstar n; omega

theorem one_le_sA {n : ℕ} (hn : 3 ≤ n) : 1 ≤ sA n := by
  unfold sA; have := jstar_add_two_le hn; omega

/-- `2·3^m ≤ 4^m` for `m ≥ 3`. -/
theorem two_mul_three_pow_le_four_pow {m : ℕ} (hm : 3 ≤ m) : 2 * 3 ^ m ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ, pow_succ]; omega

/-- **The base-6 readout theorem** (N2): for `n ≥ 3`, with `j* = jstar n`, `a = n − (j*+1)`
and `c = 3^(j*+1) − n`, the base-6 orbit of the Stoneham constant sits just above
`(3^a mod 2^c)/2^c`, within `2·3^(a−1)/2^(3^(j*+2) − n)`. -/
theorem stoneham_base6_readout (n : ℕ) (hn : 3 ≤ n) :
    (readout n : ℝ) / 2 ^ sC n < orbit 6 stoneham23 n ∧
      orbit 6 stoneham23 n
        ≤ (readout n : ℝ) / 2 ^ sC n + 2 * 3 ^ (sA n - 1) / 2 ^ (3 ^ (jstar n + 2) - n) := by
  set J := jstar n with hJ
  have hJ1 : 1 ≤ J := one_le_jstar hn
  have hJn : J + 2 ≤ n := jstar_add_two_le hn
  have h3Jn : 3 ^ J ≤ n := three_pow_jstar_le hn
  have hn3J : n < 3 ^ (J + 1) := lt_three_pow_jstar n
  -- the scaled series
  set g : ℕ → ℝ := fun j => (6 : ℝ) ^ n * sterm j with hg
  have hg_sum : Summable g := summable_sterm.mul_left _
  have hg_pos : ∀ j, 0 < g j := fun j => by
    have := sterm_pos j
    simp only [hg]; positivity
  have hmul : stoneham23 * (6 : ℝ) ^ n = ∑' j, g j := by
    rw [tsum_mul_left, mul_comm]; rfl
  have hshift_sum : Summable fun j => g (j + J) := (summable_nat_add_iff J).2 hg_sum
  have hshift_sum1 : Summable fun j => g (j + (J + 1)) := (summable_nat_add_iff (J + 1)).2 hg_sum
  -- split at J, then peel the term J
  have hsplit : ∑' j, g j = (∑ j ∈ Finset.range J, g j) + ∑' j, g (j + J) :=
    (hg_sum.sum_add_tsum_nat_add J).symm
  have hpeel : ∑' j, g (j + J) = g J + ∑' j, g (j + (J + 1)) := by
    rw [hshift_sum.tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    apply tsum_congr; intro j; congr 1; omega
  set T : ℝ := ∑' j, g (j + (J + 1)) with hT
  -- the head is an integer
  set S : ℕ := ∑ j ∈ Finset.range J, 3 ^ (n - (j + 1)) * 2 ^ (n - 3 ^ (j + 1)) with hS
  have hHead : (∑ j ∈ Finset.range J, g j) = (S : ℝ) := by
    rw [hS]; push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j < J := Finset.mem_range.mp hj
    have h3le : 3 ^ (j + 1) ≤ n := three_pow_le_of_lt_jstar hjJ
    have hj1 : j + 1 ≤ n := le_trans (Nat.lt_pow_self (by norm_num)).le h3le
    have h2 : (2 : ℝ) ^ (n - 3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) = 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have h3 : (3 : ℝ) ^ (n - (j + 1)) * 3 ^ (j + 1) = 3 ^ n := by
      rw [← pow_add]; congr 1; omega
    simp only [hg, sterm]
    rw [mul_one_div, div_eq_iff (by positivity), show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by
      rw [← mul_pow]; norm_num]
    rw [← h2, ← h3]; ring
  -- the block term is `3^a / 2^c`
  have hMid : g J = (3 : ℝ) ^ sA n / 2 ^ sC n := by
    simp only [hg, sterm, sA, sC, ← hJ]
    have h2 : (2 : ℝ) ^ (3 ^ (J + 1) - n) * 2 ^ n = 2 ^ (3 ^ (J + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h3 : (3 : ℝ) ^ (n - (J + 1)) * 3 ^ (J + 1) = 3 ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity),
      show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
    rw [← h2, ← h3]; ring
  -- tail bound: `T ≤ 2 · g (J+1)`
  have hT_pos : 0 < T := by
    rw [hT]
    exact Summable.tsum_pos hshift_sum1 (fun j => (hg_pos _).le) 0 (hg_pos _)
  have hT_le : T ≤ 2 * g (J + 1) := by
    have hterm : ∀ j, g (j + (J + 1)) ≤ g (J + 1) * (1 / 2) ^ j := by
      intro j
      have hexp : 3 ^ (J + 2) + j ≤ 3 ^ (j + J + 2) := by
        have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
        have hP : 1 ≤ 3 ^ (J + 2) := Nat.one_le_pow _ _ (by norm_num)
        calc 3 ^ (J + 2) + j ≤ 3 ^ (J + 2) * (j + 1) := by nlinarith
          _ ≤ 3 ^ (J + 2) * 3 ^ j := Nat.mul_le_mul_left _ hj3
          _ = 3 ^ (j + J + 2) := by rw [← pow_add]; congr 1; omega
      have hkey : (3 : ℝ) ^ (J + 2) * 2 ^ (3 ^ (J + 2)) * 2 ^ j
          ≤ 3 ^ (j + J + 2) * 2 ^ (3 ^ (j + J + 2)) := by
        have h3 : (3 : ℝ) ^ (J + 2) ≤ 3 ^ (j + J + 2) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (3 ^ (J + 2)) * 2 ^ j ≤ 2 ^ (3 ^ (j + J + 2)) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ one_le_two hexp
        calc (3 : ℝ) ^ (J + 2) * 2 ^ (3 ^ (J + 2)) * 2 ^ j
            = 3 ^ (J + 2) * (2 ^ (3 ^ (J + 2)) * 2 ^ j) := by ring
          _ ≤ 3 ^ (j + J + 2) * 2 ^ (3 ^ (j + J + 2)) :=
              mul_le_mul h3 h2 (by positivity) (by positivity)
      simp only [hg, sterm]
      rw [show j + (J + 1) + 1 = j + J + 2 by omega, show J + 1 + 1 = J + 2 by omega]
      rw [mul_one_div, mul_one_div, div_pow, one_pow, div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey
    have hgeom : Summable fun j : ℕ => g (J + 1) * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift_sum1.tsum_le_tsum hterm hgeom
    rw [hT]
    refine le_trans hle ?_
    rw [tsum_mul_left, tsum_geometric_two]
    ring_nf; exact le_refl _
  have hn3J2 : n < 3 ^ (J + 2) :=
    lt_of_lt_of_le hn3J (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hgJ1 : g (J + 1) = (3 : ℝ) ^ (sA n - 1) / 2 ^ (3 ^ (J + 2) - n) := by
    simp only [hg, sterm, sA, ← hJ]
    rw [show J + 1 + 1 = J + 2 by ring]
    have h2 : (2 : ℝ) ^ (3 ^ (J + 2) - n) * 2 ^ n = 2 ^ (3 ^ (J + 2)) := by
      rw [← pow_add]; congr 1; omega
    have h3 : (3 : ℝ) ^ (n - (J + 1) - 1) * 3 ^ (J + 2) = 3 ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity),
      show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
    rw [← h2, ← h3]; ring
  -- no wraparound: `T < 1/2^c`
  have hT_lt : T < 1 / (2 : ℝ) ^ sC n := by
    refine lt_of_le_of_lt hT_le ?_
    rw [hgJ1]
    have hsplit : 3 ^ (J + 2) - n = 2 * 3 ^ (J + 1) + sC n := by
      unfold sC; rw [← hJ]
      have : 3 ^ (J + 2) = 3 * 3 ^ (J + 1) := by rw [pow_succ]; ring
      omega
    have hnat : 2 * 3 ^ (sA n - 1) < 4 ^ (3 ^ (J + 1)) := by
      have ha : sA n - 1 < 3 ^ (J + 1) := by unfold sA; rw [← hJ]; omega
      have h9 : 3 ≤ 3 ^ (J + 1) := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * 3 ^ (sA n - 1) < 2 * 3 ^ (3 ^ (J + 1)) := by
            have := Nat.pow_lt_pow_right (by norm_num : 1 < 3) ha
            omega
        _ ≤ 4 ^ (3 ^ (J + 1)) := two_mul_three_pow_le_four_pow h9
    have hreal : (2 : ℝ) * 3 ^ (sA n - 1) < 4 ^ (3 ^ (J + 1)) := by exact_mod_cast hnat
    have h4 : (4 : ℝ) ^ (3 ^ (J + 1)) = 2 ^ (2 * 3 ^ (J + 1)) := by
      rw [pow_mul]; norm_num
    rw [hsplit, pow_add, ← h4]
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    have h2c : (0 : ℝ) < 2 ^ sC n := by positivity
    nlinarith [h2c, hreal]
  -- assemble: `orbit = r/2^c + T`
  have hab : 3 ^ sA n = 2 ^ sC n * (3 ^ sA n / 2 ^ sC n) + readout n := (Nat.div_add_mod _ _).symm
  have hread_lt : readout n < 2 ^ sC n := Nat.mod_lt _ (by positivity)
  have hMid' : g J = ((3 ^ sA n / 2 ^ sC n : ℕ) : ℝ) + (readout n : ℝ) / 2 ^ sC n := by
    rw [hMid]
    have h2c : (0 : ℝ) < 2 ^ sC n := by positivity
    have hcast : ((3 ^ sA n : ℕ) : ℝ) = (2 : ℝ) ^ sC n * ((3 ^ sA n / 2 ^ sC n : ℕ) : ℝ)
        + (readout n : ℝ) := by exact_mod_cast hab
    push_cast at hcast
    rw [hcast]; field_simp
  have hy_nonneg : 0 ≤ (readout n : ℝ) / 2 ^ sC n + T := by positivity
  have hy_lt : (readout n : ℝ) / 2 ^ sC n + T < 1 := by
    have h2c : (0 : ℝ) < 2 ^ sC n := by positivity
    have h1 : (readout n : ℝ) ≤ (2 : ℝ) ^ sC n - 1 := by
      have : readout n + 1 ≤ 2 ^ sC n := hread_lt
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this; linarith
    have hdiv : (readout n : ℝ) / 2 ^ sC n ≤ ((2 : ℝ) ^ sC n - 1) / 2 ^ sC n := by gcongr
    have hone : ((2 : ℝ) ^ sC n - 1) / 2 ^ sC n + 1 / 2 ^ sC n = 1 := by
      rw [← add_div, sub_add_cancel, div_self h2c.ne']
    linarith
  have horb : orbit 6 stoneham23 n = (readout n : ℝ) / 2 ^ sC n + T := by
    unfold orbit
    have hb6 : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
    rw [hb6, hmul, hsplit, hpeel, hHead, hMid']
    rw [show (S : ℝ) + (((3 ^ sA n / 2 ^ sC n : ℕ) : ℝ) + (readout n : ℝ) / 2 ^ sC n + T)
        = ((S + 3 ^ sA n / 2 ^ sC n : ℕ) : ℝ) + ((readout n : ℝ) / 2 ^ sC n + T) by
      push_cast; ring]
    rw [Int.fract_natCast_add]
    exact Int.fract_eq_self.mpr ⟨hy_nonneg, hy_lt⟩
  refine ⟨?_, ?_⟩
  · rw [horb]; linarith
  · rw [horb]
    have h2g : 2 * g (J + 1) = 2 * 3 ^ (sA n - 1) / 2 ^ (3 ^ (J + 2) - n) := by
      rw [hgJ1]; ring
    linarith [hT_le]

/-- Anchor: at `n = 10` the block is `j* = 2` (`9 ≤ 10 < 27`), so `a = 7`, `c = 17` and the
readout is `3^7 mod 2^17 = 2187`. -/
example : readout 10 = 2187 := by
  have hj : jstar 10 = 2 := by
    rw [jstar, Nat.find_eq_iff]; decide
  simp [readout, sA, sC, hj]

end NormalNumbers
