/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertGcdAverage
import NormalNumbers.JointLambertPrimeInputs

/-!
# The small prime pool: primes near `k³` suffice

§3 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` replaces the congruence primes near
`(log X)²` by primes near `L = k³`, where `k = ⌈4 log₂ log X⌉`.  The allocation of
`JointLambertPrimeSelection` needs `1 + killPoolSize k r` primes, plus one more to
pay for the single excluded prime `P(X)` of the AGP-range input.  Since
`killPoolSize k r ≤ k²` and the prime number theorem gives `≫ k³ / log k` primes in
`(k³, 2k³)`, the pool is eventually large enough **for every** `r`.

* `eventually_small_prime_pool` — for every `k ≥ K` and every `r`,
  `1 + killPoolSize k r + 1 ≤ #{p prime : k³ < p < 2k³}`.
  `k` is chosen by the caller; no existential `k ≥ K` replaces it, because an
  existence statement supplies no upper bound on `k` and the later schedule needs one.
* `exists_prime_allocation_small_pool` — the immediate consequence: an allocation
  out of that pool, avoiding divisibility of `jointB` by the one excluded `P`.

The analytic input is exactly `primeIntervalSupply_holds` (ordinary PNT), already
`#print axioms`-clean.  The elementary step is `log k ≤ 2√k`, which is
`Real.log_le_sub_one_of_pos` applied to `√k`; `k ≥ 1296` then gives `√k ≤ k/36`.
-/

namespace NormalNumbers.JointLambert

open Finset

/-- `log x ≤ 2√x` for `x > 0`: apply `log t ≤ t - 1` at `t = √x` and double. -/
private lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [h2] at h1
  linarith

/-- The elementary comparison behind the pool bound: `9 (log x)(x² + 2) ≤ x³` for
`x ≥ 1296`.  Hence `x² + 2 ≤ x³ / (9 log x)`, the PNT count at `L = x³`. -/
private lemma nine_log_mul_le {x : ℝ} (hx : 1296 ≤ x) :
    9 * Real.log x * (x ^ 2 + 2) ≤ x ^ 3 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs36 : 36 ≤ Real.sqrt x := by nlinarith
  have hsx : 36 * Real.sqrt x ≤ x := by nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := log_le_two_mul_sqrt hx0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith [sq_nonneg x, sq_nonneg (x - 1296)]

/-- **The small prime pool is eventually big enough, uniformly in `r`.**

For every `k ≥ K` and **every** `r`, the open interval `(k³, 2k³)` contains at least
`1 + killPoolSize k r + 1` primes: the allocation's `1 + killPoolSize k r` primes, plus
one spare to absorb the single excluded prime `P(X)`.

The analytic content is `primeIntervalSupply_holds` at `L = k³`, whose count
`L / (3 log L) = k³ / (9 log k)` dominates `k² + 2 ≥ 1 + killPoolSize k r + 1`. -/
theorem eventually_small_prime_pool :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ r : ℕ,
      1 + killPoolSize k r + 1 ≤ (((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime).card) := by
  obtain ⟨L0, hL0⟩ := primeIntervalSupply_holds
  refine ⟨max L0 1296, fun k hk r => ?_⟩
  have hk1296 : 1296 ≤ k := le_trans (le_max_right _ _) hk
  have hL0k : L0 ≤ k ^ 3 := by
    have : L0 ≤ k := le_trans (le_max_left _ _) hk
    calc L0 ≤ k := this
      _ ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
  have h2 : 2 ≤ k ^ 3 := by
    calc (2 : ℕ) ≤ k := by omega
      _ ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
  have hcount := hL0 (k ^ 3) hL0k h2
  set S := (((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime).card) with hS
  -- real-analytic core
  set x : ℝ := (k : ℝ) with hx
  have hxk : (1296 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hk1296
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hcast : ((k ^ 3 : ℕ) : ℝ) = x ^ 3 := by rw [hx]; push_cast; ring
  have hlogcube : Real.log (x ^ 3) = 3 * Real.log x := by
    rw [Real.log_pow]; norm_num
  rw [hcast, hlogcube] at hcount
  have hden : (0 : ℝ) < 9 * Real.log x := by linarith
  have hkey : (x ^ 2 + 2 : ℝ) ≤ x ^ 3 / (3 * (3 * Real.log x)) := by
    rw [le_div_iff₀ (by linarith)]
    have := nine_log_mul_le hxk
    nlinarith
  have hfinal : (x ^ 2 + 2 : ℝ) ≤ (S : ℝ) := le_trans hkey hcount
  -- back to ℕ
  have hnat : k ^ 2 + 2 ≤ S := by
    have : ((k ^ 2 + 2 : ℕ) : ℝ) ≤ (S : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  have := killPoolSize_le_sq k r
  omega

/-- **Allocation out of the small pool.**  With `k ≥ K` the pool of primes in
`(k³, 2k³)` supports the full CRT allocation *and* dodges the one excluded modulus
`P` (which is `1` or a prime, and may or may not lie in the interval — only the last
case actually costs a prime, and the spare `+1` pays for it). -/
theorem exists_prime_allocation_small_pool {K : ℕ}
    (hK : ∀ k : ℕ, K ≤ k → ∀ r : ℕ,
      1 + killPoolSize k r + 1 ≤ (((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime).card))
    (c k r P : ℕ) (hk : K ≤ k) :
    ∃ (q : ℕ) (p : ℕ → ℕ → ℕ),
      q ∈ (Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime ∧
      (∀ j t, j ∈ killedIdx k r → t < j + 1 →
        p j t ∈ (Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime) ∧
      (∀ j t, j ∈ killedIdx k r → t < j + 1 → p j t ≠ q) ∧
      (∀ j t j' t', j ∈ killedIdx k r → t < j + 1 → j' ∈ killedIdx k r → t' < j' + 1 →
        p j t = p j' t' → j = j' ∧ t = t') ∧
      (P ≠ 1 → ¬ P ∣ jointB c k r q p) := by
  classical
  have hcard : 1 + killPoolSize k r + ({P} : Finset ℕ).card ≤
      (((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime).card) := by
    simpa using hK k hk r
  obtain ⟨q, p, h1, h2, h3, h4, h5⟩ :=
    exists_prime_allocation c k r ((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime) {P}
      (fun π hπ => (Finset.mem_filter.mp hπ).2) hcard
  exact ⟨q, p, h1, h2, h3, h4, fun hP1 => h5 P (by simp) hP1⟩

/-! ### Permanent finite controls

Pool-exclusion cases for the spare prime: `P = 1`, `P` outside the interval, and `P`
inside it.  Only the last case actually removes a prime from the pool. -/

section Controls

/-- `P = 1` is genuinely excluded from the avoidance conclusion: `1` divides everything,
so the hypothesis `P ≠ 1` is not decoration. -/
example (n : ℕ) : (1 : ℕ) ∣ n := one_dvd n

/-- `P` outside the interval costs nothing: it is not a member of the pool, hence
removing it leaves the pool untouched.  (`k = 2`: pool primes lie in `(8,16)`, and
`P = 5` is not among them.) -/
example : (5 : ℕ) ∉ (Ioo (2 ^ 3) (2 * 2 ^ 3)).filter Nat.Prime := by decide

/-- `P` inside the interval is the only costly case, and costs exactly one prime:
`11 ∈ (8,16)` is prime, and the pool drops from `#{11,13} = 2` to `1`. -/
example : ((Ioo (2 ^ 3) (2 * 2 ^ 3)).filter Nat.Prime).card = 2 := by decide
example : (((Ioo (2 ^ 3) (2 * 2 ^ 3)).filter Nat.Prime).erase 11).card = 1 := by decide

/-- The pool bound is not vacuous at moderate `k`: the required count `1 + killPoolSize k r + 1`
is genuinely bounded by `k² + 2`, the quantity the PNT estimate dominates. -/
example (k r : ℕ) : 1 + killPoolSize k r + 1 ≤ k ^ 2 + 2 := by
  have := killPoolSize_le_sq k r; omega

end Controls

end NormalNumbers.JointLambert
