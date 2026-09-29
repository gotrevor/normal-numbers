/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertTailBounds
import NormalNumbers.JointLambertPrimeSelection

/-!
# Divisor averaging without coprimality, and the explicit `τ(A)` bound

This module supplies the elementary foundations of §2–§3 of
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`, the sharper quantitative route
(primes near `k³` instead of near `(log X)²`).  Nothing here is analytic.

* `tau_mul_le` — submultiplicativity `τ(mn) ≤ τ(m)τ(n)`, prime by prime
  (proved through `Nat.divisors_mul` and pointwise-product cardinality, so it
  needs no positivity at all).
* `sum_tau_progression_le_gcd` — the frozen coprime estimate
  `sum_tau_progression_le`, transported to an **arbitrary**
  progression at the cost of a factor `τ(gcd u A)`.  Writing `g = gcd(u,A)` and
  `u = g u'`, `A = g A'`, the reduced progression is coprime and satisfies the
  same `≤ H²` bound at the **same** `H`.  No claim `gcd(g, A/g) = 1` is made or
  needed: `u + mA = g·(u' + mA')` and submultiplicativity does the rest.
* `sum_tau_progression_le_noncoprime` — the same with `τ(A)`, since `g ∣ A`.
* `jointA_tau_le` — `τ(A) ≤ (a+1)(c+1)^(k²)` for the CRT modulus
  `A = q^a ∏_{j killed} P_j^c` of `JointLambertArithmetic`.  This is an **upper**
  bound only, so repeated submultiplicativity suffices and pairwise distinctness
  of the allocation primes is not required.  Equation (2) of the note, and the
  reason `2^(-k³)` beats the middle-tail cost.

Permanent finite controls are at the end of the file; they are `example`s, hence
compiler-enforced at every build.
-/

namespace NormalNumbers.JointLambert

open Finset NormalNumbers.SwingC2

/-! ### Submultiplicativity of `τ` -/

/-- **`τ` is submultiplicative**: `τ(mn) ≤ τ(m)·τ(n)`.

Every divisor of `mn` is a product of a divisor of `m` and a divisor of `n`
(`Nat.divisors_mul`), so the divisor set of `mn` is the pointwise product of the
two divisor sets, whose cardinality is at most the product of the cardinalities.
The degenerate cases `m = 0` or `n = 0` are covered too: both sides then have an
empty divisor set on the left. -/
theorem tau_mul_le (m n : ℕ) : tau (m * n) ≤ tau m * tau n := by
  simpa [tau, Nat.divisors_mul] using
    (Finset.card_mul_le (s := m.divisors) (t := n.divisors))

/-- Submultiplicativity over a finite product. -/
theorem tau_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    tau (∏ i ∈ s, f i) ≤ ∏ i ∈ s, tau (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [tau]
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons]
      exact le_trans (tau_mul_le _ _) (Nat.mul_le_mul_left _ ih)

/-! ### The divisor average without coprimality -/

/-- **Divisor averaging along an arbitrary progression** (note §2, equation (1)).

For `u > 0`, `A > 0`, `H ≥ 1` and every value `u + mA` (`m < M`) at most `H²`:
`∑_{m<M} τ(u + mA) ≤ τ(gcd u A) · (2M(1 + log H) + 2H)`.

The proof reduces to the frozen coprime estimate at the *same* `H`. -/
theorem sum_tau_progression_le_gcd {u A H M : ℕ} (hu : 0 < u) (hA : 0 < A)
    (hH : 1 ≤ H) (hbd : ∀ m, m < M → u + m * A ≤ H ^ 2) :
    (∑ m ∈ range M, (tau (u + m * A) : ℝ)) ≤
      (tau (Nat.gcd u A) : ℝ) * (2 * M * (1 + Real.log H) + 2 * H) := by
  classical
  set g := Nat.gcd u A with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left A hu
  set u' := u / g with hu'
  set A' := A / g with hA'
  have hgu : g * u' = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u A)
  have hgA : g * A' = A := Nat.mul_div_cancel' (Nat.gcd_dvd_right u A)
  have hcop : Nat.Coprime u' A' := Nat.coprime_div_gcd_div_gcd hgpos
  have hu'pos : 0 < u' := by
    rcases Nat.eq_zero_or_pos u' with h | h
    · exact absurd hgu (by simp [h]; omega)
    · exact h
  -- the reduced values are pointwise below the original ones
  have hsplit : ∀ m : ℕ, u + m * A = g * (u' + m * A') := by
    intro m; rw [Nat.mul_add, hgu, ← Nat.mul_assoc, Nat.mul_comm g m, Nat.mul_assoc, hgA]
  have hred : ∀ m, m < M → u' + m * A' ≤ H ^ 2 := by
    intro m hm
    have h1 : u' + m * A' ≤ g * (u' + m * A') := Nat.le_mul_of_pos_left _ hgpos
    have := hbd m hm
    rw [hsplit m] at this
    omega
  have hcore := sum_tau_progression_le (u := u') (A := A')
    (H := H) (M := M) hu'pos hcop hH hred
  have hpt : ∀ m ∈ range M,
      (tau (u + m * A) : ℝ) ≤ (tau g : ℝ) * (tau (u' + m * A') : ℝ) := by
    intro m _
    have : tau (u + m * A) ≤ tau g * tau (u' + m * A') := by
      rw [hsplit m]; exact tau_mul_le _ _
    exact_mod_cast this
  calc (∑ m ∈ range M, (tau (u + m * A) : ℝ))
      ≤ ∑ m ∈ range M, (tau g : ℝ) * (tau (u' + m * A') : ℝ) := Finset.sum_le_sum hpt
    _ = (tau g : ℝ) * ∑ m ∈ range M, (tau (u' + m * A') : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (tau g : ℝ) * (2 * M * (1 + Real.log H) + 2 * H) := by
        exact mul_le_mul_of_nonneg_left hcore (by positivity)

/-- **The `τ(A)` form of the non-coprime divisor average** (note §2).
`gcd u A` divides `A`, and `τ` is monotone along divisibility of a positive number. -/
theorem sum_tau_progression_le_noncoprime {u A H M : ℕ} (hu : 0 < u) (hA : 0 < A)
    (hH : 1 ≤ H) (hbd : ∀ m, m < M → u + m * A ≤ H ^ 2) :
    (∑ m ∈ range M, (tau (u + m * A) : ℝ)) ≤
      (tau A : ℝ) * (2 * M * (1 + Real.log H) + 2 * H) := by
  have hmono : tau (Nat.gcd u A) ≤ tau A :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hA.ne' (Nat.gcd_dvd_right u A))
  have hbrack : (0 : ℝ) ≤ 2 * M * (1 + Real.log H) + 2 * H := by
    have : (0 : ℝ) ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
    positivity
  refine le_trans (sum_tau_progression_le_gcd hu hA hH hbd) ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmono) hbrack

/-! ### The explicit divisor bound for the CRT modulus -/

/-- `τ(P_j^c) ≤ (c+1)^(j+1)` when the `j+1` slot primes are prime. -/
private lemma tau_slotProd_pow_le {c j : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : ∀ t, t < j + 1 → (p j t).Prime) :
    tau (slotProd p j ^ c) ≤ (c + 1) ^ (j + 1) := by
  classical
  have hrw : slotProd p j ^ c = ∏ t ∈ range (j + 1), p j t ^ c := by
    rw [slotProd, ← Finset.prod_pow]
  rw [hrw]
  refine le_trans (tau_prod_le _ _) ?_
  have : ∀ t ∈ range (j + 1), tau (p j t ^ c) ≤ c + 1 := by
    intro t ht
    exact le_of_eq (tau_prime_pow (hp t (Finset.mem_range.mp ht)) c)
  calc ∏ t ∈ range (j + 1), tau (p j t ^ c)
      ≤ ∏ _t ∈ range (j + 1), (c + 1) := Finset.prod_le_prod' this
    _ = (c + 1) ^ (j + 1) := by simp

/-- **Equation (2) of the note**: `τ(A) ≤ (a+1)(c+1)^(k²)` for the CRT modulus
`A = q^a ∏_{j killed} P_j^c`.

Only an *upper* bound is claimed, so repeated submultiplicativity suffices: the
allocation primes need not be pairwise distinct, and no exact multiplicativity
step is taken.  The exponent collapses through `killPoolSize_le_sq`. -/
theorem jointA_tau_le {c a k r q : ℕ} {p : ℕ → ℕ → ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a)
    (hq : q.Prime) (hp : ∀ j t, j ∈ killedIdx k r → t < j + 1 → (p j t).Prime) :
    tau (jointA c a k r q p) ≤ (a + 1) * (c + 1) ^ (k ^ 2) := by
  classical
  have hcore : tau (killCore c k r p) ≤ (c + 1) ^ killPoolSize k r := by
    refine le_trans (tau_prod_le _ _) ?_
    calc ∏ j ∈ killedIdx k r, tau (slotProd p j ^ c)
        ≤ ∏ j ∈ killedIdx k r, (c + 1) ^ (j + 1) :=
          Finset.prod_le_prod' fun j hj => tau_slotProd_pow_le (fun t ht => hp j t hj ht)
      _ = (c + 1) ^ killPoolSize k r := by rw [killPoolSize, Finset.prod_pow_eq_pow_sum]
  have hexp : (c + 1) ^ killPoolSize k r ≤ (c + 1) ^ (k ^ 2) :=
    Nat.pow_le_pow_right (by omega) (killPoolSize_le_sq k r)
  calc tau (jointA c a k r q p)
      ≤ tau (q ^ a) * tau (killCore c k r p) := tau_mul_le _ _
    _ = (a + 1) * tau (killCore c k r p) := by rw [tau_prime_pow hq]
    _ ≤ (a + 1) * (c + 1) ^ (k ^ 2) :=
        Nat.mul_le_mul_left _ (le_trans hcore hexp)

/-! ### Permanent finite controls

These are compiler-enforced at every build. -/

section Controls

/-- `M = 0`: the sum is empty. -/
example {u A : ℕ} :
    (∑ m ∈ range 0, (tau (u + m * A) : ℝ)) = 0 := by simp

/-- `u = 0` and `A = 0` are explicitly outside the contract of the average:
the statement takes `0 < u` and `0 < A` as hypotheses, and indeed `τ(0) = 0`
would make the `gcd` factor vacuous. -/
example : tau 0 = 0 := by simp [tau]

/-- Control `u = 1, A = 4, M = 3`: `τ(1)+τ(5)+τ(9) = 1+2+3 = 6`, and `g = 1`. -/
example : tau 1 + tau 5 + tau 9 = 6 := by decide
example : Nat.gcd 1 4 = 1 := by decide

/-- Control `u = 6, A = 12, M = 3`: `τ(6)+τ(18)+τ(30) = 4+6+8 = 18`, `g = 6`,
the reduced progression `1,3,5` has divisor sum `1+2+2 = 5`, and the
submultiplicative bound is the strict inequality `18 ≤ τ(6)·5 = 20`.
The final line is the trap: `gcd(g, A/g) = gcd(6,2) = 2 ≠ 1`, so any proof that
silently assumed `g` coprime to `A/g` is wrong. -/
example : tau 6 + tau 18 + tau 30 = 18 := by decide
example : Nat.gcd 6 12 = 6 := by decide
example : tau 1 + tau 3 + tau 5 = 5 := by decide
example : tau 6 + tau 18 + tau 30 ≤ tau 6 * (tau 1 + tau 3 + tau 5) := by decide
example : tau 6 + tau 18 + tau 30 ≠ tau 6 * (tau 1 + tau 3 + tau 5) := by decide
example : Nat.gcd 6 (12 / Nat.gcd 6 12) = 2 := by decide

/-- A repeated-prime control for the `jointA` **upper** bound: with all slot
primes equal the bound still holds, while the exact multiplicative formula fails.
Here `c = 2`, one killed slot `j = 0` with a single prime `p = 3`, `q = 3`, `a = 2`:
`A = 3² · 3² = 81`, `τ(A) = 5 ≤ (a+1)(c+1)^(k²) = 3 · 3^4 = 243`, whereas the
"all primes distinct" formula would give `(a+1)(c+1)^t = 3 · 3 = 9 ≠ 5`. -/
example : tau (jointA 2 2 2 1 3 (fun _ _ => 3)) ≤ (2 + 1) * (2 + 1) ^ (2 ^ 2) := by
  refine jointA_tau_le (by norm_num) (by norm_num) (by norm_num) ?_
  intro j t _ _; norm_num

end Controls

end NormalNumbers.JointLambert
