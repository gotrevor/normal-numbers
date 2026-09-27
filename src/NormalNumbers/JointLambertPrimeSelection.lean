/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.JointLambertArithmetic

/-!
# Prime selection for the joint Lambert progression (paper §3 + §4 head)

Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md`, §3 (the inherited analytic
input) and the prime-selection opening of §4.

`NormalNumbers.JointLambert.exists_joint_progression` (in `JointLambertArithmetic.lean`)
is a *finite CRT theorem*: it takes the primes `q` and `p j t` as **data**.  This file
supplies that data.  It is the first place an analytic input is unavoidable, and both
inputs are carried as **explicit named `Prop`s passed as hypotheses** — `AGP` and
`PrimeIntervalSupply` — never as global axioms, and never as the old vacuous
`PrimeDensityAP`.

## The two inputs

* `AGP` — the Alford–Granville–Pomerance consequence used by Vandehey, Prop. 2.1:
  there are `X0, D0` such that for every `X ≥ X0` an exceptional set `𝒟(X)` of at most
  `D0` integers, each exceeding `log X`, exists **before** any modulus is chosen, and
  for every `B ≥ 1` with `B ≤ X^(1/4)`, every `u` coprime to `B`, and no exceptional `D`
  dividing `B`, the count of primes `≤ X` in the class `u mod B` is at least
  `X / (2 φ(B) log X)`.
* `PrimeIntervalSupply` — the standard PNT consequence that `(L, 2L)` contains at least
  `L / (3 log L)` primes for `L` large.

Neither is strengthened here.  The exceptional set is quantified so that it is fixed
before `B`, `u` and the prime allocation, exactly as the paper demands.

## Structure

1. `killOffset` / `killPoolSize` flatten the doubly-indexed killed-slot family
   `(j, t) ↦ p j t` into one initial segment of length `∑_{j<k, j≠r} (j+1)`.
2. `exists_prime_allocation` — the **finite avoidance and allocation** theorem: a pool
   of `1 + killPoolSize k r + #𝒟` primes suffices to pick `q` and every `p j t`
   distinctly while no exceptional modulus divides `jointB`.  One prime is deleted per
   exceptional modulus; `D = 0` and moduli with no pool prime divisor are handled.
3. `pow_four_le_two_pow` / `exists_selection_scale` — the asymptotic availability of the
   parameters, *proved*, not assumed.
4. `exists_joint_prime_candidates` — the target: from `AGP` and `PrimeIntervalSupply`,
   parameters `k ≥ K` with the dyadic schedule `L = 2^k`, `U = 2^(k^4)`, `X = U^4`,
   primes in `(L, 2L)`, the full `exists_joint_progression` conclusion, the size bounds
   `Q ≤ (2L)^(a-1)`, `B ≤ (2L)^(1 + c · killPoolSize)`, `B ≤ U`, `Q ≤ U`, `R > L`, and a
   real lower bound `M / (16 k^4)` on the number of prime candidate indices.

The dyadic schedule (`L = 2^k` rather than the paper's `L = ⌊(log₂ X)²⌋`) is authorized
for the *qualitative* theorem; it is what the scalar formalization uses and it avoids
logarithmic floors.  The quantitative all-`N` bound of the paper is a separate target.
-/

namespace NormalNumbers.JointLambert

open Finset

/-- **The AGP input** (Alford–Granville–Pomerance 1994, in the form of Vandehey,
Prop. 2.1).  Source-faithful: the exceptional set `Dset` depends only on `X`, and is
therefore fixed *before* the modulus `B`, the residue `u`, and the prime allocation. -/
def AGP : Prop :=
  ∃ X0 D0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    ∃ Dset : Finset ℕ, Dset.card ≤ D0 ∧ (∀ D ∈ Dset, Real.log X < D) ∧
      ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) →
        Nat.Coprime u B → (∀ D ∈ Dset, ¬ D ∣ B) →
        (X : ℝ) / (2 * B.totient * Real.log X) ≤
          (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ)

/-- **The prime-interval supply input**: a standard PNT consequence, that the *open*
interval `(L, 2L)` contains at least `L / (3 log L)` primes once `L` is large. -/
def PrimeIntervalSupply : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → 2 ≤ L →
    (L : ℝ) / (3 * Real.log L) ≤ (((Ioo L (2 * L)).filter Nat.Prime).card : ℝ)

/-- Total number of killed-slot primes needed: `∑_{j < k, j ≠ r} (j + 1)`. -/
def killPoolSize (k r : ℕ) : ℕ := ∑ j ∈ killedIdx k r, (j + 1)

/-- Offset of killed slot `j` in the flat enumeration of the killed-slot primes. -/
def killOffset (k r j : ℕ) : ℕ :=
  ∑ i ∈ (killedIdx k r).filter (fun i => i < j), (i + 1)

/-- The target of this file, with its analytic inputs as hypotheses.  See the module
docstring.  TEMPORARY `sorry`: the statement is fixed first so that partial scaffolding
cannot be mistaken for success. -/
theorem exists_joint_prime_candidates (hagp : AGP) (hpis : PrimeIntervalSupply)
    {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r) (K : ℕ) :
    ∃ (k q : ℕ) (p : ℕ → ℕ → ℕ) (R u : ℕ),
      K ≤ k ∧ r < k ∧
      2 ^ k < q ∧ q < 2 * 2 ^ k ∧ q.Prime ∧
      (∀ j t, j < k → j ≠ r → t < j + 1 →
        (p j t).Prime ∧ 2 ^ k < p j t ∧ p j t < 2 * 2 ^ k) ∧
      -- the complete `exists_joint_progression` contract
      0 < R ∧ R < jointA c a k r q p ∧ 1 ≤ u ∧ u < jointB c k r q p ∧
      R + r = jointQ a q * u ∧
      jointA c a k r q p = jointQ a q * jointB c k r q p ∧
      u ≡ 1 [MOD q] ∧ Nat.Coprime u (jointB c k r q p) ∧
      R + r ≡ jointQ a q [MOD q ^ a] ∧
      (∀ j, j < k → j ≠ r → R + j ≡ slotProd p j ^ (c - 1) [MOD slotProd p j ^ c]) ∧
      (∀ m j, j < k → j ≠ r →
        c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (R + m * jointA c a k r q p + j)) ∧
      (∀ m, (u + m * jointB c k r q p).Prime →
        NormalNumbers.SwingC2.tau (R + m * jointA c a k r q p + r) = 2 * a) ∧
      (∀ j, k ≤ j → j < 2 ^ k → Nat.Coprime (R + j) (jointA c a k r q p)) ∧
      -- explicit size bookkeeping
      jointQ a q ≤ (2 * 2 ^ k) ^ (a - 1) ∧
      jointB c k r q p ≤ (2 * 2 ^ k) ^ (1 + c * killPoolSize k r) ∧
      jointB c k r q p ≤ 2 ^ (k ^ 4) ∧ jointQ a q ≤ 2 ^ (k ^ 4) ∧ 2 ^ k < R ∧
      -- the quantitative prime-candidate count
      ((2 ^ (4 * k ^ 4) / jointB c k r q p + 1 : ℕ) : ℝ) / (16 * k ^ 4) ≤
        (((range (2 ^ (4 * k ^ 4) / jointB c k r q p + 1)).filter
          (fun m => (u + m * jointB c k r q p).Prime ∧
            u + m * jointB c k r q p ≤ 2 ^ (4 * k ^ 4))).card : ℝ) := by
  sorry

end NormalNumbers.JointLambert
