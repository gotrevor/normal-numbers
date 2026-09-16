/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation

/-!
# Mertens' theorem for a subset of the primes — the interface and its residue-class instance

Campaign A (prime-subset Lambert series).  The base-`b` schedule of `G4SchedB*` consumes the
lower Mertens bound `log log R ≤ ∑_{p < R} 1/p + 1` at one single place
(`G4SchedBParams.sum_inv_smallPrimes_ge`, feeding `G4SchedBBudget.main_term_le`).  The audit of
2026-09-16 (`DESIGN-2026-09-16-prime-subset.md`) shows that what the schedule actually needs is a
**rate**: for the cutoff exponent `e` (i.e. `R = 2^{2^e}`) it needs

    ∑_{p ∈ S, p < R} 1/p  ≥  c·e − C     for a fixed `c > 0`,

because the cutoff exponent may be inflated by any constant factor (the schedule's window for `e`
is `[exp(O(K log K)), exp(Θ(K²))]`) but **not** by an unbounded one — so mere divergence of
`∑_{p ∈ S} 1/p` is not enough for this route.  This module isolates that hypothesis as
`MertensRate` and sets up the elementary chain that establishes it for a residue class.

## The chain (each step a named leaf)

With `A_S(N) = ∑_{p ∈ S, p < N} (log p)/p` and `x = 1 + λ/log N`:

* `sumLog_tail_le` — `∑_{n > N} Λ(n)·n^{−x} ≤ C₁·e^{−λ}·(log N)/λ`, from Chebyshev's
  `ψ t ≤ (log 4 + 4)·t` by Abel summation.
* `sumLog_ge_of_LSeries_ge` — the transfer `LSeries lower bound ⟹ A_S(N) ≥ c·log N − C`,
  using the tail bound and `p^{−(x−1)} ≤ 1`.
* `mertensRate_of_sumLog` — partial summation `1/p = (log p / p)·(log p)⁻¹`, turning
  `A_S(N) ≥ c log N − C` into `∑_{p ∈ S, p < N} 1/p ≥ c·log log N − C'`.
* `sumLog_residueClass_ge` / `mertensRate_residueClass` — the instance for `p ≡ a (mod q)`,
  fed by `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`.

Nothing here mentions the schedule; `MertensRate` is the whole interface it will consume.
-/

open Finset Real

namespace NormalNumbers.G4.MertensAP

variable (S : ℕ → Prop) [DecidablePred S]

/-- `∑_{p < N, p ∈ S} 1/p`, the quantity the schedule consumes. -/
noncomputable def sumInvPrimesIn (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow with S p, (p : ℝ)⁻¹

/-- `∑_{p < N, p ∈ S} (log p)/p`, the Mertens-with-`log` intermediate. -/
noncomputable def sumLogPrimesIn (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow with S p, Real.log p / p

/-- **The interface.**  `S` has Mertens rate `c` with defect `C`: the prime reciprocals of `S`
below `N` exceed `c·log log N − C`.  The schedule needs exactly this, with `c` fixed and `C`
arbitrary, because it may inflate the cutoff exponent by the constant factor `1/c`. -/
def MertensRate (c C : ℝ) : Prop :=
  0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * Real.log (Real.log N) - C ≤ sumInvPrimesIn S N

variable {S}

lemma sumInvPrimesIn_nonneg (N : ℕ) : 0 ≤ sumInvPrimesIn S N :=
  Finset.sum_nonneg fun p _ => by positivity

lemma sumLogPrimesIn_nonneg (N : ℕ) : 0 ≤ sumLogPrimesIn S N := by
  refine Finset.sum_nonneg fun p hp => ?_
  have : 1 ≤ p := (Nat.prime_of_mem_primesBelow (Finset.mem_filter.1 hp).1).one_lt.le.trans' le_rfl
  positivity

/-- Subsetting only shrinks the sums: the monotonicity that makes every *upper* use of the
harmonic sum in the schedule free. -/
lemma sumInvPrimesIn_le_of_subset {S' : ℕ → Prop} [DecidablePred S']
    (h : ∀ p, S p → S' p) (N : ℕ) : sumInvPrimesIn S N ≤ sumInvPrimesIn S' N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h p hp.2⟩

/-! ### Leaf 1 — the Chebyshev tail (no residue classes) -/

/-- **Leaf.**  The von Mangoldt tail beyond `N` at exponent `x = 1 + λ/log N`, bounded by Abel
summation against Chebyshev's `ψ t ≤ (log 4 + 4)·t`.  The shape recorded here is the one the
transfer step needs: the tail is `≤ 11·e^{−λ}·(log N)/λ`. -/
theorem sumLog_tail_le {N : ℕ} (hN : 16 ≤ N) {lam : ℝ} (hlam : 1 ≤ lam)
    (hlam' : lam ≤ Real.log N) :
    ∑' n : ℕ, (if N < n then ArithmeticFunction.vonMangoldt n else 0)
        / (n : ℝ) ^ (1 + lam / Real.log N)
      ≤ 11 * Real.exp (-lam) * Real.log N / lam := by
  sorry

/-! ### Leaf 2 — the transfer from the `L`-series lower bound to `A_S(N)` -/

/-- **Leaf.**  If the Dirichlet series of `S`-primes weighted by `log` is bounded below by
`c/(x−1) − C₀` on `(1, 2]`, then `A_S(N) = ∑_{p ∈ S, p < N} (log p)/p ≥ c'·log N − C'` for
constants depending only on `c, C₀`.  Steps 1, 3, 4 of the design chain: split at `N`, use
`p^{−(x−1)} ≤ 1` below `N` and `sumLog_tail_le` above, and choose `λ = log(11/c₁)` with
`c₁ = c/2`. -/
theorem sumLog_ge_of_LSeries_ge {c C₀ : ℝ} (hc : 0 < c)
    (h : ∀ x : ℝ, 1 < x → x ≤ 2 →
      c / (x - 1) - C₀
        ≤ ∑' n : ℕ, (if n.Prime ∧ S n then Real.log n else 0) / (n : ℝ) ^ x) :
    ∃ c' C' : ℝ, 0 < c' ∧ ∀ N : ℕ, 2 ≤ N → c' * Real.log N - C' ≤ sumLogPrimesIn S N := by
  sorry

/-! ### Leaf 3 — partial summation `A_S ↦ ∑ 1/p` -/

/-- **Leaf.**  Partial summation: `1/p = (log p / p)·(log p)⁻¹`, so a linear-in-`log N` lower
bound for `A_S` gives a `log log N` lower bound for the reciprocal sum, with the same constant
up to the defect. -/
theorem mertensRate_of_sumLog {c C : ℝ} (hc : 0 < c)
    (h : ∀ N : ℕ, 2 ≤ N → c * Real.log N - C ≤ sumLogPrimesIn S N) :
    ∃ C' : ℝ, MertensRate S c C' := by
  sorry

/-! ### The residue-class instance -/

section ResidueClass

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Leaf.**  The hypothesis of `sumLog_ge_of_LSeries_ge` for `S = {p : p ≡ a (q)}`, obtained
from `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` after discarding the
prime-power part (`summable_residueClass_non_primes_div`, uniformly `O(1)` for `x ≥ 1`). -/
theorem LSeries_residueClass_primes_ge (ha : IsUnit a) :
    ∃ C₀ : ℝ, ∀ x : ℝ, 1 < x → x ≤ 2 →
      ((q.totient : ℝ)⁻¹) / (x - 1) - C₀
        ≤ ∑' n : ℕ, (if n.Prime ∧ (n : ZMod q) = a then Real.log n else 0) / (n : ℝ) ^ x := by
  sorry

/-- **Mertens in arithmetic progressions, in the form the schedule needs.**  Not in mathlib;
assembled here from the `L`-series lower bound plus Chebyshev and two partial summations. -/
theorem mertensRate_residueClass (ha : IsUnit a) :
    ∃ c C : ℝ, MertensRate (fun p => (p : ZMod q) = a) c C := by
  obtain ⟨C₀, hC₀⟩ := LSeries_residueClass_primes_ge ha
  obtain ⟨c', C', hc', hA⟩ :=
    sumLog_ge_of_LSeries_ge (S := fun p => (p : ZMod q) = a)
      (inv_pos.mpr (mod_cast q.totient.pos_of_neZero)) hC₀
  obtain ⟨C'', hM⟩ := mertensRate_of_sumLog hc' hA
  exact ⟨c', C'', hM⟩

end ResidueClass

end NormalNumbers.G4.MertensAP
