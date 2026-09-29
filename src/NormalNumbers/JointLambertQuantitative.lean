/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertQuantitativeStatement
import NormalNumbers.JointLambertUnconditional
import NormalNumbers.JointLambertGcdAverage
import NormalNumbers.JointLambertSmallPool

/-!
# The quantitative joint Lambert theorem

The two ratified endpoints of the counting campaign.  `jointWordCount` and its predicate
are frozen in `JointLambertQuantitativeStatement.lean`; `orbit` and `E_b` are the ones of
`JointLambertStatement.lean`, so the qualitative theorem
`jointWords_unconditional` and these counts speak about the same object.

* `jointWords_quantitative` — for **every** `N ≥ N₀`,
  `A(N) ≥ N exp(-C (log log N)² log log log N)`.
  The parenthesisation is load-bearing: `(-C) * (log log N)^2 * (log log log N)`.
* `jointWords_power_count` — for each **fixed** `ε > 0`, eventually `A(N) ≥ N^{1-ε}`.

Paper route: `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §§3–5.  The open obligations are
named below with a content locator each; no opaque `Prop` hypothesis stands in for them.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- The iterated-logarithm rate is `o(log N)`: for every `C > 0` and `ε > 0`,
eventually `C (log log N)² log log log N ≤ ε log N`.

This is the only analytic input of §5 of the note, and it is what converts the
exponential-in-iterated-logs count into the power count. -/
theorem iteratedLog_rate_le_eps_log (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * (Real.log (Real.log (N : ℝ))) ^ 2 * Real.log (Real.log (Real.log (N : ℝ)))
        ≤ ε * Real.log (N : ℝ) := by
  sorry

/-- **The quantitative joint Lambert count.**  For every finite set `S` of bases `≥ 2`
and every choice of a nonempty valid word in each base, the number of offsets `n < N` at
which all the words start simultaneously is at least
`N exp(-C (log log N)² log log log N)` for all `N ≥ N₀`.

`C` and `N₀` depend on `S` and the words.  No uniformity in the bases and no effective
threshold is claimed.

Route (note §§3–5): at each large height `X` choose `k = ⌈4 log₂ log X⌉`, `L = k³`, draw the
CRT allocation primes from `(L, 2L)` via `exists_prime_allocation_small_pool`, take `P(X)`
from `exists_pointwise_exponential_distribution` first, get `≥ M/(4 log X)` prime
candidates with `M = ⌊X/B⌋+1`, kill the tail in three ranges
(`sum_tau_progression_le_noncoprime` and `jointA_tau_le` in the middle range), Markov at the
fixed threshold `2δ`, keep the good-set CARDINALITY, and convert to every `N` by
`X = ⌊N/D_N⌋`. -/
theorem jointWords_quantitative (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b)
    (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ))))
          ≤ (jointWordCount S lengths values N : ℝ) := by
  sorry

/-- **The power count.**  For each fixed `ε > 0`, eventually `A(N) ≥ N^{1-ε}`.
Derived from `jointWords_quantitative` and `iteratedLog_rate_le_eps_log`; `ε > 1` is
allowed by the stated type and is covered by the same argument. -/
theorem jointWords_power_count (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b)
    (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (jointWordCount S lengths values N : ℝ) := by
  obtain ⟨C, hC, N1, hN1⟩ := jointWords_quantitative S hb2 lengths values hwin
  obtain ⟨N2, hN2⟩ := iteratedLog_rate_le_eps_log C ε hC hε
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 _) hN)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  refine le_trans ?_ (hN1 N hN1')
  -- `N ^ (1 - ε) = N * exp (-ε * log N) ≤ N * exp (-C * (log log N)^2 * log log log N)`
  have hkey := hN2 N hN2'
  have hrw : (N : ℝ) ^ (1 - ε) = (N : ℝ) * Real.exp (-ε * Real.log (N : ℝ)) := by
    rw [Real.rpow_def_of_pos hNR,
      show Real.log (N : ℝ) * (1 - ε) = Real.log (N : ℝ) + -ε * Real.log (N : ℝ) by ring,
      Real.exp_add, Real.exp_log hNR]
  rw [hrw]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hNR.le
  nlinarith [hkey]

/-! ### Permanent audit examples for the ratified endpoints -/

/-- Exact-type audit anchor for the main count. -/
example (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b) (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ))))
          ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_quantitative S hb2 lengths values hwin

/-- Exact-type audit anchor for the power count. -/
example (S : Finset ℕ) (hb2 : ∀ b ∈ S, 2 ≤ b) (lengths values : ℕ → ℕ)
    (hwin : ∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_power_count S hb2 lengths values hwin ε hε

/-- The multiplicatively dependent specialization `S = {2, 4}`, with the binary word `11`
(`lengths 2 = 2`, `values 2 = 3`) and the leading-zero base-4 word `0` (`values 4 = 0`). -/
example : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 - (1 / 2 : ℝ))
      ≤ (jointWordCount ({2, 4} : Finset ℕ)
          (fun b => if b = 2 then 2 else 1) (fun b => if b = 2 then 3 else 0) N : ℝ) := by
  refine jointWords_power_count _ (by decide) _ _ ?_ (1 / 2) (by norm_num)
  decide

end NormalNumbers.JointLambert
