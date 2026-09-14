/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeLambertDefs
import NormalNumbers.Disjunctive

/-!
# The base-four prime Lambert number `G₄`: frozen endpoint

The G4 disjunctivity campaign (`KICKOFF-2026-09-14-g4-disjunctivity.md`) targets the candidate
theorem that

  `G₄ = ∑_{p prime} 1/(4^p − 1) = ∑_{n ≥ 1} ω(n)/4^n`

is disjunctive in base `4`, hence in base `2`.  This module pins the endpoint:

* `primeLambertAtBase b = ∑' n, ω(n)/bⁿ` and `primeLambertFour = primeLambertAtBase 4`.
  ⚠️ `PrimeLambert.primeLambert` is the **base-two** number and is left untouched
  (`primeLambertAtBase_two` records the agreement).
* summability at every base `b ≥ 2` (`summable_omegaR_div_pow`);
* the prime-sum form `primeSumAtBase b = ∑'_{p prime} 1/(bᵖ − 1)` and the identity
  `primeSumAtBase b = primeLambertAtBase b` (`primeSumAtBase_eq_primeLambertAtBase`);
* the headline Props `G4DisjunctiveFour` / `G4DisjunctiveTwo`, and the *proved* reduction
  `isDisjunctive_two_of_four` through the existing `isDisjunctive_pow_iff` (`b = 2`, `k = 2`).

The disjunctivity statements themselves are **not** proved here; `G4Wiring.lean` reduces them to
the named analytic inputs A–E of the candidate proof.
-/

open Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- The prime Lambert number at integer base `b`: `∑_{n ≥ 0} ω(n) / bⁿ` (the `n = 0` term is `0`). -/
noncomputable def primeLambertAtBase (b : ℕ) : ℝ := ∑' n : ℕ, omegaR n / (b : ℝ) ^ n

/-- **`G₄`**, the base-four prime Lambert number `∑ ω(n)/4ⁿ`. -/
noncomputable def primeLambertFour : ℝ := primeLambertAtBase 4

/-- `primeLambertAtBase 2` is the existing base-two constant. -/
theorem primeLambertAtBase_two : primeLambertAtBase 2 = primeLambert := by
  simp [primeLambertAtBase, primeLambert]

/-- Summability of `ω(n)/bⁿ` for every base `b ≥ 2`. -/
lemma summable_omegaR_div_pow {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun n : ℕ => omegaR n / (b : ℝ) ^ n) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / (b : ℝ))) (by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_lt_one (by linarith)]; linarith)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · have := omegaR_nonneg n; positivity
  · rw [div_eq_mul_inv, ← inv_pow, pow_one, one_div]
    gcongr
    exact omegaR_le n

/-- The prime-sum form `∑_{p prime} 1/(bᵖ − 1)`. -/
noncomputable def primeSumAtBase (b : ℕ) : ℝ := ∑' p : Nat.Primes, 1 / ((b : ℝ) ^ (p : ℕ) - 1)

/-- The headline Prop of the campaign: `G₄` is disjunctive in base four. -/
def G4DisjunctiveFour : Prop := IsDisjunctive 4 primeLambertFour

/-- The binary corollary: `G₄` is disjunctive in base two. -/
def G4DisjunctiveTwo : Prop := IsDisjunctive 2 primeLambertFour

/-- Base four to base two, through the existing base-power dictionary (`k = 2`). -/
theorem isDisjunctive_two_of_four (h : IsDisjunctive 4 primeLambertFour) :
    IsDisjunctive 2 primeLambertFour := by
  have := isDisjunctive_pow_iff 2 2 (by norm_num) (by norm_num) primeLambertFour
  norm_num at this
  exact this.2 h

theorem G4DisjunctiveTwo_of_four (h : G4DisjunctiveFour) : G4DisjunctiveTwo :=
  isDisjunctive_two_of_four h

end NormalNumbers.PrimeLambert
