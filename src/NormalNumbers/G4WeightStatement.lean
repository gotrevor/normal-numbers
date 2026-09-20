/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4LogLogPowSched
import NormalNumbers.G4WeightASched

/-!
# The audit surface for campaign B: the additive weights with unbounded coefficients

Each headline is restated here with every abbreviation unwound, so an auditor reads the
arithmetic function itself and never a `TWeight`, a `weightLambert` or a `subsetWeightLambert`.

In words:

> Fix a base `b ≥ 3` and a coefficient vector `c : ℕ → ℕ` growing no faster than a fixed power
> of `log₂ log₂`.  Then the real number
> `∑_n (#{p : p ∣ n} + ∑_{p ∣ n} c_p·(v_p(n) − 1)) / bⁿ`
> is **disjunctive** in base `b`: every finite base-`b` word occurs in its expansion.  The same
> holds with the prime counts restricted to any prime set `S` carrying a Mertens rate — in
> particular any residue class `p ≡ a (mod q)` with `a` a unit.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-- **Audit form of the unbounded-coefficient headline.** -/
theorem audit_isDisjunctive_weight_logLogPow (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' n : ℕ,
      ((n.primeFactors.card + ∑ p ∈ n.primeFactors, c p * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) := by
  have hrw : (∑' n : ℕ,
      ((n.primeFactors.card + ∑ p ∈ n.primeFactors, c p * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) = weightLambert b c := by
    unfold weightLambert
    refine tsum_congr fun n => ?_
    rw [weightW_eq_cast]
    unfold weightN
    rw [cardDistinctFactors_eq_card_primeFactors]
  rw [hrw]
  exact SchedB.isDisjunctive_weight_logLogPow c hc hb

/-- **Audit form of the merged headline** `w_{c,S}`. -/
theorem audit_isDisjunctive_subsetWeight_logLogPow (S : ℕ → Prop) [DecidablePred S]
    (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate S cm Cm) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' n : ℕ,
      (((n.primeFactors.filter S).card
          + ∑ p ∈ n.primeFactors, (if S p then c p else 0) * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) := by
  have hrw : (∑' n : ℕ,
      (((n.primeFactors.filter S).card
          + ∑ p ∈ n.primeFactors, (if S p then c p else 0) * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) = subsetWeightLambert S c b := by
    unfold subsetWeightLambert
    refine tsum_congr fun n => ?_
    rw [weightSW_eq_cast]
    unfold weightSN omegaSN coeffOn
    rfl
  rw [hrw]
  exact SchedB.isDisjunctive_subsetWeight_logLogPow S c hc hmert hb

/-- **Audit form of the residue-class instance.**  `a` a unit mod `q`, `b ≥ 3`. -/
theorem audit_isDisjunctive_residueClass_weight_logLogPow {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (c : ℕ → ℕ) {A₀ s : ℕ}
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' n : ℕ,
      (((n.primeFactors.filter (fun p : ℕ => (p : ZMod q) = a)).card
          + ∑ p ∈ n.primeFactors,
              (if (p : ZMod q) = a then c p else 0) * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) := by
  obtain ⟨cm, Cm, hmert⟩ := MertensAP.mertensRate_residueClass ha
  exact audit_isDisjunctive_subsetWeight_logLogPow _ c hc hmert hb

/-- **Audit form of the `a`-side headline** (campaign B's terminal objective).  For a bounded
multiplier `a` whose active primes `{p : 1 ≤ a_p}` carry a Mertens rate, and any coefficient
vector with `c_p ≤ ⌊log₂ log₂ p⌋`, the real number
`∑_n (∑_{p ∣ n} a_p + ∑_{p ∣ n} c_p (v_p(n) − 1)) / bⁿ` is disjunctive in base `b ≥ 3`.

At `a = 1` this is `audit_isDisjunctive_weight_logLogPow` (at `s = 0`); at `a = 1_S` it is
`audit_isDisjunctive_subsetWeight_logLogPow`. -/
theorem audit_isDisjunctive_weightA_logLog (a c : ℕ → ℕ) {Ca : ℕ} (hCa1 : 1 ≤ Ca)
    (hCa : ∀ p, a p ≤ Ca) (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {cm Cm : ℝ}
    (hmert : MertensAP.MertensRate (fun p => 1 ≤ a p) cm Cm) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' n : ℕ,
      (((∑ p ∈ n.primeFactors, a p)
          + ∑ p ∈ n.primeFactors, c p * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) := by
  have hrw : (∑' n : ℕ,
      (((∑ p ∈ n.primeFactors, a p)
          + ∑ p ∈ n.primeFactors, c p * (n.factorization p - 1) : ℕ) : ℝ)
        / (b : ℝ) ^ n) = weightALambert b a c := by
    unfold weightALambert
    refine tsum_congr fun n => ?_
    rw [weightAW_eq_cast]
    unfold weightAN
    rfl
  rw [hrw]
  exact SchedB.isDisjunctive_weightA_logLog a c hCa1 hCa hc hmert hb

end NormalNumbers.G4
