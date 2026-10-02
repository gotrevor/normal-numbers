/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureTTEquidistributed
import NormalNumbers.LiteratureTTEquidistributedDefect
import NormalNumbers.G4VeryLargeCov
import NormalNumbers.G4SubsetWitnessCov
import NormalNumbers.G4Base2Cov

/-!
# Erdős #257 at base 2 for prime subsets (campaign launched 2026-10-02)

The base-`≥ 3` theorem `G4.isDisjunctive_subsetLambert` fails at `b = 2` exactly at the
very-large-prime step: the frame bounds the primes above `Y` pointwise, and `rowL1 2 K = 1`
(`rowL1_two`, `one_le_rowMass_two`).  Tao–Teräväinen's irrationality of `Σ ω(n)/2ⁿ` needs the same
input and get it from a two-point correlation estimate, their Theorem 3.1(i), applied to "avoids
every prime in bin `ℓ`" indicators.  Those stay equidistributed when the bins are cut down to
`S`-primes, so the route transfers to `ω_S`, with a Mertens rate replacing their variance lower
bound.

Audit and route: `docs/ERDOS257-BASE2-SUBSET-AUDIT-2026-10-02.md` (§4, lemmas N1-N8; the
mathematics closes 75%, reachable in days 50%).  Interface first: `VeryLargeCov` replaces the
pointwise bound by a second-moment one (N1 `blockSum_sq_le_of_cov`, N2
`gridFrameW_subset_propD_of_cov`).

## Frozen statements (do not edit; prove them)

* `isDisjunctive_subsetLambert_two`, conditional on `CastingOut.TTEquidistributedDyadic` only
  (re-frozen 2026-10-02 by the operator: the first transcription,
  `TTEquidistributedCorrelation`, is vacuous, `ttEquidistributedCorrelation_trivially_true`).
* `erdos257_primeSubset`: Erdős #257 for `A = S` itself, any prime set with a Mertens rate.
* `erdos257_residueClass`: the residue-class instance.

## Guard rule

**Content locator.**  `S` = all primes, irrationality only, is Tao–Teräväinen's theorem; the new
content is disjunctivity (stronger than irrationality, new even for all primes) and proper prime
subsets.  **Degenerate cases.**  A finite `S` gives a rational constant and fails the Mertens rate;
`b ≥ 3` is the existing theorem, so the case split at `b = 2` is where the content is.
-/

namespace NormalNumbers.Erdos257

open G4

variable {S : ℕ → Prop} [DecidablePred S]

/-- **The very-large covariance supply near the `SchedB` scales** (`Y = 2^{2^{mE}}`, and a
power-of-two `X = 2^x` with `100·2^{mE} ≤ x ≤ 101·2^{mE}`, so `Y^{100} ≤ X ≤ Y^{101}`): for every
grid of the schedule family, `κ` can be made arbitrarily small by taking the cutoff exponent `e`
large, with the fixed variance budget `V = 20000` (`ω_{S,>Y}(m) ≤ 102` for `m ≤ Mx`).

**Why `X` is chosen, not fixed** (found 2026-10-02 lap 3): TT's dyadic conclusion may fail on a
fraction `Cst·L^{-c}` of scales, which can include the top block `(X/2, X]` carrying half the
sample.  So `X` must be picked among `≈ 2^{mE}` candidate powers of two whose top `J₀` blocks are
all good scales; a union bound over the `B²` bin pairs leaves one. -/
def VeryLargeCovSupply (S : ℕ → Prop) [DecidablePred S] : Prop :=
  ∀ K N : ℕ, ∀ hK : 1 ≤ K, ∀ κ : ℝ, 0 < κ → ∃ e₀ : ℕ, ∀ e, e₀ ≤ e →
    ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
      VeryLargeCov S (gridOf K N hK) (2 ^ x) (SchedB.YE K e) 20000 κ

/-- **N3–N6: the covariance supply from Tao–Teräväinen 3.1(i)** (dyadic form).  Route: bins of
`S ∩ (Y, Mx]` of harmonic mass `≤ 1/B` (N3), `ω_{S,>Y} = Σ_ℓ (1 − g_ℓ) + err` (N4), TT's
hypothesis (3.1) for the bin indicators `g_ℓ` via the rough-number count (N5), and averaging the
dyadic-block conclusion over `[0, X)` with the bad scales charged pointwise (N6).
`κ ≪ B²·(log X)^{-c} + A/B`, so `κ → 0` as `e → ∞` with `B` chosen late.  No Mertens rate is
needed.  75% (audit §4). -/
theorem veryLargeCovSupply_of_TT (htt : CastingOut.TTEquidistributedDyadic) :
    VeryLargeCovSupply S := by
  sorry

/-- **N7: the base-2 schedule.**  A Mertens rate and the covariance supply give a schedule
witness for every omitted dyadic cylinder.  At `bb = 2`, `rowL1 = 1`, `rowL2 = 2^{-K}/3`, so the
very-large term needs `κ ≤ 2^{-K/2}/(256 K²)`, which the supply provides; the remaining fields
are the `b ≥ 3` schedule (`SchedB.scheduleWitnessSE`) redone at `b = 2`.  70%. -/
theorem exists_scheduleWitnessSC_two_of_supply (hsup : VeryLargeCovSupply S)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSC S 2 ℓ w) := by
  sorry

/-- **N6 + N7: the base-2 schedule witness with the covariance interface.** -/
theorem exists_scheduleWitnessSC_two (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSC S 2 ℓ w) :=
  exists_scheduleWitnessSC_two_of_supply (veryLargeCovSupply_of_TT htt) hm ℓ w hℓ

/-- **Base-2 disjunctivity of `Σ_{p∈S} 1/(2ᵖ − 1)`** for any prime set with a Mertens rate,
conditional on Tao–Teräväinen Theorem 3.1(i).  75% (audit). -/
theorem isDisjunctive_subsetLambert_two (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) :
    IsDisjunctive 2 (PrimeLambert.subsetLambert S 2) := by
  refine isDisjunctive_subsetLambert_of_witnessC S 2 le_rfl fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico 2 (PrimeLambert.subsetLambert S 2) 0)
  · exact exists_scheduleWitnessSC_two htt hm ℓ w hℓ

/-- **Erdős #257 for a prime set `A = S`** with a Mertens rate. -/
theorem erdos257_primeSubset (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) :
    Irrational (∑' n : kMulPrimes S 1, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [← subsetLambert_two_pow_eq le_rfl, pow_one]
  exact IsDisjunctive.irrational (isDisjunctive_subsetLambert_two htt hm)

/-- **Erdős #257 for the primes `≡ a (mod q)`.** -/
theorem erdos257_residueClass (htt : CastingOut.TTEquidistributedDyadic)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Irrational (∑' n : kMulPrimes (fun p => (p : ZMod q) = a) 1, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  obtain ⟨c, C, hm⟩ := MertensAP.mertensRate_residueClass ha
  exact erdos257_primeSubset htt hm

end NormalNumbers.Erdos257
