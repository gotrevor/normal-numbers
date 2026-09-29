import NormalNumbers.JointLambertDisjunctivity
import ErdosProblems.Erdos446.PrimeDyadic

/-!
# `PrimeIntervalSupply` is a theorem

The second analytic input of the joint-Lambert headline,
`NormalNumbers.JointLambert.PrimeIntervalSupply`, asks for
`L / (3 log L) ≤ #{p prime : L < p < 2L}` once `L` is large.  This is an ordinary
prime-number-theorem consequence — *not* PNT in arithmetic progressions — and the
installed dependency already has it in half-open form:

* `Erdos446.eventually_dyadicPrimes_card_bounds`
  (`.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos446/PrimeDyadic.lean`),
  proved from `BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent`,
  the real PNT.  Both are `#print axioms`-clean (`propext`, `Classical.choice`,
  `Quot.sound` only).

Two gaps to close, both bookkeeping:

1. **Half-open → open.**  `Erdos446.dyadicPrimes L` is the primes in `(L, 2L]`.
   For `2 ≤ L` the right endpoint `2L` is even and `> 2`, hence composite, so the
   two Finsets are *equal* — an `ext`, not an estimate.
2. **Constant `1/2 → 1/3`.**  Free once `log L ≥ 0`, i.e. `L ≥ 1`.

The two headline corollaries then follow from the frozen conditional theorems by
discharging `hpis`, leaving `AGP` as the single remaining analytic input.  See
`docs/JOINT-LAMBERT-AGP-GAP.md` for what is actually available towards `AGP`.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- For `2 ≤ L` the endpoint `2 * L` is composite, so the primes of the half-open
dyadic interval `(L, 2L]` are exactly the primes of the open interval `(L, 2L)`. -/
theorem dyadicPrimes_eq_filter_Ioo {L : ℕ} (hL : 2 ≤ L) :
    Erdos446.dyadicPrimes L = (Finset.Ioo L (2 * L)).filter Nat.Prime := by
  ext p
  rw [Erdos446.mem_dyadicPrimes, Finset.mem_filter, Finset.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso
      have h2p : (2 : ℕ) ∣ p := ⟨L, by omega⟩
      have := (Nat.Prime.eq_one_or_self_of_dvd h3 2 h2p)
      omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, le_of_lt h2, h3⟩

/-- **`PrimeIntervalSupply` is a theorem**, from the prime number theorem as packaged
in `Erdos446.eventually_dyadicPrimes_card_bounds`.  No new assumption. -/
theorem primeIntervalSupply_holds : PrimeIntervalSupply := by
  obtain ⟨L1, hL1⟩ := Filter.eventually_atTop.1 Erdos446.eventually_dyadicPrimes_card_bounds
  refine ⟨max L1 2, fun L hL hL2 => ?_⟩
  have hLL1 : L1 ≤ L := le_trans (le_max_left _ _) hL
  obtain ⟨hlow, -⟩ := hL1 L hLL1
  rw [dyadicPrimes_eq_filter_Ioo hL2] at hlow
  have hlog : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hL2)
  have hLpos : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hratio : 0 ≤ (L : ℝ) / Real.log (L : ℝ) := by positivity
  have : (L : ℝ) / (3 * Real.log (L : ℝ)) = (1 / 3 : ℝ) * ((L : ℝ) / Real.log (L : ℝ)) := by
    rw [div_mul_eq_div_div_swap]; ring
  rw [this]
  linarith

/-- The frozen headline `JointLambertDisjunctivity`, now conditional on `AGP` **alone**. -/
theorem jointLambertDisjunctivity_of_agp (hagp : AGP) : JointLambertDisjunctivity :=
  jointLambertDisjunctivity hagp primeIntervalSupply_holds

/-- The dependent-base instance `{2, 4}`, conditional on `AGP` alone. -/
theorem jointWords_two_four_of_agp (hagp : AGP) : JointWords ({2, 4} : Finset ℕ) :=
  jointWords_two_four hagp primeIntervalSupply_holds

/-! ### Reproducible exact-type audit

These `example`s are compiler-enforced: each states the *frozen* headline type and
supplies the new theorem, so a drift in either the statement or the theorem breaks
the build.  The axiom side of the audit is `scripts/check-joint-lambert-inputs.sh`. -/

section Audit

example : PrimeIntervalSupply := primeIntervalSupply_holds
example : AGP → JointLambertDisjunctivity := jointLambertDisjunctivity_of_agp
example : AGP → JointWords ({2, 4} : Finset ℕ) := jointWords_two_four_of_agp

end Audit

end NormalNumbers.JointLambert
