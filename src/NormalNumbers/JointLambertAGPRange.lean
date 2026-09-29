/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertPrimeInputs
import ErdosProblems.Erdos4.FGKMTWeightedDistribution
import ErdosProblems.Erdos446.PrimeDyadic

/-!
# `AGPExpRange` — AGP on the Siegel–Walfisz modulus range

`docs/JOINT-LAMBERT-AGP-GAP.md` §6 names this as the one concrete next target on the
joint-Lambert front.  It is `AGP` **verbatim** — same `X`-only exceptional set, chosen
*before* the modulus `B` and residue `u`; same `D > log X` clause; same relative lower
bound `X/(2 φ(B) log X)`; same `π` encoding as a `range (X+1)` filter card — with the
single change that the modulus range `B ≤ X^{1/4}` is cut down to `B ≤ exp (c √log X)`.

Why this statement and not another.  §4 of the gap document shows that the strongest
installed analytic input,

  `Erdos4.FGKMT.exists_exponential_prime_distribution`,

bounds an **absolute** prime discrepancy by `C · x · exp(−(a/2)√log x)`, while `AGP` is a
**relative** lower bound whose main term `x / (φ(B) log x)` shrinks with `B`.  An absolute
error independent of the modulus can never dominate that main term once
`φ(B) ≥ x / (E(x) log x)`; so the installed material reaches exactly the Siegel–Walfisz
range and no further, and improving the error factor makes the range *worse*.  Proving
`AGPExpRange` therefore discharges the whole *architecture* of `AGP` — the bounded,
`X`-only, chosen-first exceptional set with `D0 = 1` — against real analytic input, and
reduces the remaining gap to the single named implication

  `AGPExpRange` + (log-free zero-density: range `exp(c√log X) → X^{1/4}`) ⟹ `AGP`.

That density estimate is the substantial missing theorem, a multi-lap analytic campaign,
and is deliberately **not** attempted here.

## Status

The bookkeeping layer (§1 below) is proved: the `AGP`/`BoundedGaps` prime-count encodings
are literally the same function, and a single modulus can be extracted from the excised
sum.  The assembly (§2) carries two disclosed `sorry`s, both named and both discussed in
the gap document:

* `exceptionalConductor_gt_log` — the `D > log X` clause.  The needed conductor bound is
  installed (`Erdos48.PageExceptionalWitness.log_scale_lt_quadraticGapDenom` gives
  `m ≫ (log Q)^{2−ε}`), but the `Erdos4` excision chain
  (`exists_excised_distribution_envelope → exists_exponential_centered_distribution →
  exists_exponential_prime_distribution`) *discards* the Page witness, so the bound cannot
  be read off the statement we consume.  Adapter work, not new mathematics.
* `agpExpRange_holds` — the quantitative assembly, blocked only on the above.

`AGP` itself is untouched and stays frozen.
-/

namespace NormalNumbers.JointLambert

open Finset Filter BoundedGaps.Maynard

/-- **`AGP` on the Siegel–Walfisz modulus range.**  Identical to `AGP` except that
`(B : ℝ) ≤ X ^ (1/4)` is replaced by `(B : ℝ) ≤ exp (c * √(log X))`, and `D0` is pinned
to `1` (one excised conductor is what the installed analytic input supplies). -/
def AGPExpRange : Prop :=
  ∃ (X0 : ℕ) (c : ℝ), 0 < c ∧ ∀ X : ℕ, X0 ≤ X →
    ∃ Dset : Finset ℕ, Dset.card ≤ 1 ∧ (∀ D ∈ Dset, Real.log X < D) ∧
      ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log X)) →
        Nat.Coprime u B → (∀ D ∈ Dset, ¬ D ∣ B) →
        (X : ℝ) / (2 * B.totient * Real.log X) ≤
          (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ)

/-! ### 1. The encodings agree, and one modulus can be extracted

Nothing analytic happens in this section; it is the dictionary between `AGP`'s prime count
and `BoundedGaps.Maynard`'s, plus non-negativity bookkeeping. -/

/-- `AGP`'s prime count **is** `BoundedGaps.Maynard.primeCountUpTo` at the reduced
residue `u % B`.  Not an estimate: the two filters are the same predicate. -/
theorem agpCount_eq_primeCountUpTo (X B u : ℕ) :
    (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℕ)
      = primeCountUpTo X B (u % B) := by
  unfold primeCountUpTo
  congr 1
  apply Finset.filter_congr
  intro z _
  simp [Nat.mod_mod_of_dvd u (dvd_refl B)]

/-- The reduced residue representative of a unit `u` really is one. -/
theorem mod_mem_coprimeResidues {B u : ℕ} (hB : 0 < B) (hu : Nat.Coprime u B) :
    u % B ∈ coprimeResidues B := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hB), ?_⟩
  show Nat.gcd (u % B) B = 1
  rw [← Nat.gcd_rec, Nat.gcd_comm]
  exact hu

/-- One residue's discrepancy is at most the maximum over reduced residues. -/
theorem progressionDiscrepancy_le_max {X B u : ℕ} (hB : 0 < B)
    (hu : Nat.Coprime u B) :
    progressionDiscrepancy X B (u % B) ≤ maxProgressionDiscrepancy X B := by
  rw [maxProgressionDiscrepancy, dif_pos hB]
  exact Finset.le_sup' _ (mod_mem_coprimeResidues hB hu)

/-- **Single-modulus extraction.**  The excised sum has non-negative terms, so each
individual modulus coprime to the excised conductor inherits the whole bound. -/
theorem maxDisc_le_excisedPrimeSum {x Q B q : ℕ} (hx : 2 ≤ x) (hq1 : 1 ≤ q)
    (hqQ : q ≤ Q) (hqB : q.Coprime B) :
    maxProgressionDiscrepancy x q ≤ Erdos4.FGKMT.excisedPrimeSum x Q B := by
  have hmem : q ∈ (Finset.Icc 1 Q).filter (fun r => r.Coprime B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hqQ⟩, hqB⟩
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun r => Erdos4.FGKMT.primeDiscrepancyUpTo x r)
    (fun r _ => Erdos4.FGKMT.primeDiscrepancyUpTo_nonneg x r) hmem)
  exact Erdos4.FGKMT.maxProgressionDiscrepancy_le_primeDiscrepancyUpTo hx le_rfl

/-- **The pointwise form of the installed analytic input.**  For one excised conductor and
every modulus `q` up to `x^{1/3}` coprime to it, *every* reduced residue class has prime
count within `C x exp(−(a/2)√log x)` of the expected `π(x)/φ(q)`.  This is (★) of the gap
document, and is exactly `exists_exponential_prime_distribution` read at a single term. -/
theorem exists_pointwise_exponential_distribution :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ Erdos4.FGKMT.exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
          ∀ q u : ℕ, 1 ≤ q → q ≤ Erdos4.FGKMT.powerDistributionLevel x →
            q.Coprime B → Nat.Coprime u q →
            |((primeCountUpTo x q (u % q) : ℝ)
                - (primeCountTotal x : ℝ) / (q.totient : ℝ))|
              ≤ C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨a, C, ha, ha1, hC, hdist⟩ :=
    Erdos4.FGKMT.exists_exponential_prime_distribution
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  filter_upwards [hdist, eventually_ge_atTop 2] with x hdist hx
  obtain ⟨B, hBcut, hB, hbound⟩ := hdist
  refine ⟨B, hBcut, hB, fun q u hq1 hqQ hqB hu => ?_⟩
  have hq0 : 0 < q := hq1
  calc |((primeCountUpTo x q (u % q) : ℝ) - (primeCountTotal x : ℝ) / (q.totient : ℝ))|
      = progressionDiscrepancy x q (u % q) := rfl
    _ ≤ maxProgressionDiscrepancy x q := progressionDiscrepancy_le_max hq0 hu
    _ ≤ Erdos4.FGKMT.excisedPrimeSum x (Erdos4.FGKMT.powerDistributionLevel x) B :=
        maxDisc_le_excisedPrimeSum hx hq1 hqQ hqB
    _ ≤ _ := hbound

/-! ### 2. The assembly, and the one adapter gap that blocks it -/

/-- **The `D > log X` clause — DISCLOSED GAP, adapter work.**

`AGP` (and `AGPExpRange`) require every excluded modulus to exceed `log X`.  The excised
conductor returned by `exists_exponential_prime_distribution` carries only
`B ≤ exp (a √log x)` and `B = 1 ∨ B.Prime` — no *lower* bound.  The bound that is needed
does exist in the installed tree: a Page exceptional conductor `m` at scale `Q` satisfies
`Real.log Q < c * (2^22 * √m * (log m)^4)`
(`Erdos48.PageExceptionalWitness.log_scale_lt_quadraticGapDenom`), i.e. `m ≫ (log Q)^{2−ε}`,
comfortably `> log x` at `Q ≍ x^{1/3}`.  But the `Erdos4` excision chain
(`exists_excised_distribution_envelope → exists_exponential_centered_distribution →
exists_exponential_prime_distribution`) projects the Page witness away, so the bound is not
derivable from the statement consumed above: closing this needs re-entering that chain at a
point where the witness is still present.  Adapter work, not new mathematics — but not
free, and deliberately left open rather than assumed. -/
theorem exceptionalConductor_gt_log :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
      B ≤ Erdos4.FGKMT.exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
        (B = 1 ∨ Real.log (x : ℝ) < B) := by
  sorry

/-- **`AGPExpRange` — DISCLOSED GAP, quantitative assembly.**

The plan, entirely from material already proved above and in `Erdos446.PrimeDyadic`:
take `Dset := if B = 1 then ∅ else {B}` for the excised conductor `B` of
`exists_pointwise_exponential_distribution`, so `Dset.card ≤ 1` and `¬ B ∣ q` gives
`q.Coprime B` for prime `B`.  Then for `q ≤ exp(c √log x)`:

* `primeCountUpTo x q (u % q) ≥ π(x)/φ(q) − C x e^{−(a/2)√log x}` by (★);
* `π(x) ≥ (9/10) x / log x` by `Erdos446.eventually_primeCounting_tenth_bounds`;
* so it suffices that `C x e^{−(a/2)√log x} ≤ (2/5) · x / (φ(q) log x)`, and since
  `φ(q) ≤ q ≤ exp(c √log x)` with `c := a/4`, this reduces to
  `(5/2) C log x ≤ exp((a/4) √log x)`, true for all large `x`.

Blocked only on `exceptionalConductor_gt_log`: without it `Dset` cannot be given the
`log X < D` property that `AGPExpRange` (faithfully, following `AGP`) demands.  Filling
that adapter should close this theorem too. -/
theorem agpExpRange_holds : AGPExpRange := by
  sorry

end NormalNumbers.JointLambert
