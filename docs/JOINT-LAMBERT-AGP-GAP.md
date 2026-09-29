# The AGP gap for joint Lambert disjunctivity — what is actually installed

**Date** 2026-09-28 (lap 7, bounded joint-Lambert campaign) · **HEAD at writing** `3ddc0b6`

After `3ddc0b6` the joint Erdős–Borwein headline rests on **exactly one** analytic
hypothesis.  `PrimeIntervalSupply` is a theorem
(`src/NormalNumbers/JointLambertPrimeInputs.lean`, `primeIntervalSupply_holds`), so

    jointLambertDisjunctivity_of_agp : AGP → JointLambertDisjunctivity
    jointWords_two_four_of_agp       : AGP → JointWords {2,4}

This document audits `AGP` against the **actual installed dependency versions**
(`.lake/packages/…` at the pins in `lakefile.toml` / `lake-manifest.json`), not against
the read-only working checkouts `~/src/lean-proofs` and `~/src/FormalPantheon`, whose
revisions differ (the host's `relake plan` skipped for exactly that reason).

---

## 1. The target, with its quantifiers

`src/NormalNumbers/JointLambertPrimeSelection.lean:64`:

```lean
def AGP : Prop :=
  ∃ X0 D0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    ∃ Dset : Finset ℕ, Dset.card ≤ D0 ∧ (∀ D ∈ Dset, Real.log X < D) ∧
      ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) →
        Nat.Coprime u B → (∀ D ∈ Dset, ¬ D ∣ B) →
        (X : ℝ) / (2 * B.totient * Real.log X) ≤
          (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ)
```

Faithfulness against the source prose (AGP 1994 Thm 2.1, in the form of Vandehey
Prop. 2.1; restated in `papers/2026-09-26-joint-lambert-disjunctivity.md` §3) — the four
quantifier facts that matter:

| feature | in the prose | in our `AGP` |
| --- | --- | --- |
| `X0, D0` | absolute constants | `∃ X0 D0`, outermost |
| exceptional set | `D(X)`, depends on `X` only | `Dset` bound **before** `∀ B u` ✅ |
| size of exceptions | each `> log X` | `∀ D ∈ Dset, Real.log X < D` ✅ |
| modulus range | `B ≤ X^{1/4}` | `(B:ℝ) ≤ X^(1/4)` ✅ |
| conclusion | `π(X;B,u) ≥ X/(2φ(B) log X)` | ditto, `π` as a `range (X+1)` filter card ✅ |

The choice order is the whole point: `Dset` is chosen before `B`, so the downstream CRT
construction may pick `B` avoiding `Dset`.  No reordering, no `∀ B ∃ Dset` weakening.

---

## 2. What is PROVED in the installed tree

**Audit status of this section.**  §2a was verified in-kernel at the installed pins:
`#print axioms` on both declarations gives `[propext, Classical.choice, Quot.sound]` only, and
they are now *consumed* by a committed theorem (`3ddc0b6`), so the full `lake build` gates them.
**§2b is now also confirmed in-kernel** (lap 7, second commit): `Erdos4.FGKMT.exists_exponential_prime_distribution`
gives `[propext, Classical.choice, Quot.sound]`, and it is consumed by
`NormalNumbers.JointLambert.exists_pointwise_exponential_distribution`
(`src/NormalNumbers/JointLambertAGPRange.lean`), which is `sorry`-free with the same axiom set —
so the repo's own build now gates it.  §2c–§2d are read off the installed **sources** (paths and
line numbers below) and are `sorry`-free by `grep` in their own files, but their transitive axiom
sets were **not** confirmed in-kernel this lap: `#print axioms` on them needs `Util.Linnik.Theorem` and the `Erdos4`/`Erdos48` analytic
trees built, and those wide cold builds kept hitting the box's `EMFILE`/"too many open files"
ceiling (errno 24, rotating target names — the known spurious-build failure, not an elaboration
error).  Treat §2c–§2d as *stated-and-sourced*, and re-run `probes/AgpAudit.lean` before relying
on them.  Nothing in §4–§6 depends on their axiom cleanliness: the obstruction argued there is
that these statements, even taken at face value, have the wrong *shape*.

### 2a. Ordinary PNT — proved, and now consumed

* `BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent`
  (`.lake/packages/BoundedGaps/…/PrimeNumberTheorem/Analytic/PrimeCounting.lean`)
* `Erdos446.eventually_dyadicPrimes_card_bounds`
  (`.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos446/PrimeDyadic.lean`)

This is what `primeIntervalSupply_holds` uses.  **Correction to the old `STATUS.md` row:**
interval supply is an *ordinary* PNT consequence.  It is **not** PNT in arithmetic
progressions, and the two frozen hypotheses were never of equal strength.

### 2b. Averaged prime discrepancy after conductor excision — proved

`Erdos4.FGKMT.exists_exponential_prime_distribution`
(`…/ErdosProblems/Erdos4/FGKMTPrimeDistribution.lean:97`):

```lean
∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
  ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
    B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
      excisedPrimeSum x (powerDistributionLevel x) B ≤
        C * (x * Real.exp (-(a/2) * Real.sqrt (Real.log x)))
```

unwinding the definitions (`…/Erdos4/FGKMTPrimeDistribution.lean:12`,
`…/Erdos4/FGKMTDistributionCutoffs.lean:9`, and
`.lake/packages/BoundedGaps/…/BombieriVinogradov/Statement.lean:36-57` for
`maxProgressionDiscrepancy`) to:

> `∑_{q ≤ x^{1/3}, (q,B)=1} max_{y ≤ x} max_{(a,q)=1} |π(y;q,a) − π(y)/φ(q)| ≤ C x e^{−(a/2)√log x}`
> for one excised conductor `B ≤ exp(a √log x)` which is `1` or prime.

That is strictly stronger than Bombieri–Vinogradov in the error factor and, crucially,
already has **the AGP exceptional-set shape**: a bounded (here: one) excised conductor
chosen before the modulus.

### 2c. Page's theorem with a conductor-size gap — proved

* `Erdos48.exists_pageBand_excludedConductor_with_selection`
  (`…/ErdosProblems/Erdos48/PageExcludedConductor.lean:51`) — one common conductor `m₀ ≤ Q`
  carries all primitive real zeros of the narrow Page window, canonically selected.
* `Erdos48.PageExceptionalWitness.log_scale_lt_quadraticGapDenom`
  (`…/Erdos48/PowerSieveExceptionalRetarget.lean:138`):
  `Real.log Q < c * (2^22 * √m * (log m)^4)`, i.e. **`m ≫ (log Q)^{2−ε}`** for a Page
  exceptional conductor at scale `Q`.
* `Erdos48.eventually_pageExceptionalWitness_modulus_ge` (ibid.:167) — the weaker
  "`m → ∞`" projection.

### 2d. Linnik's theorem — proved

`Util.Linnik.exists_eventual_polynomial_prime_bound`
(`…/Util/Linnik/Theorem.lean:39`): `∃ L ≥ 1`, eventually every `n` has a prime
`p ≡ 1 (mod n)` with `p ≤ n^L`.  The supporting `Util/Linnik/` tree (log-free moment
bounds, Deuring–Heilbronn repulsion, `ZeroRepulsion`, `HighZeroMoment`,
`MomentDecay`) is the closest installed machinery to what AGP needs.

---

## 3. What is merely STATED

* **Bombieri–Vinogradov.** `BoundedGaps.Maynard.bombieriVinogradov` and
  `hasPrimeLevel` are `def`s only
  (`.lake/packages/BoundedGaps/…/BombieriVinogradov/Statement.lean:66,76`); the
  `Challenge.lean` in the same directory carries **3 `sorry`s** and no file in that
  directory proves `bombieriVinogradov`.  It is a contract, not a theorem.
* **AGP itself.** `grep` over `~/src/lean-proofs` and `~/src/FormalPantheon` finds **no**
  declaration of AGP shape — so there is no renamed copy to mistake for progress, and
  none is manufactured here.
* `src/NormalNumbers/ElliottPrimeDensityAP.lean` (`exists_primeDensityAP`) is a theorem,
  but of the wrong shape: **fixed finite modulus, reciprocal-prime mass**
  (`∑_{p ≡ a (q), p ≤ X} 1/p`), quantified `∀ A : ℕ` over a *fixed* `q ≤ A`.  AGP needs a
  **count** for a **modulus moving with `X` up to `X^{1/4}`**.  Not a lead.

---

## 4. The actual obstruction — and why averaging cannot be patched

Take §2b at a single modulus.  The `excisedPrimeSum` terms are non-negative, so for one
`B' ≤ x^{1/3}` coprime to the excised conductor,

    max_{(u,B')=1} |π(x;B',u) − π(x)/φ(B')| ≤ C x e^{−(a/2)√log x}.       (★)

Combine (★) with PNT `π(x) ≥ (9/10) x/log x` (§2a).  AGP's conclusion needs

    π(x)/φ(B') − C x e^{−c√log x} ≥ x / (2 φ(B') log x),

for which it suffices that `0.4 x/(φ(B') log x) ≥ C x e^{−c√log x}`, i.e.

    **φ(B') ≲ e^{c√log x} / (2.5 C log x).**                              (†)

So (★) yields the AGP conclusion **only for moduli up to `exp(c√log x)`** — the
Siegel–Walfisz range.  `AGP` asks for `B ≤ X^{1/4}`, where `φ(B)` may be `≍ X^{1/4}`,
astronomically larger than any `e^{c√log X}`.

This failure is **structural, not a constant loss**: (★) is an *absolute* error bound,
while AGP is a *relative* lower bound, and the main term `π(x)/φ(B)` shrinks with `B`.
An absolute error `E(x)` independent of the modulus can never dominate a main term of
size `x/(φ(B) log x)` once `φ(B) ≥ x/(E(x) log x)`.  Improving the error factor from
`e^{−c√log x}` (§2b) to any `x/(\log x)^A` (Bombieri–Vinogradov, §3) makes this *worse*:
the admissible range in (†) collapses from `exp(c√log x)` to `(log x)^{A−1}`.

**Averaged absolute error is therefore not an adequate relative-error lower bound for
every modulus, at any constant.**  Nothing installed closes the range gap.

A **second gap, sharper than it first appears** (traced to its root lap 7, second half).
`AGP` requires every `D ∈ Dset` to exceed `log X`, while §2b's excised conductor carries only
`B ≤ exp(a√log x)` and `B = 1 ∨ B.Prime`.  My first reading blamed the `Erdos4` chain for
projecting away `Erdos48`'s Page witness, so that the installed bound `m ≫ (log Q)^{2−ε}` could
not be read off.  **That reading was wrong, and the truth is worse.**  Following the chain

    exists_landauPage_unique → exists_prime_excision_of_unique → exists_uniform_prime_excision
    → exists_uniform_twisted_sum → exists_uniform_primitive_maximum
    → exists_excised_distribution_envelope → exists_exponential_centered_distribution
    → exists_exponential_prime_distribution

to its root, `…/ErdosProblems/Erdos4/FGKMTPrimeExcision.lean:8` excises

    B := (χ.modulus).minFac,

the **smallest prime factor** of the exceptional conductor, with the exclusion stated as
coprimality `d.Coprime B`.  No lower bound on `B` exists even in principle: the exceptional
conductor `m` can be large while `minFac m = 2`, and then `B = 2 ≤ log X` for every `X ≥ 3`.
Re-threading a Landau–Siegel bound on `m` does not help, because `m` is not what is excised.

**The repair is structural, and it is now proved sound in-kernel.**
`NormalNumbers.JointLambert.exists_modulus_excision_of_unique` and
`exists_uniform_modulus_excision` (`src/NormalNumbers/JointLambertAGPRange.lean`, axiom-clean)
excise `m` **itself**, with the exclusion expressed as **divisibility** `¬ D ∣ d` — which is
`AGP`'s own form, and the mathematically right one: a character mod `d` is induced by a primitive
character whose conductor divides `d`, so an exceptional primitive character of conductor `m` can
only pollute **multiples** of `m`.  Coprimality to `minFac m` is strictly cruder than the
mathematics requires.  With `m` as the excised value, `D > log X` becomes a genuine
Landau–Siegel statement about the conductor, which §2c's ingredients address.

The cost of the repair, stated plainly: `¬ m ∣ d` does **not** imply `d.Coprime (minFac m)`, so
the new excision cannot be fed to the existing chain.  Consuming it means re-deriving
`exists_uniform_twisted_sum` … `exists_exponential_prime_distribution` with divisibility-based
excision — five substantial upstream theorems, in a dependency this campaign does not modify.
So this is **not** the "adapter work, not new mathematics" it was first called.

---

## 5. What suffices as an adapter, and what does not

| piece | status |
| --- | --- |
| open vs half-open dyadic interval, `1/2 → 1/3` constant | ✅ adapter, **done** (`3ddc0b6`) |
| single-modulus extraction from `excisedPrimeSum` (★) | adapter (`Finset.single_le_sum`) |
| `π(x) ≥ (9/10) x/log x` | ✅ installed (§2a) |
| AGP-shaped (divisibility) excision is sound | ✅ **proved lap 7** (`exists_uniform_modulus_excision`) |
| exceptional conductor `> log X` | ❌ not an adapter: the installed chain excises `minFac m`, which has no lower bound; needs the chain re-derived with divisibility excision, plus a Landau–Siegel bound on `m` |
| **modulus range `exp(c√log X) → X^{1/4}`** | ❌ **substantial missing theorem** |

The missing theorem is a **log-free zero-density estimate** for Dirichlet `L`-functions
in the Linnik/Gallagher style — the input that lets `x^{θ}`-size moduli keep a *relative*
main term after a bounded exceptional set is removed.  AGP 1994 §2 obtains Thm 2.1 from
such a density result rather than from any averaged discrepancy bound.  (I have the
statement locally, in the paper draft's §3; I have **not** read AGP's §2 on this box, so
the precise source lemma attribution is unverified here — the mathematical necessity of a
density-type input, argued in §4, does not depend on it.)  This is a multi-lap analytic
campaign and is **out of scope** for this bounded run.

---

## 6. ONE concrete next proof target

Not a renamed `AGP`.  A strictly weaker, **fully quantified** proposition that the
installed tree plausibly already proves, and which factors `AGP` into a proved half and a
single named range extension:

```lean
/-- AGP verbatim, with the modulus range `X^{1/4}` replaced by the
Siegel–Walfisz range `exp (c * √log X)`. -/
def AGPExpRange : Prop :=
  ∃ (X0 : ℕ) (c : ℝ), 0 < c ∧ ∀ X : ℕ, X0 ≤ X →
    ∃ Dset : Finset ℕ, Dset.card ≤ 1 ∧ (∀ D ∈ Dset, Real.log X < D) ∧
      ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log X)) →
        Nat.Coprime u B → (∀ D ∈ Dset, ¬ D ∣ B) →
        (X : ℝ) / (2 * B.totient * Real.log X) ≤
          (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ)
```

**Target: `agpExpRange_holds : AGPExpRange`**, with no new hypothesis.  **Opened lap 7** in
`src/NormalNumbers/JointLambertAGPRange.lean`, which now contains `AGPExpRange` and the proved
bookkeeping layer — in particular `exists_pointwise_exponential_distribution`, the single-modulus
(★) form of the installed input, `#print axioms`-clean.  Two disclosed `sorry`s remain there:
`exceptionalConductor_gt_log` (the `D > log X` adapter of §4) and the quantitative assembly that
is blocked on it.

Why it bridges.  Every structural feature of `AGP` is present unchanged — the `X`-only
exceptional set chosen *before* `B` and `u`, `D0 = 1`, `D > log X`, the same relative
lower bound, the same `π` encoding.  The *only* difference is the modulus range.  So
proving it (a) discharges the entire choice-order and exceptional-set architecture of
`AGP` against real analytic input, (b) confirms `D0 = 1` is enough, and (c) leaves the
remaining gap as one crisp, nameable implication

    AGPExpRange  +  (log-free density: range `exp(c√log X) → X^{1/4}`)  ⟹  AGP,

which is exactly the multi-lap analytic target identified in §4 and nothing else.

Route, all from §2: `exists_exponential_prime_distribution` for (★) at one modulus
(`Finset.single_le_sum`, non-negativity of `primeDiscrepancyUpTo`);
`eventually_primeCounting_tenth_bounds` for the main term; inequality (†) with
`c := a/4` and the threshold pushed up so `2.5 C log X ≤ exp((a/4)√log X)`; and the
Page-witness re-thread of §2c for `log X < D`.  Expected cost: one lap, *if* the
`Erdos4` excision chain can be re-entered at a point that still carries the Page
witness; if it cannot, the honest outcome is `AGPExpRange` with the `D > log X` clause
weakened to `∀ D ∈ Dset, M ≤ D` for an arbitrary fixed `M` (§2c's
`eventually_pageExceptionalWitness_modulus_ge` shape), which is still a real reduction.

No normality claim, no quantitative-occurrence claim, and no change to any frozen
statement is involved in any of the above.

---

## Correction (2026-09-29): obstacles to AGP are not obstacles to the Lambert consumer

Everything above is about `AGP` itself, and stands. It does **not** establish that `AGP` is
necessary for the qualitative joint-Lambert headline, and it is not: see
`docs/JOINT-LAMBERT-RESCALED-PROOF.md`.

The detour came from two demands that the consumer never made.

1. **The search endpoint was tied to the modulus.** The old schedule fixed `X = 2^{4k⁴}` with
   `B ≤ 2^{k⁴}`, i.e. `B = X^{1/4}` — precisely the AGP range. Nothing downstream requires
   that; `X` may grow as fast in `k` as we like. At `X = 2^{4k¹²}` the same modulus sits in
   the Siegel–Walfisz range, where §2b's *proved* input already applies.
2. **A lower bound on the excised conductor was demanded.** §2/§4 above are right that the
   installed chain excises `minFac(χ.modulus)` and admits no lower bound. But
   `exists_prime_allocation` dodges any finite set of non-unit moduli at one pool prime each,
   with **no** size hypothesis, so the `D > log X` clause was never needed by the consumer.

`jointLambertDisjunctivity_unconditional` and `jointWords_two_four_unconditional` are now
theorems with no hypotheses. `AGP` and `AGPExpRange` remain open; the analysis of §4–§6 of
this document is unaffected, and is simply no longer on the headline's critical path.
