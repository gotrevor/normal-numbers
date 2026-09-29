# KICKOFF 2026-09-28 — joint-Lambert prime inputs + AGP gap map (bounded, ≤ 2 laps)

Saved verbatim-in-substance from the operator instruction, for the record.  Trevor's
authorization: "Go for it! It's an interesting claim."  **Not** a Vandehey assembly campaign.

- **Baseline** `7b17c447520411f85e2c5ad5ef7ee35e04002c59`, tree clean, no treadmill running.
- **Cap** at most TWO laps, Opus/low.
- **Gate discharged.** `DIRECTION.md`'s lap-4 rule "do not open `PrimeIntervalSupply` until
  `hjs` is a theorem" is satisfied by lap 6's `VandeheyTransport.jointStateFreq_lrDelta` and
  `VandeheyTransportB.jointStateFreq_lrB`.  Recorded as a dated scoped section in
  `DIRECTION.md` (objective 2026-09-28 (c)); Vandehey's queue and history preserved, and no
  Vandehey implementation touched.

## Deliverable 1 — exact headline types, no extra assumptions

New `src/NormalNumbers/JointLambertPrimeInputs.lean`, namespace `NormalNumbers.JointLambert`:

    theorem primeIntervalSupply_holds : PrimeIntervalSupply
    theorem jointLambertDisjunctivity_of_agp (hagp : AGP) : JointLambertDisjunctivity
    theorem jointWords_two_four_of_agp (hagp : AGP) : JointWords ({2,4} : Finset ℕ)

Existing `JointLambert*.lean` FROZEN byte-identical to baseline; new file + root import only.
`AGP`, `PrimeIntervalSupply`, `JointWords`, `JointLambertDisjunctivity` must not change.
The existing conditional theorems supply the corollaries.

Source: the installed `.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos446/PrimeDyadic.lean`
`Erdos446.eventually_dyadicPrimes_card_bounds`; for `L ≥ 2`, `2L` is composite, so equality with
`(Ioo L (2*L)).filter Nat.Prime` via `Erdos446.mem_dyadicPrimes`; weaken `1/2 → 1/3` with
`log L ≥ 0`.  Check axioms before use; fall back to `PrimeNumberTheoremAnd/Consequences.lean`
`pi_alt'` if it rests on unproved inputs.  No new axioms, no PNT-as-hypothesis, no pin changes,
no vendoring.

## Deliverable 2 — required before declaring done

`docs/JOINT-LAMBERT-AGP-GAP.md`: audit the **locally installed** analytic statements against the
frozen `AGP` — file paths, exact declaration names, quantifier comparison.  Distinguish installed
pins from the read-only `~/src/lean-proofs` and `~/src/FormalPantheon` checkouts.  Say precisely
what is proved, what is merely stated, what adapters suffice, what substantial analytic theorem is
missing.  Averaged absolute error is not an adequate relative-error lower bound for every modulus.
Name ONE concrete next proof target with quantifiers and the bridge argument; no renamed copy of
`AGP` as "progress"; no multi-lap analytic campaign; no normality or quantitative-occurrence claims.
Leads checked: `Erdos4/FGKMTPrimeDistribution.lean`, `Erdos48/PageExcludedConductor.lean`,
`Erdos48/PowerSieveExceptionalRetarget.lean`, `Util/Linnik`, installed `BoundedGaps`, and
`NormalNumbers/ElliottPrimeDensityAP.lean` (wrong shape: fixed finite modulus, reciprocal mass).

## Validation

Add the module to `src/NormalNumbers.lean`; scoped Lean check; exact headline type checks;
`#print axioms` on the new targets; frozen-file diff vs baseline; then one full `lake build` and a
green commit.  Keep the declaration checks reproducible in-repo, not just asserted in prose.
Preserve prior handoffs; update `HANDOFF-joint-lambert.md`, `STATUS.md`, `PENDING_WORK.md`.
Correct the misleading `STATUS.md` row claiming both hypotheses are PNT-in-AP strength: interval
supply needs ordinary PNT.  Mark this bounded objective complete when done, preserving other
directives.  Do not work unrelated pre-existing holes to satisfy a global sorry gate.

**Completion** = all three exact theorems with no new mathematical assumption beyond `hagp`,
the AGP gap document, frozen statements intact, build green.  A truthful specific obstruction
counts as progress if the exact target cannot be proved within the cap.

## Outcome (lap 7, 2026-09-28)

Both deliverables met.  `3ddc0b6` has all three theorems at the exact frozen types,
`#print axioms`-clean, frozen files byte-identical, full `lake build` green (10352 jobs).
`docs/JOINT-LAMBERT-AGP-GAP.md` written; next target named as `AGPExpRange`.
