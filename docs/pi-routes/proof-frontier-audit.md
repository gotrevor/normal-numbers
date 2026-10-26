# Pi disjunctivity: proof-frontier audit, 2026-10-26

**The requested result has not been proved.**  The objective remains: exhibit an integer base b≥2 and prove `IsDisjunctive b Real.pi`, without an unproved mathematical premise or an admitted proof in its dependency chain.

This audit checked the current local branch `research/pi-routes` at mathematical-work commit `c3a5b571`.  A source search for the pi normality/disjunctivity conclusions and a fresh Lean type/axiom audit found the following frontier.  Audit source and output are in `tmp/20261026-pi-proof-frontier/Audit.lean` and `audit.txt`.

| Route | Verified declaration | Still missing |
|---|---|---|
| BBP identity | `NormalNumbers.piBBP_proved : PiBBP` | The identity itself is proved; it does not supply digit visits. |
| Odd invariance | `pi_disjunctive_iff_oddInvariant` | `PiOrbitClosureOddInvariant`; the theorem is an equivalence, not a proof of either side. |
| Quantitative return | `pi_disjunctive_of_quantitativeTripleReturn` | `PiQuantitativeTripleReturn`. |
| Prime reservoir | `pi_disjunctive_of_primeReservoirSupport` | `PiPrimeReservoirSupport`; BBP can be supplied, this support premise cannot. |
| Diagonal reservoir | `pi_disjunctive_of_reservoirDiagonalSupport` | `PiReservoirDiagonalSupport`. |
| Disk residues | `pi_disjunctive_of_diskResidueCover` | `DiskResidueCover`. |
| Bailey–Crandall | `MasterConjectures.hypA_pi_base2_uncond` | `BaileyCrandallHypA`.  Despite the suffix `uncond`, the theorem explicitly takes Hypothesis A; only the BBP assumption was discharged. |
| Denominator criterion | `CutoffSix.denominatorCouplingCriterion_iff` | An equivalent form of the target, not an independent sufficient input already available. |
| Backward BBP | `BBPBackward.backward_hasSum_zero` | Its infinite proof still uses `sorryAx`; no digit-visitation implication has been established even conditional on it. |

The transfer theorems' baseline axiom lists do not prove their hypotheses.  Their printed types are essential to interpreting their status.

## What the recent continuations actually accomplished

- `44a947af`: `BBPAdelicGrid.rational_grid_comparison` proves that finite exact BBP data, actual denominator budgets, and prescribed finite 2-adic precision admit rational-target comparisons at an explicit grid error scale.  It does not preserve the exact infinite recurrence, exact reduced denominators, or all odd-prime poles.
- `c3a5b571`: `DiskFloorError.tail_floorError_scaled_bound` derives a vanishing scaled floor-error bound from the perimeter theorem and the explicit divisor/Leibniz inputs.  It corrects a proposed research target but does not establish residue visits.
- Both commits passed the full repository build.  Fresh axiom inspection found no admitted proof in these two theorems.  Neither concludes pi disjunctivity.

These were scoped research results.  Counting them as completion, or continuing to accumulate unrelated auxiliary lemmas, would change the objective rather than solve it.

## Research impasse

The same central gap persisted through the user-triggered continuation, the disk continuation, and this audit: no available argument derives the required digit visits from pi's exact arithmetic.  The auxiliary results changed which shortcuts remain plausible, but did not provide that argument.

I do not currently have a further justified proof mechanism.  Formalizing the remaining backward logarithm calculation, running more finite digit probes, or restating one of the equivalent criteria would not resolve this gap.  This is a limitation of the present investigation, not a theorem that the problem or these routes are impossible.

Resuming substantive proof work needs a new mathematical input or a concrete mechanism for one of the remaining premises.  Such an input must be assessed on its own mathematical content and on the existing comparison examples; simply naming a premise or observing more digits does not establish it.  Nothing has been pushed or merged into the main checkout by this continuation.
