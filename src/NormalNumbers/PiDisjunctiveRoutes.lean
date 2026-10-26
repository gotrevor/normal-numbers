/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.TripleReturn
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoir
import NormalNumbers.PiDisjunctiveRoutes.DiskResidue

/-!
# Three experimental routes to disjunctivity of π

These are research statements, not established arithmetic estimates.  The three
new premises are `PiQuantitativeTripleReturn`, `PiPrimeReservoirSupport`, and
`DiskResidueCover`.  The transfer arguments below are frozen with `sorry`:
their docstrings give the mathematical argument and its evidence tier.

The first qualitative premise is EQUIVALENT to binary disjunctivity for
irrational inputs.  It is a change of target, not a weakening.  The other two
premises ask for extra joint support or a quantitative covering rate.  No
numerical evidence or claim of literature priority is asserted here.

Existing foundation: `MasterConjectures.BaileyCrandallHypA`,
`MasterConjectures.hypA_pi_base16`, `PiBBP`, and
`Furstenberg.isClosed_invariant_finite_or_univ`.  In particular the BBP
surrogate itself is not a new route; the prime/residual JOINT support is the
new premise, and must not be inferred from separate marginal distribution.

One file per route, so the routes can be worked independently:
`TripleReturn` (route 1), `PrimeReservoir` (route 2), `DiskResidue` (route 3).
-/
