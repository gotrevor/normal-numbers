# Next lap: forge new math (operator note, 2026-08-29 evening) 🔨🧭

**Written at Trevor's direction on wrap: the lane-2 backlog is CLEARED (batches 1–2 all
landed, `## RESULT` in the two 2026-08-29 briefs) — the next lap leans into FORGING REAL
NEW MATHEMATICS, not grinding formalizations.**  DIRECTION.md's conjecture-graph objective
is the frame: weigh every move by its probability of producing new mathematics.

## State that changes the board (all trust-triple, host-verified 2026-08-29)

- Tier-1 is proved IN-HOUSE: `lnTwoExpSep_sharp` (β=9) ⇒ `lnTwoRun_le_unconditional_sharp`
  — **every binary run of ln 2 capped at 9n, hypothesis-free**.
- The Fermat-quotient bridge is a THEOREM (`lnTwoNum_modEq_fermatQuotient`), no longer a
  provenance note: the R3 door's arithmetic handle is machine-checked.
- The signed-kick machine exists (`PiSqBBP.lean`): boundary forcing now covers signed-BBP
  constants (π² live, quadratically-thin windows).

## Ranked suggestions (novelty-weighted)

1. **The Wieferich-coincidence forcing theorem (R3 assembly — best value per lap).**
   All pieces are landed theorems: unique-candidate certificate (`zeroRun_res_eq_ceil` /
   `oneRun_res_eq_ceil_sub_one`), the bridge, `occursAt_replicate_suffix`, Bertrand
   covering.  One wiring theorem away: *a super-threshold run at `p−1` forces
   `q_p(2) ≡ (specific computable residue) (mod p)`* — a forcing-level statement with no
   counterpart in the 2026-08-29 lit sweep.  Then its contrapositive rung: any per-p
   exclusion of that one residue value caps runs at p−1 — a NEW conditional node strictly
   weaker than `LnTwoPrimeRunBound`, i.e. a genuine weakening-lattice advance.  Probe
   idea first: compute the forced residue for many p and check it against actual q_p(2)
   (they should essentially never coincide — quantify).
2. **The shared Diophantine-wall interface (joint with collatz-moonshot).**  The alien
   named "sliver/kick is Diophantine-free" as the weakest joint; today's vendoring proved
   the two repos literally run one Legendre engine.  Freeze ONE separation-interface node
   family both repos consume; refactor `sep_two_three`-family and `LnTwoExpSep` as its
   instances.  Architecture-level novelty; makes the wall a first-class object instead of
   an assumption.
3. **Discrepancy socket / quantitative Wall** (alien second tier): the strategically
   correct interface rung; pair any new rung with work on a dischargeable node (the
   standing anti-rung-minting ratio).

## Explicitly de-prioritized

- More kicked-machine constant instances (log²2, π² demonstrated — further instances are
  stamp-collecting, zero new-math weight).
- The ride-profile node as a campaign (alien: same wall, different graffiti — probe only).
- `piSqBBP_proved` (`PiSqBBPProof.lean`, stub still `sorry`): the last lane-2 item,
  dilogarithm-heavy, batch-3 lap was stopped mid-flight at wrap.  Fine as opportunistic
  lane-2 later; do NOT let it lead a lap.
