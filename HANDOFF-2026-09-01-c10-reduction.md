# HANDOFF: C10 proved by reduction (tower brief fully closed) 🗼

Branch `wip/adder-tower-c9` (continuing).  Full `lake build` green (8843 jobs).
Operator instruction this session: do NOT chase the sorry-free gate, do NOT touch
the two OFF-LIMITS `CFScheduleA` sorries; grind provable leaves + the tower's named
cruxes.

## Landed this lap

1. **C10 — the last named tower claim — PROVED, kernel tier, trust triple.**
   `NormalNumbers.Adder.c10_disjunction_universal` (`src/NormalNumbers/AdderTowerC10.lean`),
   the dossier's exact nine-disjunct base-5 statement.  `#print axioms` =
   `[propext, Classical.choice, Quot.sound]`; the certificates `c10y_cert`/`c10z_cert`
   = `[propext]`.
   - **REDUCTION FINDING (C5 pattern).**  The dossier rated C10 "largest certificate,
     540 396 live states"; in our encoding the two-track automaton is 46080 ambient /
     18 live and DOES collapse (Python, 1.2 s — verdict agrees).  But the kernel proof
     needs none of it: irrational `Y` ⇒ the four `Y`-only channels collapse alone
     (`c10_y_branch`: 3 in Y ∨ 4 in 2Y ∨ 2 in 3Y ∨ 0 in 4Y; 24 ambient / 5 live);
     rational `Y` ⇒ `Z = X+Y` irrational and the diagonal channels are `Z,2Z,3Z,4Z`
     avoiding digit 2, which collapse alone (`c10_z_branch`; 24 ambient / 6 live).
     `X+4Y` is unused.  Recorded as the C10 addendum in `BRIEF-adder-tower.md`;
     the novelty audit's "credible new candidate" rating for C10 should be
     downgraded to the C5 disposition (operator-owned doc, not edited).
   - Emitter `experiments/adder_baseg_emit.py` gained `c10`, `c10y`, `c10z`
     families; certs JSON emitted under `experiments/certs/`.
2. **Aristotle faithfulness check of `PiSqBBP` PASSED** (project `7ee16d3a`): its
   prose-only formalization is term-for-term our `piSqTerm`.  Recorded in
   `PENDING_WORK.md`.  Returned proof not imported (ours is axiom-clean already).

## Repo state

- Every DIRECTION-queued brief (disjunction → universal → signed engine → tower
  C1–C10 → literature ledger) has a written RESULT.
- `src/` sorries: only the two OFF-LIMITS `CFScheduleA.lean` residues (`:4400`, `:5774`).
- Aristotle: nothing in flight.

## Next attack (this run continues)

Provable leaves / cruxes still open, in the order I intend to take them:
- Literature ledger discharges (cite → verify): `mahler_theoremM` /
  `berendBoshernitzan_bound` (general-`(g,k)` multiplier theorems — a genuine
  proof, not certificates), `furstenberg_dense_orbit` (Boshernitzan's elementary
  proof), `philipp_psi_mixing` (needs the constant-free `ρ<0.8` form; the repo's
  `(9/10)^n` bounds carry a constant — real work).
- Ln-2 sink path: all remaining nodes are hard-open (normality of `log 2`) or
  PNT-walled (β<9 run sharpening).
