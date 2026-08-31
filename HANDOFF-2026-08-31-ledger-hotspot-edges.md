# HANDOFF: π² BBP merged; B–M hot-spot cluster verified; frontier walls mapped 🔌

Overnight autonomous continuation (operator-authorized 2026-08-30, same night).
Branch `master`, tree clean, full build green (8833 jobs). Continuation of
`HANDOFF-2026-08-31-pisq-bbp-proved.md`.

## What landed this session (8 commits on master)

1. **Merged `wip/pisq-bbp-decomp` → master** (`3003362`, `--no-ff` per repo
   precedent). `piSqBBP_proved : PiSqBBP` (Bailey Formula 29) axiom-clean;
   re-confirmed on master post-merge (`[propext, Classical.choice, Quot.sound]`,
   no `sorryAx`).

2. **Ledger deepening — statement nodes** (`b71ed1b`), the operator-named targets:
   - `philipp_psi_mixing` (Philipp 1967 Satz 3 / Scheerer Thm 2.1) — exponential
     ψ-mixing of CF digits, stated in cylinder form (new `CFDefs.cfCylinderFrom`);
   - `baileyMisiurewicz_strong_hot_spot` (Thm 3.4) + `_criterion` (Thm 3.5),
     sequence-space, via new `IsSeqHotSpot` / `bmHotSpotRatio`.

3. **Frontier audit** (`59ac373`): kernel-verified the ln-2 run tower
   (`lnTwoRun_le_unconditional_sharp`: **binary `ln 2` runs at `n` ≤ 9n,
   unconditional**) is axiom-clean; **refuted the β<9 sharpening** against the
   actual v4.33.1 mathlib pin (no PNT: `Chebyshev` tops out at `theta_le_log4_mul_x`
   = the `4^ℓ` already used). β<9 is a machinery wall (needs PNT ported).

4. **B–M hot-spot cluster VERIFIED** (`src/NormalNumbers/LiteratureBMStrong.lean`,
   all axiom-clean, 0 sorries):
   - `baileyMisiurewicz_strong_hot_spot_criterion_holds` (**Thm 3.5**, `3057205`)
     — uniform-`C` block-occurrence ⇒ normal, via a full block↔b-adic-interval
     bridge (`blockOfNat` round-trip, `matchesAt_iff_occursAt`,
     `visitCount_eq_card_matchesAt`, `eventually_visit_bound_of_limsup`) into
     `isNormal_of_visit_upper_bound`;
   - `baileyMisiurewicz_weak_hot_spot_holds` (**Thm 1.1, full iff**, `5d4b7eb`)
     — `⟸` the visit criterion, `⟹` Wall's `isNormal_iff_equidistributed_orbit`
     (limsup = `d−c`, `B=1`);
   - `normal_no_seqHotSpot` (**Thm 3.4 forward**, `1807381`) — normal ⇒ no hot
     spot (each `bmHotSpotRatio = 1`). Converse (non-normal ⇒ hot spot) stays
     unformalized: needs weak-* compactness + Besicovitch covering.

5. **Faithfulness cross-check in flight** (`e35c652`): submitted the *prose* of
   Formula 29 to Aristotle (project `7ee16d3a-f125-48f0-9381-d39b95c4ba42`) for
   an independent NL→formalization to compare against `PiSqBBP`.
   **NEXT SESSION: `aristotle show 7ee16d3a…`, verify statement-equivalence to
   `HasSum piSqTerm (Real.pi^2)`.** Don't trust any returned proof without
   `#print axioms`.

## Ledger status (`Literature.lean`)

WIRED/verified: AR boundary, B–Y existence, M31, weak hot spot (1.1),
strong-3.5, strong-3.4-forward. Remaining nodes are the **hard/open tier**,
none lap-tractable with current mathlib:
- `philipp_psi_mixing` — needs Gauss–Kuzmin–Lévy spectral gap;
- `baileyMisiurewicz_strong_hot_spot` **converse** — weak-* compactness;
- `mahler_theoremM`, `berendBoshernitzan_bound` — Diophantine number theory;
- `furstenberg_dense_orbit` — Furstenberg 1967 ×2×3 rigidity;
- `vandehey_matrix_action` — Compositio-level CF ergodic theory;
- `waldschmidt_conjecture_1_1`, `vandehey_quadratic_problem`,
  `mendesFrance_simple_normality_problem` — **OPEN problems**.

## Sink-path frontier (DIRECTION.md conjecture-graph objective)

Sink `IsNormal 2 (Real.log 2)`. Weakest open nodes are the equidistribution /
disjunctivity hypotheses (`LnTwoHypothesisFreq/Lambda/D`, `Equidistributed
lnTwoOrbit`) — these ARE normality/disjunctivity of `log 2`, hard-open. Tier-1
run cap done (β=9, pin-walled below); Tier-2 `LnTwoPolySep` Mahler-class open.
No cheap node/edge available; the named frontier moves (sliver-recurrence,
mixing/discrepancy rungs) all route through the same walled Diophantine input.

## Off-limits (operator brief, untouched)

Both `CFScheduleA.lean` sorries (~4400 REFUTED-FALSE, ~5774 retired) and the two
`Comparator/Challenge.lean` statement holes.
