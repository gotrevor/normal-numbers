# HANDOFF — pointer

**STUCK (2026-10-06, branch `proof/cantorexp-stretch`):** the CURRENT DIRECTIVE's objective is
met — `CantorExactExponentStretch.ae_not_liouvilleWith_all` and the stretch headline are proved
(standard axioms; verify: `#print axioms` in a scratch file importing the module), and the module
is sorry-free.  Remaining `src/` sorries belong to other campaigns; `StretchBFR` is forbidden
drift.  Ask: an altitude lap sets the next directive.  See `HANDOFF-2026-10-06-stretch-lap3.md`.

This is a thin pointer, not an overview.  Newest lap: `HANDOFF-2026-10-03-levinsparse-lap1.md` (BLOCKED, operator-gated).  Read, in order:

1. **`DIRECTION.md` → CURRENT DIRECTIVE** — binding, altitude-owned, outranks every baton.
2. **`STATUS.md`** — the living overview (refreshed on review laps).
3. **The newest dated baton**: `HANDOFF-2026-10-02-erdos257b2-lap3.md` (Erdős #257 base 2).
   Find it with `ls HANDOFF-*.md | sort -t p -k2 -n | tail -1` (numeric — plain `ls | tail`
   breaks once lap numbers pass 99).
4. **`PENDING_WORK.md`** — the queue and the corrected attack path.
5. `src/NormalNumbers/Maze.lean` — every refuted route, as Lean data.  Read before proposing one.

Earlier batons: `HANDOFF-2026-09-29-2330.md`, `HANDOFF-2026-09-29-2100.md`,
`HANDOFF-2026-09-29-0307.md`, and `archive/handoff/`.

## BLOCKER (2026-10-02, erdos257-base2 run) — operator-gated
Scoped target `sorry-free:src/NormalNumbers/Erdos257Base2.lean` cannot be honestly met:
its only hypothesis `CastingOut.TTEquidistributedCorrelation` is PROVABLY TRUE
(`ttEquidistributedCorrelation_trivially_true`, LiteratureTTEquidistributedDefect.lean; Maze row
"TT 3.1(i) with a Lebesgue-measured exceptional set"), so the frozen headlines are unconditional
base-2 disjunctivity (open). Verify: `#print axioms` on that theorem = trust base.
Ask: operator re-freezes the headline on `CastingOut.TTEquidistributedDyadic`. Details:
HANDOFF-2026-10-02-erdos257b2-lap1.md.
Re-confirmed 2026-10-02 (lap 2): stuck-bail confirmed, treadmill halted for operator.

## OPERATOR RESOLUTION (2026-10-02)
Accepted.  `Erdos257Base2.lean` headlines are re-frozen on `CastingOut.TTEquidistributedDyadic`
(the derivation from TT Thm 3.1(i), with `c/4`, is now in its docstring, 85%).
`TTEquidistributedCorrelation` stays as the recorded vacuous transcription (Maze row).  The stuck
flag is cleared: continue with N3-N8 against the dyadic Prop (N6 now consumes it).

## STUCK-BAIL (2026-10-02, erdos257b2 run, strike 1)
- **What:** this run's operator scope — Erdős #257 base 2 headline axiom-clean — is MET (2d2e70e1).
  Verify: `#print axioms` of `NormalNumbers.Erdos257.{isDisjunctive_subsetLambert_two,
  erdos257_primeSubset, erdos257_residueClass}` = `[propext, Classical.choice, Quot.sound]`.
- **Why stuck:** the repo-wide self-stop gate counts 23 sorries in other lanes (outside the operator's
  scope for this run), so `box done` is declined; no lap in this scope can clear them.
- **Need from operator:** relaunch/stop with `--done-when` scoped to `src/NormalNumbers/Erdos257Base2.lean`
  (or accept done).  Details: `HANDOFF-2026-10-02-erdos257b2-lap5.md`.
Re-confirmed 2026-10-02 (fresh lap): build green, axioms trust-base only; stuck strike 2 recorded.

## STUCK-BAIL (2026-10-03, dimh run, strike 1)
- **What:** this run's operator target, `ExplicitOmegaK.dimH_Omega_eq_one`, is PROVED (b2c7ac2f).
  Verify: `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The optional
  `bakerBanajiAnalyticQuarterCantor_of_general` is proved too.
- **Why stuck:** the repo-wide self-stop gate counts sorries in other lanes, outside this run's scope.
- **Need from operator:** accept done, or relaunch with `--done-when` scoped to this lane.
  Details: `HANDOFF-2026-10-03-dimh-lap1.md`.
Re-confirmed 2026-10-03 (fresh lap): `#print axioms dimH_Omega_eq_one` = trust base only; stuck strike 2 recorded.

## STUCK-BAIL (2026-10-03, levinsparse run) — CONFIRMED, treadmill halted for operator
- **Done:** `NormalNumbers.LevinSparse.exists_levinRate_oddNormal` proved; `#print axioms` = [propext, Classical.choice, Quot.sound].
- **Blocker:** scope `sorry-free:src/NormalNumbers/LevinSparse.lean` has one sorry, `exists_absNormal_base2_fast`,
  a FROZEN statement of an open problem (absolutely normal x with base-2 discrepancy O(N^-θ), θ>1/2; ABSS 1707.02628 barrier).
- **Operator ask:** convert `exists_absNormal_base2_fast` to a `def … : Prop` conjecture node, or rescope `--done-when` to exclude it.
  Details: `HANDOFF-2026-10-03-levinsparse-lap1.md`.

## STUCK 2026-10-06 (BFR directive lap 1) — stop condition met
Directive says stop when BFR confidence < 1% with every route in the Maze. Verify fast:
`StretchBFR.lean` module doc (confidence line), Maze rows "3-adic Farey separation as a BFR count"
and "power saving for N_K(Q, delta) from separation", `#print axioms StretchBFR.card_cantor_hyperbola_le` clean.
Ask: operator's next directive. Detail in HANDOFF-2026-10-06-bfr-lap1.md.
WHAT is blocked: further BFR-directive work; the directive's own stop rule ("stop when < 1% with every route in the Maze") has fired.
WHY operator-gated: continuing would mean picking a new objective (e.g. transcribing Chow–Varjú–Yu, or another campaign's sorries), which the directive reserves to the operator; the remaining StretchBFR sorries are off-bet.
NEED from operator: a next directive, or a rejection of the <1% verdict saying which candidate to reopen.
