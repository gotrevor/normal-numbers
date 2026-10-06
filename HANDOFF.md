# HANDOFF — pointer

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

## cantorbad BLOCKER (2026-10-06, box stuck strike 1)
- Blocked: the frozen crux `fourierPairRate_descent` is about `descentLaw`, whose dead-block replacement is
  `Classical.choose` (`descent_eq_descentR`, `repC_ok`). A proof can use only `RepOK repC`, so in effect it
  must cover every admissible rule.
- Why operator-gated: `AdversarialReplacement` (55%) says some admissible rule breaks 2-normality. Dead-stage rate is
  flat at ≈1e-3 (numerics in its docstring), so an adversary gets infinitely many steers. The operator forbade
  restating the crux or the law.
- Exact ask: may the headline be routed through a new law with canonical replacement (e.g. uniform resampling
  among alive blocks from fresh coins), with its own Fourier crux? The headline statement stays unchanged.
- Verify fast: read the `AdversarialReplacement` docstring and run `scripts/cantorbad_eta.py 3 10 400`.
Re-confirmed 2026-10-06 (cantorbad lap 4): new `fourierPairRate_descent_of_deadRateDecay` reduces the crux, for every
admissible replacement rule, to `DeadRateDecay`. That node is believed false (dead-stage rate flat at about 1e-3), so the
crux as frozen is likely unprovable from `choose_spec`. The operator ask stands. Stuck strike 2.

## OPERATOR RESOLUTION (2026-10-05 22:55, cantorbad)
Accepted, with the headline `exists_mem_cantorSet_bad_isNormal_coprime_three` unchanged.
- Route the headline through a NEW law with canonical replacement: a dead coin block is replaced by an alive
  block chosen UNIFORMLY from fresh coins (rejection sampling on the next coin blocks is fine), so the law stays
  within a controlled distance of uniform at every stage.  Give it its own Fourier crux
  (`fourierPairRate_descentR` or similar) and wire the headline through `exists_of_law` on it.
- Convert the old crux `fourierPairRate_descent` (choose-based `descentLaw`) into a recorded conjecture node,
  `def FourierPairRateChoose : Prop`, keeping its docstring plus the `AdversarialReplacement` evidence, so it is
  recorded but no longer a blocking sorry.  Keep `DeadRateDecay` and `fourierPairRate_descent_of_deadRateDecay`.
- Guard for the new crux: a proof that only uses `RepOK` (any admissible rule) reduces to `DeadRateDecay`
  (believed false), so it must use the uniformity of the resampled block.  The base-2 sibling
  `perStage_deadCount_not_enough` and `b = 3` still apply; update the BarrierAudit crux link to the new crux.
Stuck flag cleared.

## cantorbad BLOCKER (2026-10-06, lap 5, box stuck strike 1)
- Blocked: headline rests only on `midStages` (CantorBadNormal.lean): the signed dead-character sum over the stages
  with N^{1/40} ≲ 3^{10S'} ≲ b^N.  The low and high stages are proved (`hybridCassels_low`, `deadChar_tail_le`).
- Why: it needs decorrelation, under μ_K, between being near a rational p/q (q ≈ 3^{5S'}) and the size of the lacunary
  sums Σ e(h bⁿ x).  That input is research-level and unproved in the literature.  Absolute and per-stage forms are
  recorded as too strong (`DeadCharCancelAbs`, `StageSaving`), and the Cauchy–Schwarz bootstrap and derandomization
  only reach a floor (`cs_bootstrap_floor`; PENDING_WORK).
- Ask: (a) accept a conditional headline from a decorrelation node, (b) keep narrowing on the treadmill, or (c) retarget.
- Verify fast: `grep -n "sorry" src/NormalNumbers/CantorBadNormal.lean` shows `midStages` plus the off-path old-law
  sorry; read the docstrings of `midStages` and `deadCharSigned_core`.

## cantorbad lap 6 (2026-10-06): blocker strike 1 superseded
The operator's session instruction (keep attacking the resLaw crux) answers the lap-5 ask.  The headline now goes
through the local almost-sure route; crux `localDeadBias_resLaw`.  See `HANDOFF-2026-10-06-cantorbad-lap6.md`.
