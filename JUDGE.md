# JUDGE — the attended architect/judge role for the B5′ campaign ⚖️

The treadmill grinds; **statement authority stays with the attended judge
sessions** (the goodstein "judge mode" pattern).  A monitor thread loads this
file and works the checklist.  Laps never edit this file above the Ledger.

## Division of authority

- **Laps (unattended)**: prove the frozen statements; add any private
  intermediate lemmas; commit green; flag suspected-wrong statements in
  HANDOFF and move on.  Laps do NOT reshape, weaken, re-hypothesize, or
  delete a frozen statement, and do not change the W-plan or this file.
- **Judge (attended)**: adjudicates flags, owns every statement change, owns
  route changes, owns the W-plan (`KHINCHIN.md`), decides stop/continue.

## Per-visit checklist

1. **Status**: `lean-treadmill status normal-numbers` — lap/kind, sorry
   count, HEAD; then `git-safe -C ~/src/normal-numbers log --oneline
   <last-judged>..HEAD` for what's new.
2. **Statement integrity** (the non-negotiable): diff the frozen statement
   file(s) against the last judged SHA —
   `git-safe diff <last-judged> -- src/NormalNumbers/CFCylinder.lean` —
   every frozen statement and every anchor must be **character-identical**
   (docstrings/intermediates may change freely).  Any drift: stop the
   treadmill, adjudicate, restore or ratify explicitly here.
3. **Axiom hygiene** on newly discharged sorries: `#print axioms` = exactly
   `propext`, `Classical.choice`, `Quot.sound`.  No `native_decide` (prefer
   `decide +kernel`), no new axioms, no unexplained `maxHeartbeats` bumps —
   `/lean-review` covers the smell list.
4. **Silent-restriction scan**: a frozen statement whose proof suddenly
   delegates to a reshaped private lemma can hide a weakening ("a
   generalization can be a silent restriction").  Skim the load-bearing
   intermediates of anything newly discharged.
5. **HANDOFF flags**: read the newest `HANDOFF-*.md`.  A lap claiming a
   frozen statement is *wrong* is the highest-priority item — adjudicate
   against `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` and the
   source paper before touching anything.
6. **Ledger**: append a dated line below (SHA judged through + verdict).

## Architecture guardrails (enforce; laps must not cross)

- **No efficiency machinery.**  B5′ deliberately drops B–Y's O(n⁴) claim:
  no Morita/Vallée CLT, no B–Y Lemma 4/5 analogs.  Length control is the
  Markov + Fibonacci substitute (W2).
- **W3 route is decided** (`KHINCHIN.md` "W3 route"): the `tailDensity`
  family + ratio-contraction, Kuzmin √n-rate as fallback.  No Philipp, no
  Merlevède–Peligrad–Rio, no KPW imports; no ergodicity or pointwise
  Birkhoff anywhere in B5′.
- **Conventions are load-bearing**: digit `0` = junk marker (rationals /
  out-of-range), so `∀ a ∈ w, 1 ≤ a` hypotheses stay; cylinder-vs-interval
  mismatches are null sets — measure-zero handling, not set equalities.
- **Constants**: the frozen distortion/quasi-mult constant is `2` (B–Y's
  own proofs deliver exactly 2).  A lap that can only reach a weaker
  constant has a proof problem, not a statement problem — judge decides.

## Stop / escalate

- `lean-treadmill stop normal-numbers` (graceful) · `--after-lap` ·
  `--now`.  Stop for: statement drift (check 2), axiom drift (check 3), or
  thrashing (a lap burning its budget on `volume_cfCylinder` without
  committed intermediates → consider an attended session to split the
  bridge into its own scaffold).
- Campaign self-stops when `src/` is sorry-free (= W1 done).  Then the
  judge runs the close-out: full `#print axioms` sweep of the 12,
  `/lean-review` on the whole W1 diff, ROADMAP/`KHINCHIN.md` status update,
  and stages the W2 scaffold (new frozen statements = judge work).

## Ledger (append-only, newest last)

- 2026-08-23 · judged through `4ad5f8e` (scaffold + briefs, pre-campaign
  baseline) · 12 sorries open · statements/anchors as frozen.
- 2026-08-23 11:20 · judged through `8fa056f` (lap 1 algebra batch, 9/12
  discharged) · statements + anchors character-identical vs `4ad5f8e` (only
  `sorry` lines replaced; private helpers `cfK_cons`, `one_le_cfK` added —
  in-charter) · smell scan of the Lean diff: greps clean (no `axiom`, no
  `native_decide`, no `maxHeartbeats`, no import changes) · kernel-tier
  `#print axioms` NOT run this visit (lap live, avoiding build contention) —
  box's "axiom-clean" stands at its tier; full sweep owed at close-out ·
  no wrongness flags in HANDOFF · lap grinding the 3 measure sorries
  (`volume_cfCylinder` crux) · verdict: healthy, continue.
- 2026-08-23 ~11:45 · **W1 CLOSE-OUT** · judged through `f76a1b1` (laps 2–3;
  campaign complete, self-stopped after lap 3) · statements + anchors
  character-identical vs baseline across the whole campaign (only the 12
  `sorry` lines ever removed in `CFCylinder.lean`) · **kernel-tier
  `#print axioms` sweep run by the judge on all 12: every one a subset of
  {propext, Classical.choice, Quot.sound} — axiom-clean, verified
  2026-08-23** · `/lean-review` on `4ad5f8e..HEAD`: no heartbeat bumps, no
  `native_decide`, no `axiom` decls, no trust escapes, no silenced linters,
  no Prop-def laundering, no import changes; residue = style lints only
  (unused `hwpos`/`hupos` binders forced by the frozen shapes, a few
  `<;>`/`simpa`/unreachable-tactic nits) · no wrongness flags · verdict:
  **W1 ratified**.
- 2026-08-23 ~11:50 · **W2 scaffold staged by the judge** (new frozen
  statements): `CFDigitLaw.lean` — `genWords` def + 10 sorry'd statements
  (digit law, disjointness, partition `tsum`, Gauss/Lebesgue two-sided
  comparison, `γ(univ)=1`, `K ≤ ∏(aᵢ+1)`, conditional `E[log qₙ] ≤ Cn`,
  Markov half-mass Lemma-5 substitute, Fibonacci relative-length bound) ·
  4 kernel-checked anchors frozen · builds green (10 sorries expected) ·
  these shapes are now the frozen trust surface for the W2 campaign.
