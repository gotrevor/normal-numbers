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
