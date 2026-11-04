# ON-LINE-FINDINGS 2026-11-03: gate 6 causal panel - operator decision PARK (pre-registered) - answered

Request: ON-LINE-REQUEST.md "2026-10-12, gate 6 causal panel done; operator decision", commit d67eb468 (HANDOFF
4b135daf, stuck strike 1).  Sources: PENDING_WORK "Gate 6 CAUSAL PANEL (2026-10-12)"; DIRECTION "Operator gate 6
CAUSAL PANEL" + ADDENDUM; `scripts/cstar_models/gate6/cpanel/classify.txt`; Astra (Codex reviewer) mail
`~/personal/agent-mail/nn-cstar/20261012T090735Z-codex-8b3d4904-*.md` (PARK recommendation, 90% on the resource
decision) and the unanswered review request `20261012T140828Z-opus-e3c64935-*.md` (token ASTRA-PANELR-e3c64935);
KB `knowledge/core/projects/portfolio/README.md` (board row: "read UNRESOLVED -> its pre-registered PARK").
Answered by Ren (host, 2026-11-03) - no web research was needed; this is the decision the request asked for.

## Answer: PARK
- **Decision: PARK the gate-6 route (fallback (a), bases {5,6,7} folded into the shared-phase {2,3} core) at the
  established bound c⋆ ≤ 124/25.**  This executes the pre-registered reading in DIRECTION step (5): LOOSE 16/40 and
  GENUINE 3/40 meet neither threshold (LOOSE ≥ 60%, GENUINE ≥ 50%), so "unresolved; stop, recommend PARK".
  Astra's standing recommendation was PARK; its review of the panel (four questions, 2026-10-12 14:08Z) received no
  reply in three weeks, and no nn-cstar run has been live since 2026-10-12.  Reopening is real compute spend
  (post-update slice ~49 h/pass; Astra: ~10 h/pass even with exMin at 0%), so reopen stays Trevor's explicit call.
- **Record the stop as:** "the current product+exception representation/search misses the cost gate (≤ 2 h/pass)
  by ~25x after one update; convergence unresolved."  It is NOT a refutation of c⋆ ≤ 449/100 and NOT a barrier at
  9/2 - so no Maze row (Maze records refuted routes).  Open statements stay open: `cStar_le_449` rests on
  `tailChargeBudget449`; `cStar_le_four`, `cStar_le_nine_halves`, `CStarLeThirteenFifths` unchanged.
- **Reopen bar (if Trevor ever funds it), in this order:** (1) remove the base-5 sliver r-bins only with an
  unreachability proof (Astra's point: unreachable pairs need a proof, not a density argument) - otherwise they are
  part of the state space and 18/40 panel pairs live there; (2) adopt the split-rule fix (bisect r as well as x:
  WORLDS+RSPLIT, ~4x nodes on the panel) in the pass-0 checker too; (3) rerun the cost slice with the WORLDS+RSPLIT
  evaluator on the SAME parent IDs and compare the post-update failure fraction with the pass-0 0.2763.  Caveat the
  lap itself recorded: the failure-fraction gate is the one Astra rejected, so a drop below 0.276 is a reason to
  price a sound joint-image checker, not a pass.
- **Caveats carried forward (unreviewed):** (a) WORLDS+RSPLIT is not the joint-image evaluator DIRECTION's ADDENDUM
  specified; if it is a sound lower bound, 40% LOOSE is a floor, not the looseness; its soundness is asserted in the
  lap, not reviewed.  (b) The concrete-parent teeth (every admissible parent's exact value ≥ both lower bounds on
  every panel pair) are not explicitly evidenced beyond `xcheck.py`'s 120-cell match.  Both are open questions to
  Astra, not findings.
- **Housekeeping done with this answer:** DIRECTION.md gains a "PARKED" block for this branch; the KB todo
  `nn-cstar-gate5-relaunch` and `projects/normal-numbers.md` record the park.  Nothing launched.

## The request, verbatim (cleared)
# ON-LINE-REQUEST (2026-10-12, gate 6 causal panel done; operator decision)
Causal panel finished per DIRECTION.  Pre-registered reading: **UNRESOLVED -> recommend PARK**.
LOOSE 16/40 (sound WORLDS+RSPLIT evaluator passes), GENUINE 3/40 (concrete real parents below target), UNRESOLVED
21/40; controls 40/40.  Identical-ID fractions 0.2763 -> 0.5713 confirmed.  Details: PENDING_WORK "Gate 6 CAUSAL
PANEL", commit 1fb883c0, table scripts/cstar_models/gate6/cpanel/classify.txt.  Side finding for Astra: the stock
split rule never bisects r, which accounts for ~40% of newly failing pairs (cheap fix); base-5 sliver r-bins hold
45% of the panel and admit no constructible real parent.  Nothing launched.
