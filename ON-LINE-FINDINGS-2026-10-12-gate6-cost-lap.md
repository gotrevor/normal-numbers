# ON-LINE-FINDINGS 2026-10-12: gate 6 cost lap (cost gate missed) - answered

Request: ON-LINE-REQUEST.md "2026-10-12 ~05:40Z - gate 6 cost lap: COST GATE MISSED (operator: bring Trevor
park-vs-continue)", commit 13e52e15.  Sources: PENDING_WORK "Gate 6 COST LAP (2026-10-12)"; Astra (Codex reviewer)
mail `~/personal/agent-mail/nn-cstar/20261012T090735Z-codex-8b3d4904-cc8a-4618-ae68-678d29cea5cc.md`.

## Answer
- **Astra: PARK** (90% on the resource decision, not a probability that the route is false).  Its corrections are
  recorded in PENDING_WORK (operator note, 30673b71): the met-set exception idea is unsound as stated; poisoning is
  partly enclosure looseness; even with exMin at 0% the post-update slice projects ~10 h/pass; record as
  "current representation/search misses the cost gate; convergence unresolved".
- **Trevor's decision (2026-10-12): fund the CAUSAL PANEL**, not a speed/shape lap: one bounded diagnostic lap that
  classifies newly failing pairs as GENUINE vs CHECKER LOOSENESS on frozen before/after weights.  Binding directive:
  DIRECTION.md "Operator gate 6 CAUSAL PANEL (2026-10-12 ~09:20Z)".  No search, stop either way.

## The request, verbatim (cleared)
## 2026-10-12 ~05:40Z - gate 6 cost lap: COST GATE MISSED (operator: bring Trevor park-vs-continue)
- Summary in PENDING_WORK.md "Gate 6 COST LAP (2026-10-12)".  Tool `scripts/cstar_models/gate6/exact5b0.c`.
- Root-positivity acceptance in place, with teeth (exact5z certified an all-zero PHI; exact5b0 rejects it).
- Pass 0: exMin was 90% of CPU (empty scans); with the index + B0, 255-344 s per 3% slice (2.4-3.2 h/pass on
  a box at load ~12), records byte-identical to exact5z.
- Post-update (185k exceptions): ~49 h/pass projected even with a row index (exMin still 80%; pair evals
  17x; slice failure fraction 0.28 -> 0.57).  Gate (<= 2 h/pass) missed by ~25x on the passes that matter.
- No multi-pass search launched.  Request: Astra/Trevor decision - park the route at 124/25, or fund one
  more engineering lap (exMin range-min + an exception shape that does not poison neighbouring leaves).
