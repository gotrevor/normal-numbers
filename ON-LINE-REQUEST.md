# ON-LINE-REQUEST

## 2026-10-12 ~05:40Z - gate 6 cost lap: COST GATE MISSED (operator: bring Trevor park-vs-continue)
- Summary in PENDING_WORK.md "Gate 6 COST LAP (2026-10-12)".  Tool `scripts/cstar_models/gate6/exact5b0.c`.
- Root-positivity acceptance in place, with teeth (exact5z certified an all-zero PHI; exact5b0 rejects it).
- Pass 0: exMin was 90% of CPU (empty scans); with the index + B0, 255-344 s per 3% slice (2.4-3.2 h/pass on
  a box at load ~12), records byte-identical to exact5z.
- Post-update (185k exceptions): ~49 h/pass projected even with a row index (exMin still 80%; pair evals
  17x; slice failure fraction 0.28 -> 0.57).  Gate (<= 2 h/pass) missed by ~25x on the passes that matter.
- No multi-pass search launched.  Request: Astra/Trevor decision - park the route at 124/25, or fund one
  more engineering lap (exMin range-min + an exception shape that does not poison neighbouring leaves).
