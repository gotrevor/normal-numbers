# HANDOFF — pointer

This file is a **thin pointer**, not a second overview.

* Living overview: **`STATUS.md`**
* Newest baton: **`HANDOFF-2026-09-15-R-laps146-164.md`**
* Open items / attack paths: **`PENDING_WORK.md`**
* Binding orders: **`DIRECTION.md`** → the ACTIVE override at the top (outranks every handoff)

## ⛔ STUCK-BAIL, strike 1 (2026-09-15, lap 165) — verifying lap, read this

**Claim**: every remaining obligation in `src/` is operator-gated.  Full write-up in
`HANDOFF-2026-09-15-R-laps146-164.md` (section "STUCK-BAIL, strike 1").

**WHAT is blocked.**  `src/` contains exactly two `sorry`s:
* `NormalNumbers.PrimeLambertOscillation.phaseOscillation` — `src/NormalNumbers/PrimeLambertOscillation.lean:95`
* `NormalNumbers.MahlerDriftOne.exists_drift_one_background` — `src/NormalNumbers/MahlerDriftOne.lean`

**WHY it is outside a lap's power.**  Both are on `DIRECTION.md`'s **forbidden-drift list**.  The
ACTIVE override at the top of `DIRECTION.md` (2026-09-14 night, "AFTER THE EXTRACTION", plus its
23:59 addendum) scopes this run to objective **R** and re-binds the forbidden-drift list.  Grind
laps may not edit `DIRECTION.md`.  So the work is not hard — it is *forbidden*.

**WHY the scope is finished.**  The override's stop condition is "stop when R has a kernel
verdict".  R had it at lap 136; laps 146–164 then closed all three items R's own wrap left open
((E) proved in kernel, `union_le_of_determining`, `grouped_union_le'`), pinned the threshold at
every `K ≥ 3` (`threshold_exact`), and closed both routes to a better density exponent
(`balance_not_determined_by_axes` proved; `PROBE-2026-09-15-balanced-count.md` refuted).

**WHAT IS NEEDED FROM THE OPERATOR** — any one of:
1. authorise work on the forbidden-drift `sorry`s (`phaseOscillation` and/or
   `exists_drift_one_background`); or
2. set a new objective in `DIRECTION.md`; or
3. relaunch scoped, e.g. `--done-when 'sorry-free:src/NormalNumbers/G4RowVariance.lean'`, so the
   host stops on the actual target rather than on the whole repo being sorry-free.

**Fast verification**: `grep -rn "sorry" src/ --include=*.lean | grep -v "^.*--"` shows only those
two; then check they are named on `DIRECTION.md`'s forbidden-drift list.  If confirmed, file your
own `box stuck`.
