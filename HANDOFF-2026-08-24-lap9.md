# HANDOFF — Khinchin Tier 2, route C′ FAMILY machinery complete

**Branch/HEAD**: master @ `ed87d7d`, `lake build` green (8750 jobs).
Supersedes `HANDOFF-2026-08-24-0316.md`.

## What landed this run (9 green commits, all axiom-clean `[propext, Classical.choice, Quot.sound]`)

1. `volume_logBadZone_le_vol` (`KhinchinBrick.lean`) — Lebesgue bridge for the
   Khinchin log-tail bad zone.
2. `exists_good_avoiding_bad_khinchin` / `_of_large_khinchin` — three-zone
   combine (CF + d-ary + ONE log zone), `TBrick.lean`-mirroring machinery.
3. `TBrick.exists_refinement_uniform_khinchin` (`KhinchinRefine.lean`) —
   threaded the log-tail payload through the refinement step, via the new
   `logBirkhoffSum_shift` digit-shift identity.
4. **Layering fix** (`CFLogTail.lean`'s `integral_logTailFn_tendsto_zero`,
   khinchinK₀-free) — needed so the Khinchin refinement machinery stays
   upstream of `CFSchedule.lean` (avoiding an import cycle through
   `Khinchin.lean`/`Headline.lean`).
5. **First CFSchedule.lean threading attempt** (`KFn t` tied to `schedEps t`)
   — built, green, Tier-1 re-verified clean — **then DISCOVERED WRONG**
   (see below) and **SUPERSEDED** by the family design (the commit is still
   in history; nothing was reverted, the schedule was just rewired again).
6. **DESIGN FIX — the summable family** (`KhinchinFamily.lean`): a real bug
   was found and fixed in the SAME run (not left for a future lap to
   discover). See "The bug and the fix" below.
7. `exists_good_avoiding_bad_khinchin_family` / `_of_large_khinchin_family`
   (`KhinchinFamily.lean`) — three-zone combine, FAMILY form (log budget
   fixed at `1/7`, no per-call hypothesis).
8. `TBrick.exists_refinement_uniform_khinchin_family`
   (`KhinchinRefineFamily.lean`) — refinement step, FAMILY form: the
   extension word's log-tail mass past `khinchinK j` is `≤ khinchinEta j * n`
   for EVERY `j < tK` simultaneously.

**Important**: `CFSchedule.lean` currently still carries the SUPERSEDED
(item 5, `KFn t`/`schedEps t`-tied) threading — it is a TRUE, GREEN,
axiom-clean statement, just not useful for closing `xstar_log_tail_uniform`
(see below). It has NOT been ripped out; the FAMILY machinery (items 6-8) is
built ALONGSIDE it, ready to be wired in as the replacement. Next lap's first
job is exactly that rewire (see NEXT).

## The bug and the fix (read this before touching CFSchedule.lean again)

The natural first design ties the log-zone slack `η_t` to `schedEps t → 0`
per level, which via Markov forces the cutoff `K_t = KFn t → ∞`. For ANY
FIXED external `K` (as `xstar_log_tail_uniform` needs — `∃K₀ ∀K≥K₀ ∀n`), once
`K_t > K` for a stage (which happens for COFINITELY many levels, since
`K_t→∞`), that stage's own guarantee bounds `tail-past-K_t` — a SMALLER
quantity than `tail-past-K` we actually need (bigger cutoff catches fewer
digits ⟹ smaller tail; the schedule only controls the smaller one). So the
per-level bound at a GROWING cutoff can never transfer to a FIXED external
`K`, and the naive assembly is a dead end — not a missing lemma, a genuine
design defect. Full derivation is in `KhinchinFamily.lean`'s module
docstring.

**Fix**: decouple the cutoff from the level. Use a GLOBAL countable family
`(khinchinK j, khinchinEta j)`, `j : ℕ`, `khinchinEta j = 1/(j+1) → 0`, with a
SUMMABLE coefficient budget `khinchinCoeff j = (1/7)·(1/2)^(j+1)` (geometric,
partial sums `≤ 1/7` for ALL `t` — `sum_khinchinCoeff_le`). At level `t`, the
schedule makes the extension word avoid ALL `j < t` zones SIMULTANEOUSLY (a
FINITE union bounded by the FULL geometric sum, uniform in `t` — no
per-level coefficient blowup). For a target `ε`, pick `j(ε)` with
`khinchinEta j(ε) ≤ ε`; the FIXED cutoff `K₀ := khinchinK j(ε)` then works
for every level `t > j(ε)` — that level's own guarantee is available
VERBATIM at the SAME fixed `j(ε)`, no growing-cutoff mismatch.

## NEXT (concrete, in order)

1. **Rewire `CFSchedule.lean`** to use
   `TBrick.exists_refinement_uniform_khinchin_family` (not the single-zone
   `_khinchin` version) with `tK := ` the level. Mirrors the exact edit
   pattern already done once for the single-zone version (see commit
   `949f0b1` for the shape of the diff: `sched_refinement`, `kminFn_spec`,
   `nFn_spec` gain the family conjunct; `SchedStep`/`schedStep_exists` gain
   one more field). All downstream `sched_step` destructuring already ends
   in a trailing `-` (verified in commit `949f0b1`) except
   `DaryCorrect.lean:48`'s named destructure, which needs one more `-`
   appended (same fix as last time).
2. **Assemble `xstar_log_tail_uniform`** (`Khinchin.lean`, the sole
   remaining Tier-2 `sorry`): for target `ε`, take `j(ε) := ⌈1/ε⌉` (so
   `khinchinEta j(ε) ≤ ε`), split `xstar`'s prefix of length `n` at the
   schedule stage where level first exceeds `j(ε)` (a FIXED, finite index —
   `sched_t_eventually`/`sched_t_tendsto` already give this kind of
   threshold-crossing fact for CF/d-ary, mirror it). Early stages (level
   `≤ j(ε)`, finitely many) contribute a BOUNDED absolute amount via the
   unconditional `uSched_log_sum_le`/`wSched_log_sum_le`-style coarse bound
   (already exists in `CFCorrect.lean`, reuse the `goodC`-telescoping
   pattern). Late stages (level `> j(ε)`) use the family guarantee AT INDEX
   `j(ε)` directly (available since `j(ε) < t_s`). This gives a bound
   `≤ ε + (bounded)/n`, i.e. an EVENTUAL-in-`n` statement. Check whether
   `xstar_log_tail_uniform`'s literal `∀n` (not `∃N∀n≥N`) is load-bearing
   for its ONE consumer, `xstar_log_digit_avg_tendsto` (`Khinchin.lean`) — if
   not (very likely: that proof already works via `Metric.tendsto_atTop`,
   which only needs eventual bounds), WEAKEN `xstar_log_tail_uniform`'s
   statement to `∃N, ∀n≥N` (it is an internal, non-JUDGE-frozen lemma) and
   redo the trivial `N`-combination in `xstar_log_digit_avg_tendsto`'s proof
   (`max` of two thresholds — standard).
3. Once `xstar_log_tail_uniform` is closed: `xstar_khinchinTypical` and
   `xstar_log_digit_avg_tendsto` (already proved MODULO this sorry) close
   automatically. Then route D′ (layering: move `KhinchinTypical`/
   `khinchinK₀` defs upstream so `Headline.lean:134` can invoke
   `xstar_khinchinTypical`) is the last step to close the Tier-2 headline
   `exists_absolutely_normal_cf_normal_khinchin`.

## Verification notes

- Tier-1 (`exists_absolutely_normal_cf_normal`, `Headline.lean:109`)
  re-checked axiom-clean after EVERY `CFSchedule.lean` edit this run — stays
  `[propext, Classical.choice, Quot.sound]`. The additive-schedule-edit fence
  in `DIRECTION.md` is intact.
- `src/` open sorries: `Headline.lean:134` (Tier-2 headline, awaiting route
  D′ layering) + `Khinchin.lean:521` (`xstar_log_tail_uniform`, the active
  crux) — unchanged count, this is the ongoing decomposition, not a
  regression.
- No uncommitted edits; working tree clean at `ed87d7d`.
