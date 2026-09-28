# Operator brief: unattended lane-2 grind (Fable-low treadmills) 🏃

## RESULT (2026-08-29, run complete — all 5 targets landed) ✅

All five targets discharged in ~75 min of Fable/low laps (`lean-lap-driver`, one
scoped run per target, planted `sorry` stubs as host-side done-when gates), every
claim below re-verified HOST-side by `#print axioms` — trust triple
`[propext, Classical.choice, Quot.sound]`, 2026-08-29.  (1) **PiBBP discharged**:
`piBBP_proved` (`PiBBPProof.lean`) proves the BBP formula integral-free via the
roots-of-unity filter over `Complex.hasSum_taylorSeries_neg_log` — every π headline
is now unconditional at its call site.  (2) **Twin edge** `oneRun_le_of_sliverEscape`
(`KickDynamicsOneRun.lean`): honest width-mismatch resolution — new wide-sliver node
`SliverEscapeWide` (provenance docstring) with `sliverEscape_of_wide`, constant `+2`.
(3) **Fermat-quotient bridge** `lnTwoNum_modEq_fermatQuotient`
(`LnTwoFermatBridge.lean`): the Glaisher/Sun congruence proved in the probe-frozen
shape, byte-identical statement.  (4) **Tier-1 discharged**: `lnTwoExpSep_holds`
(`LnTwoExpSepProof.lean`) — `∃ N₀, LnTwoExpSep 26 N₀`, in-house via the vendored
shifted-Legendre package (`LegendreShifted/LegendreHeight/LcmUptoGrowth.lean`, both
honest gaps closed: `|Q|` height + pairing argument); β = 26 is the crude-constant
rate (Alladi–Robinson ≈ 3.63 needs sharp asymptotics, not attempted) but ANY explicit
β lights the run tower unconditionally via `run_le_of_expSep`.  (5) **Dessert**:
`logTwoSq_top_sliver_of_zeroRun` (`LogTwoSqKicked.lean`) — summed-kick machine
instantiated for log²2 over the new CITED node `LogTwoSqSeries` (probe
`experiments/logtwosq_series.py`, identity verified to 70 digits, PASSES), with the
position-dependent cap and `logTwoSqCap_le_half`.  Frozen decls and the two dead
`CFScheduleA` sorries untouched; build green throughout; nothing hard-blocked, outbox
empty.  Lane-2 discharge now owed: `LogTwoSqSeries` (the one new CITED node).

**Written 2026-08-29 by Ren at Trevor's direction.  Trevor opening a session on this brief IS
the launch authorization** ([[agent-operated-treadmills]]: treadmills are agent-operated after
explicit authorization — this is it).  Trevor is AFK for several hours; operate unassisted.

## Mission

Grind **lane-2 formalizations** (known mathematics discharging named nodes) in this repo via
treadmill laps on **Fable, low effort**.  This is the operator firing DIRECTION.md's
"lane 2 only when scheduled" clause — it does not override the novel-proofs objective; it
schedules the backlog that makes the novel results unconditional.  Effort routing: low
suffices for frozen-scaffold grinding; escalate one lap's effort only when a genuinely
crux-shaped subgoal walls twice → `knowledge/core/projects/lean-journey/reference/treadmill-effort-routing-quality-vs-cost.md`.

## Targets, ranked (work top-down; each is self-contained)

1. **Discharge `PiBBP`** (`PiBBP.lean:62`, the frozen node `HasSum bbpTerm Real.pi`).
   The classical BBP integral computation (Bailey–Borwein–Plouffe 1997): geometric series
   under `∫₀^{1/√2}`, four arctan/log integrals reassembling to π.  Payoff is large: every π
   headline (`pi_top_sliver_of_zeroRun`/`_fRun`, `pi_digit_mismatch_boundary`) becomes
   unconditional trust-triple.  Check mathlib for `arctan`/integral API before hand-rolling.
2. **Twin edge `oneRun_le_of_sliverEscape`** (blueprint architecture list; "an afternoon").
   Hygiene edge beside the existing zero-run form.
3. **Glaisher/Sun congruence** (R3 bridge, `LnTwoPrimeWindow.lean` docstring):
   `lnTwoNum (p−1) ≡ lcmRange (p−1) · q_p(2) (mod p)` for odd primes.  Route: Fermat little
   theorem manipulations on `Σ 2^k/k` mod p.  Probe-verified for all 2261 primes < 20 000
   (`experiments/lntwo_fermat_bridge.py`) — the statement shape is settled; formalize exactly
   that form.  Turns the R3 door's provenance note into a theorem.
4. **Tier-1 `LnTwoExpSep` via shifted-Legendre** (blueprint §5.6): donor machinery in
   `~/src/collatz-moonshot` `FrontA/Legendre.lean` (re-home with a `Compat.lean` shim if its
   tree churns — never axioms).  Big; only start if 1–3 land with hours remaining.
5. **Machine instantiation, log² 2 or π²** (`KickedOrbit.lean` summed-kick machine): freeze the
   series identity as a CITED node + elementary kick bounds → sliver corollaries via
   `top_sliver_of_zeroRun_kicked`.  Optional dessert.

## Standing rules (non-negotiable)

- **Lane-2 phase-1 tolerances**: deprecation warnings, step boosts allowed; prefer
  `decide +kernel` over `native_decide` (bespoke axiom).  Distribution prep is NOT this
  session's job.
- **ADDITIVE ONLY** 🧊 on everything frozen: never edit/weaken a frozen decl or landed module.
  The two dead `CFScheduleA.lean` sorries (`:4400`, `:5774`) are REFUTED markers — do not touch.
- **Evidence tiers**: after each unit, build green + `#print axioms` on the touched headlines —
  trust triple `[propext, Classical.choice, Quot.sound]` (plus disclosed named hypotheses)
  or revert.  The hedge lives inside the claim.
- **Commit green reflexively** per unit via `git-safe` (bare `git` is hook-blocked; `git stash`
  banned — WIP goes on `wip/<desc>` branches).  Pre-commit runs the build gate.
- **Report crux-advance, never sorry count** — decomposing a fat sorry into named leaves is
  progress even when the count rises.  Lap notes: state-verb headline + ≤2 sentences.
- **No outward actions**: no pushes to remotes you haven't seen this repo routinely push to,
  no PRs, no Zulip, no announcements.  Blocked on something only a human can resolve → write
  `~/personal/claude/knowledge/outbox/2026-08-29-<desc>.md` and move to the next target.

## Ops mechanics

- Treadmill tooling: `lean-treadmill` (+ `lean-treadmill-reaper`), catalog in
  `~/personal/claude/knowledge/core/preferences/helper-scripts.md`, fleet detail in
  `knowledge/core/projects/lean-tooling.md`.  Read those before firing; model/effort = Fable/low.
- Fresh worktree? Run `lake-base status v4.33.1` + `relake plan` BEFORE any `lake build` —
  "Decompressing N file(s)" means you forked a 7 GB tree where a 30 MB CoW clone existed.
  This checkout (`~/src/normal-numbers`) already has a warm `.lake`; building here directly
  is fine.  Concurrent laps must not share files — disjoint targets or separate worktrees.
- Long unattended run: wrap the driver in `caffeinate -i -s`.
- Repo state at handoff: HEAD `dc3a4a6` on `master`, build green (8776 jobs), all headlines
  trust-triple (verified 2026-08-29).  Today's context: `docs/lnTwo-kick-blueprint.md` §5,
  D10–D13 in `~/personal/claude/knowledge/core/projects/normal-numbers.md`.

## Stop condition

Run until targets are exhausted or Trevor returns.  All targets landed or hard-blocked →
final commit, one-paragraph summary at the top of this file (edit in place, mark it
`## RESULT`), self-stop.  Never idle-loop; never report unpushed commits as an open item.
