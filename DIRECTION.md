# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-24, review lap — route SETTLED, fence relaxed)

- **TIER 1 IS LOCKED**: `exists_absolutely_normal_cf_normal` (Becher–Yuhjtman,
  IMRN 2019, apparently first formalization) is **proved and axiom-clean**
  (`propext, Classical.choice, Quot.sound` only) — `Headline.lean:109`
  (re-verified this lap). Do NOT reopen or MODIFY any of it.
- **THE objective now**: **Tier 2 — Khinchin-typical (W6)**, the frozen headline
  `exists_absolutely_normal_cf_normal_khinchin` (`Headline.lean:134`, `sorry`):
  a real that is absolutely normal ∧ CF-normal ∧ Khinchin-typical. Reduces (via
  `khinchinTypical_iff_log_tendsto`, proved) to `xstar_log_digit_avg_tendsto`
  (`Khinchin.lean`, the sole crux `sorry`): `(1/n)·Σ_{i<n} log aᵢ → log K₀`.
- **ROUTE — settled, no longer an open question**: the last 3 laps (route-analysis)
  established, and this review ratifies: pattern-frequency data + the total-mass
  bound `wSched_log_sum_le` (`Σ log aᵢ ≤ goodC·n`) do **NOT** suffice — the
  `44fb8bb`/`e018429` "goodC suffices" insight is **REFUTED** (quantitative:
  `limsup(1/n)Σ_{aᵢ>K} log aᵢ ≤ goodC − log K₀ > 0`, and `KHINCHIN.md`'s
  large-digit-planting counterexample kills frequencies-only). The ergodic-theorem
  route (Birkhoff for the Gauss map) is a charter-forbidden import (trigger b).
  The ONLY viable route is the **original `KHINCHIN.md` W6 plan**: enforce
  uniform tail control *in the construction* via a Khinchin log-concentration
  bad zone.
- **Mandated next move — BUILD the concentration bad zone, ADDITIVELY**:
  1. `summable_gaussKuzmin_logsq` — moment condition `E[(log a₁)²]<∞` — DONE
     this lap (`Khinchin.lean`, axiom-clean).
  2. Variance bound `Var(Σ_{i<n} log aᵢ) ≤ C·n` under the existing γ-mixing
     machinery (`CFGammaMixing`/`CFBlockFreq`), with observable `log a₁` in place
     of a cylinder indicator — mirror `cfBadZone`'s Chebyshev treatment.
  3. `logBadZone w n η := {x | |Σ_{i<n} log(digit_i x) − n·log K₀| ≥ η·n}`;
     Chebyshev ⇒ its cylinder-relative measure `≤ C/(η²n)` — small.
  4. Thread it through the union bound **additively**: a new
     `exists_good_avoiding_bad_khinchin` / `exists_refinement_uniform_khinchin`
     that unions this ONE extra zone (re-balance the coeff budget: three zones
     each `<1/6` in `exists_mem_notMem_union_of_bounds`), returning everything
     the Tier-1 version does PLUS the log-sum guarantee. Then a witness (new or a
     schedule parameterized by the bad-zone family) that is abs-normal ∧ CF-normal
     (unchanged proofs — it avoids a SUPERSET of zones) ∧ has `(1/n)Σ log aᵢ →
     log K₀`, closing the headline.
  Start with steps 2–3 (analytic, developable in a NEW file, no TBrick edit yet);
  do the invasive step-4 plumbing only once 2–3 are solid. Elementary reduction
  (the 3ε assembly of truncated-convergence + tail-control into
  `xstar_log_digit_avg_tendsto`) can be wired in `Khinchin.lean` in parallel and
  reduces the crux to a single clean tail-control lemma.
- **Fence (REVISED — this is the sticky change)**: additive extension of the
  schedule/refinement machinery (`TBrick.lean`, `TBrickRefine.lean`,
  `CFSchedule.lean`) **IS authorized** for the W6 graft — the prior "do NOT touch
  the schedule" was over-broad (its purpose is protecting locked Tier-1, which an
  additive lemma does not threaten; the JUDGE froze witness-existence form
  precisely to allow a W6 rebuild). **Hard invariant**: NEVER edit/weaken an
  existing Tier-1 declaration or any JUDGE-frozen statement (`IsAbsolutelyNormal`,
  `IsCFNormal`, `khinchinK₀`, `KhinchinTypical`, both headlines). After ANY
  TBrick/schedule edit, re-run `#print axioms exists_absolutely_normal_cf_normal`
  and confirm it stays `[propext, Classical.choice, Quot.sound]` — a change there
  means you modified locked machinery; revert and make it purely additive.
  Constants: distortion `2`, γ-mixing `(9/10)`, brick ratio `1/(2d)`.
- **Why**: the "operator-gated, cannot proceed" conclusion the grind laps reached
  is a false stop — there is no operator (autonomous run), the extension is
  additive/tractable/multi-lap, and it is exactly the source-backed W6 plan.
  Descoping Tier 2 to "Tier 1 is the deliverable" would be miscalibrated caution;
  the expedition headline (the conjunction, apparently new even on paper) stays
  the destination and is now unblocked.

### Directive history
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence RELAXED.** Last
  3 laps (fc801ba/17dc2c9/7d6740f) diagnosed the step-2 crux as "operator-gated"
  and stopped — a false stop (no operator on an autonomous run). Ratified the
  "goodC total-mass suffices" insight as REFUTED; confirmed the only route is the
  original W6 log-concentration bad zone, which is ADDITIVE (Tier-1 stays
  byte-identical/axiom-clean) so the prior "don't touch the schedule" fence is
  relaxed to "additive only, never modify locked decls." Proved the moment seed
  `summable_gaussKuzmin_logsq` (`E[(log a₁)²]<∞`). No charter route trigger fired
  (route needs Chebyshev/γ-mixing, not a forbidden Birkhoff import).
- 2026-08-26 (review lap): **Tier 1 LOCKED** — `exists_absolutely_normal_cf_normal`
  proved, axiom-clean (Pillai + xstar_dary_freq_tendsto + xstar_cf_freq_tendsto
  wired via a List.count/Finset.filter bridge lemma). Redirected to Tier 2
  (Khinchin-typical, W6), now unfenced. No route trigger fired (Tier 1 closed
  clean on the first attempt this lap).
- 2026-08-24 (review lap): d-ary chain + `m`-growth crux + Pillai window/phase
  count identity (`windowCount_eq_sum_phaseCount`) ALL closed & axiom-clean since
  last directive. Refreshed the stale directive (it still named the closed
  `m`-growth estimate as THE crux). Redirected to FINISH Pillai: the double-limit
  assembly (new crux), then the theorem statement, then the headline. No route
  trigger fired (whole-lemma targets closing fast; finishability improving).
- 2026-08-23 (review lap): Track A certified complete + axiom-clean; kept Track
  B / B5′ direction; sharpened next move to the W4 block-frequency Chebyshev
  assembly (`CFBlockFreq.lean`). No route trigger fired.
- 2026-08-24 (review lap): W4 + ALL Lemma-13 inputs certified proved & axiom-
  clean (8 headlines trust-triple only, 8735 jobs green). Diagnosed input-
  gathering fixation: crux (Lemma 13 assembly) untouched for ~10 laps. Redirected
  from "prove inputs" to "ATTACK the measure-balance selection lemma" — the
  route-decisive test. No route trigger fired (both deep imports discharged).
- 2026-08-23 (reflection lap): the measure-balance crux CLOSED — Lemma 13 +
  schedule + `xstar` + CF normality (`xstar_cf_freq_tendsto`) all proved
  axiom-clean since. ROUTE VERDICT: CONTINUE (no trigger fired; whole-lemma
  targets closing fast, finishability IMPROVED). Refreshed the stale directive
  (it still named the closed crux). Reframed destination: Tier 1 = B–Y
  abs-normal + CF-normal (source-backed, lockable) vs Tier 2 = + Khinchin
  (campaign-original stretch). Redirected to the d-ary side, hardest-first at
  the `m`-growth estimate; Khinchin fenced off until Tier 1 is stated + proven.

## JUDGE addendum (2026-08-23, post-kill judge pass) ⚖️

- Directive item (3)'s "stage the conjunction for JUDGE to freeze" is **DONE —
  by the judge, in `src/NormalNumbers/Headline.lean`**: frozen defs
  (`IsAbsolutelyNormal`, `IsCFNormal`, `khinchinK₀`, `KhinchinTypical`) + two
  frozen ∃-form statements — Tier 1 `exists_absolutely_normal_cf_normal`
  (B–Y) and Tier 2 `exists_absolutely_normal_cf_normal_khinchin` (the
  expedition headline).  **Deliberately witness-existence form** (does not
  name `xstar`), so a W6 capped rebuild discharges the same statements.
  Laps prove TOWARD these; do not restate or duplicate them.
- The Tier-1/Tier-2 framing is ratified **as sequencing, not descoping**:
  Tier 2 stays the expedition destination (its sorry now holds the
  self-stop gate open); the directive's W6 fence until Tier 1 is locked
  stands.
- `IsCFNormal` is the general-`x` form of the proven `xstar_cf_freq_tendsto`
  shape; discharging Tier 1's CF conjunct from it should be a wrapper, not
  new math.  `IsAbsolutelyNormal` is Track A's FULL `IsNormal` — the
  Pillai (or direct-blocks) obligation is unchanged.

### JUDGE note on the Tier-2 route question (2026-08-23) ⚖️

The directive's route-decisive question — "can `KhinchinTypical xstar` be
derived from already-proved frequency data alone?" — has a **known NO in
general**: `KHINCHIN.md` §"Both expansions at once" holds the
counterexample (planting digit `⌈e^{2^j}⌉` at position `2^j` is a
density-zero change that preserves EVERY pattern frequency yet breaks the
geometric mean).  Pattern frequencies can never suffice as a formal
implication; the missing ingredient is **large-digit tail control /
uniform integrability of `log a`**.  So the honest fork is: (a) find a
digit-size/tail-mass bound already implicit in the schedule's good-block
selection (the `uSched_log_sum_le`-style log-sum telescopes are the right
family), or (b) the W6 digit-cap re-plumb per `KHINCHIN.md` W6.  Do not
spend laps attempting the frequencies-only derivation.

## Standing charter (destination)

Two classical harvests of one machine — Birkhoff-on-[0,1] applied to two
digit-reading dynamical systems:

- **Track A — base-b normality** (✅ COMPLETE, axiom-clean): Wall's theorem
  (`isNormal_iff_equidistributed_orbit`), the ln 2 reduction
  (`isNormal_log_two_of_equidistributed`), Stoneham's constant unconditional
  (`isNormal_two_stoneham23`).
- **Track B — CF metric theory / Khinchin** (🔨 active): the B5′ expedition
  (W1–W6, plan in `KHINCHIN.md`). **Tier 1 (source-backed, lockable)** =
  `xstar` absolutely normal ∧ CF-normal (Becher–Yuhjtman, first formalization).
  **Tier 2 (stretch, original even on paper)** = + Khinchin-typical (W6 graft).
  W1✅ W2✅ W3✅ W4✅ + W5 core ✅ (Lemma 13, schedule, `xstar`, CF normality —
  all axiom-clean). Remaining Tier 1: d-ary simple normality + Pillai + stated
  conjunction. Governance: statement freezing is JUDGE-owned (`JUDGE.md`);
  grind laps prove frozen statements and add intermediate lemmas.

Route-level abort/escalate triggers: (a) γ-mixing rate collapses below summable
→ escalate (would break W4/W5); NOT fired (geometric proven). (b) W5/W6 needs a
deep import the charter forbids (CLT/KPW/Birkhoff) → escalate; not yet reached.
