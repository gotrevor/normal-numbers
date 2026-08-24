# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-26, review lap)

- **TIER 1 IS LOCKED**: `exists_absolutely_normal_cf_normal` (Becher–Yuhjtman,
  IMRN 2019, apparently first formalization) is **proved and axiom-clean**
  (`propext, Classical.choice, Quot.sound` only) — `Headline.lean:109`. Pillai's
  theorem, the double-limit crux, CF normality, and d-ary simple normality at
  every base are all DONE. Do NOT reopen any of this.
- **THE objective now**: **Tier 2 — Khinchin-typical (W6)**, the expedition
  headline `exists_absolutely_normal_cf_normal_khinchin` (`Headline.lean:134`,
  still `sorry`): additionally show the geometric mean of `xstar`'s CF digits
  tends to `khinchinK₀`. This is fenced no longer — Tier 1 is locked, so W6 may
  start.
- **Mandated next move**: read `KHINCHIN.md` / `KhinchinTypical`'s definition
  (`Headline.lean:82`) and survey what W6 needs: does `xstar`'s existing CF
  digit-frequency data (`xstar_cf_freq_tendsto`, the Gauss-measure cylinder
  frequencies) already pin down the geometric-mean limit via a
  SMB/ergodic-theorem-style argument, or does it need a genuinely new estimate
  (a digit-cap re-plumb of the schedule, per the Headline.lean module doc's
  "any future digit-cap re-plumbing for the Khinchin graft")? Determine the
  route-decisive question first: can `KhinchinTypical xstar` be derived from
  already-proved frequency data alone, or does the `xstar` construction need to
  change? Don't guess — read the source math (Khinchin's own proof of his
  constant theorem uses the ergodic theorem for the Gauss map; check whether
  our `gaussMeasure`/`cfCylinder` machinery already has an ergodicity result to
  reuse before building one from scratch).
- **Forbidden drift**: do NOT re-attack Tier 1 (Pillai, d-ary chain, CF
  normality, the measure balance, Lemma 13, the schedule) — ALL PROVED and
  axiom-clean, `exists_absolutely_normal_cf_normal` is a locked theorem. Do NOT
  weaken/reshape any JUDGE-frozen statement (`IsAbsolutelyNormal`, `IsCFNormal`,
  `khinchinK₀`, `KhinchinTypical`, or the two headline statements themselves).
  Constants: distortion `2`, γ-mixing `(9/10)`, brick ratio `1/(2d)`.
- **Why**: Tier 1 was the entire prior directive's target and is now a stated,
  kernel-checked, axiom-clean theorem — first formalization of Becher–Yuhjtman
  in any prover. The expedition's actual headline (Tier 2, Khinchin-typicality
  conjoined with absolute+CF normality, "apparently new even on paper") is the
  only remaining source-backed obligation; nothing else in the repo blocks it.

### Directive history
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
