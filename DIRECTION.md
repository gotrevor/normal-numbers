# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-24, review lap)

- **THE objective**: **LOCK TIER 1** — prove `xstar` is **absolutely normal ∧
  CF-normal** (Becher–Yuhjtman, first formalization). CF normality DONE
  (`xstar_cf_freq_tendsto`). d-ary simple normality at every base DONE
  (`xstar_dary_freq_tendsto`, axiom-clean). The whole d-ary correctness chain +
  the `m`-growth crux the LAST directive named are **CLOSED**. The sole remaining
  math obligation is **Pillai's theorem** (`Pillai.lean`), then the headline
  conjunction (`Headline.lean:93,100`). **Khinchin-typical (W6) is Tier 2 —
  do NOT start it until Tier 1 is a proven, axiom-clean, stated theorem.**
- **Mandated next move**: FINISH Pillai in `Pillai.lean`, hardest-first, in this
  order (all leaves feed the one headline; the analytic crux is (1)):
  (1) **THE CRUX — the double-limit assembly**: divide
      `windowCount_eq_sum_phaseCount` (PROVED this lap, axiom-clean) by `N`,
      apply `phaseWindowFreq_tendsto` per non-straddling phase (`s ≤ r−L`) as
      `N→∞` (each `phaseOccCount r L s N / N → 1/r`), bound the `L−1` straddling
      phases via `card_straddling_phases`, sum the finite phase-limits, then let
      `r→∞` (ε-managed, style of `xstar_dary_freq_tendsto`'s
      `Metric.tendsto_atTop` but simpler — arithmetic-progression decomposition,
      no schedule machinery). Decompose into named sub-`sorry`s if it doesn't
      close in one lap — that RAISES the src count and IS progress.
  (2) **State + prove Pillai's theorem**: hypothesis `∀ r ≥ 1,
      SimplyNormalAt (b^r) y` (check for an existing equivalent def before adding
      one), conclusion `IsNormalSequence b (digitOf b y)`. Needs a short bridge
      from `IsNormalSequence`'s `countOccurrences` (`l.tails.countP …`) to the
      filter-based window count — via `List.isPrefixOf_iff_prefix` +
      `List.prefix_iff_eq_take` + `List.getElem_tails`.
  (3) **Headline conjunction** (`Headline.lean:93,100`): discharge
      `exists_absolutely_normal_cf_normal` from Pillai +
      `xstar_dary_freq_tendsto` (abs-normal leg) and `xstar_cf_freq_tendsto`
      (CF leg, a wrapper per the JUDGE addendum).
- **Forbidden drift**: do NOT re-attack the d-ary chain / `m`-growth estimate /
  Lemma 13 / the schedule / the measure balance / the CF side — ALL PROVED and
  axiom-clean. Do NOT re-prove `windowCount_eq_sum_phaseCount`,
  `phaseWindowFreq_tendsto`, or `card_straddling_phases` — DONE this lap. Do NOT
  start W6/Khinchin caps before Tier 1 is a stated axiom-clean theorem. Do NOT
  open Track A side-quests. Do NOT pivot to ergodicity/Birkhoff. Do NOT
  weaken/reshape any JUDGE-frozen statement. Constants: distortion `2`, γ-mixing
  `(9/10)`, brick ratio `1/(2d)`.
- **Why**: every genuinely-new-math obligation for the source-backed headline is
  now discharged — CF normality, d-ary simple normality at every base, and (this
  lap) the Pillai window/phase count identity `windowCount_eq_sum_phaseCount`.
  What remains is the double-limit ANALYSIS (item 1, the real crux: a Cesàro /
  arithmetic-progression limit interchange) plus classical statement labor. Once
  Pillai closes, the headline conjunction is a wiring of two proven `Tendsto`
  results. Locking Tier 1 = a complete, first-anywhere formalization; Khinchin
  (Tier 2) must not destabilize a lockable Tier-1 result.

### Directive history
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
