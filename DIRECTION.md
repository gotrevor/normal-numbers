# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-23, reflection lap)

- **THE objective**: **LOCK TIER 1** — prove `xstar` is **absolutely normal ∧
  CF-normal** (the Becher–Yuhjtman result, first formalization). CF normality is
  DONE (`xstar_cf_freq_tendsto`, axiom-clean). What remains for Tier 1 is the
  **d-ary side**: base-`d` simple normality of `xstar` for every `d ≥ 2`, then
  Pillai, then the stated conjunction. **Khinchin-typical (W6) is Tier 2 — a
  stretch beyond the source paper; do NOT start it until Tier 1 is a proven,
  axiom-clean, stated theorem.**
- **Mandated next move**: attack the d-ary correctness chain in
  `DaryCorrect.lean`, hardest-first. In order:
  (1) **THE CRUX — the `m`-growth estimate** (interior condition, "the only
      genuinely new math left"): per-stage base-`d` digit gain `k_{s+1}(d)` is
      eventually a vanishing fraction of the accumulated count `m_d(s) − m_d(s₀)`.
      Route (from HANDOFF-…-0900 §(c), source-verified this lap): numerator
      `d^{k} ≤ 32d·cfK(u)²` from good-length upper bound + containment;
      denominator `Σ k_j ≳ (log2/(4 log d))·(L_s − L_{s₀})` via
      `two_pow_le_cfK` (`cfK(u_j) ≥ 2^{(n_j−1)/2}`, already proved); ratio
      ≲ goodC·n_{s+1}/L_s → 0 by `sched_dominance`. Decompose into named
      sub-`sorry`s in `DaryCorrect.lean` — that RAISES the src count and IS
      progress.
  (2) **the d-ary chain** → `xstar_dary_freq_tendsto` (digit `c` freq → 1/d):
      MIRROR the proven `xstar_cf_freq_tendsto` skeleton (chain / boundary /
      interior / `exists_stage` locator / metric limit), swapping
      CFDiscLt→HasDiscLt. Lemma 9 (`BaryConcat`: `HasDiscLt.append`,
      `hasDiscLt_append_take`, `hasDiscLt_short_append`) is the CF-chain analogue,
      already proved. Do NOT re-derive the chain machinery — transcribe it.
  (3) **Pillai** (`simple normal to all b^k ⇒ normal to b`) + **the headline
      statement**: stage the conjunction `IsNormal b xstar (∀ b≥2) ∧
      (CF-normal xstar)` for JUDGE to freeze. Pillai is NOT in mathlib/repo —
      formalize it (classical, self-contained). Check `Sandwich`/`Counting`/
      `Wall` for reusable window-frequency pieces first.
- **Forbidden drift**: do NOT re-attack Lemma 13 / the schedule / the measure
  balance / the CF side — ALL PROVED and axiom-clean (the previous directive's
  "route-decisive crux" is closed). Do NOT start W6/Khinchin caps before Tier 1
  is a stated axiom-clean theorem. Do NOT open Track A side-quests. Do NOT pivot
  to ergodicity/Birkhoff (B5′ is Birkhoff-free). Do NOT weaken/reshape any
  JUDGE-frozen statement. Constants: distortion `2`, γ-mixing `(9/10)`, brick
  ratio `1/(2d)`.
- **Why**: the W5 crux the last directive named (the measure-balance selection
  lemma) is proved, and CF normality of the explicit witness `xstar` is proved
  axiom-clean — the campaign is far past "will the route close". The only
  genuinely-new-math obligation left for the source-backed headline is the d-ary
  `m`-growth estimate (item 1); once it lands, the d-ary chain is a
  transcription and Pillai is classical labor. Locking Tier 1 = a complete,
  first-anywhere formalization; Khinchin (Tier 2) is a real research reach that
  revisits the construction and must not be allowed to destabilize a lockable
  Tier-1 result.

### Directive history
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
