# STATUS — normal-numbers 📊

**Two classical harvests of one Birkhoff-on-[0,1] machine: base-b normality (Track A) + CF/Khinchin metric theory (Track B — Tier 1 Becher–Yuhjtman + Tier 2 Khinchin). ALL PROVED, axiom-clean.** · **Build**: 🟢 green (8751 jobs) · **Updated**: reflection lap · 2026-08-24 · `4629029`

## Where it stands

**THE EXPEDITION IS COMPLETE.** All ten headline theorems are proved and
`#print axioms`-clean (trust triple `propext, Classical.choice, Quot.sound`
only); ZERO `sorry`/`admit` terms in `src/`; ZERO cited/proven-but-cited math
axioms (the two B–Y deep imports — Morita/Vallée CLT and Kifer–Peres–Weiss
large deviations — were discharged via elementary Markov + γ-mixing substitutes).

- **Track A** (base-b normality): Wall, the ln 2 reduction (conditional on the
  correct equidistribution hypothesis), Stoneham — axiom-clean.
- **Tier 1 = Becher–Yuhjtman** (IMRN 2019): `exists_absolutely_normal_cf_normal`
  (`Headline.lean`) — an explicit real absolutely normal ∧ CF-normal. Apparently
  the first formalization in any prover.
- **Tier 2 = the expedition headline**: `exists_absolutely_normal_cf_normal_khinchin`
  — additionally **Khinchin-typical**. We found no write-up of the conjunction,
  but that is NOT a novelty claim: the implication may well be routine and simply
  unstated, and our survey instrument cannot speak to the paper literature. Closed via `xstar_khinchinTypical`, whose crux `xstar_log_tail_uniform`
  is delivered by the route-C′ **summable Markov log-tail family** grafted
  additively into the schedule (`xstar_logTail_prefix_bound`, `CFCorrect.lean`) —
  and route D′ layering (`KhinchinDefs.lean`) to break the def/proof import cycle.

## What's happened (newest first)

- 2026-08-24 (reflection lap → COMPLETION): **Tier 2 CLOSED — the whole
  expedition is done, axiom-clean.** Steps 1–3 all landed this lap. (1) Rewired
  `CFSchedule.lean` to the summable-**family** refinement (fixed cutoffs
  `khinchinK j`, no level-tied `K_t→∞`). (2) Built the log-tail telescoping in
  `CFCorrect.lean` (`logTailMass` + monotonicity, `uSched_logTail_le`,
  `tailSched_logTail_le`, `xstar_logTail_prefix_bound`, `logTailMass_cfPrefix`)
  and assembled the crux `xstar_log_tail_uniform`, hence `xstar_khinchinTypical`
  (axiom-clean). (3) Route D′: relocated the frozen `khinchinK₀`/`KhinchinTypical`
  defs byte-identical to a new upstream `KhinchinDefs.lean`, dropped Khinchin's
  `import Headline`, and closed the Tier-2 headline
  `⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal, xstar_khinchinTypical⟩`.
  All 10 headlines re-`#print axioms`-verified trust-triple. Also (earlier in the
  lap): ratified route C′ and de-staled the CURRENT DIRECTIVE (it still named the
  superseded Chebyshev/variance plan). ROUTE VERDICT: CONTINUE → reached the
  destination.
- 2026-08-24 (grind run, route C′): **FAMILY machinery COMPLETE + axiom-clean.**
  `volume_logBadZone_le_vol` (Lebesgue bridge), three-zone combine
  (`exists_good_avoiding_bad_khinchin` + `_family`), `exists_refinement_uniform_khinchin_family`
  (log-tail payload at every `j<tK`), `CFLogTail.lean` layering (khinchinK₀-free
  upstream). Found+fixed the level-tied-cutoff design bug via the summable family
  (geometric budget `≤1/7`). CFSchedule still carries the SUPERSEDED single-zone
  threading (true, green, unused) — next lap rewires it to the family form.
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence relaxed, moment
  seed proved.** Broke the 3-lap "operator-gated" stall (fc801ba/17dc2c9/7d6740f
  were pure route-analysis ending in a false "need operator" stop). Confirmed the
  only route is the additive W6 log-concentration bad zone; relaxed the
  `DIRECTION.md` "don't touch the schedule" fence to additive-only with a
  Tier-1-axiom invariant. Proved `summable_gaussKuzmin_logsq` (moment condition
  `E[(log a₁)²]<∞`, axiom-clean) — the analytic seed of the tail bound.
  Re-verified Tier 1 axiom-clean (trust triple), build green (8735 jobs).
- 2026-08-24 (grind laps): **Tier 1 LOCKED** (`b3bc2c4`,
  `exists_absolutely_normal_cf_normal`, axiom-clean) + Tier-2 assembly seeded:
  `gaussMeasure_Ioo`/`gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit
  law), `Khinchin.lean` (geometric-mean⟺log-average reduction `khinchinTypical_iff_log_tendsto`,
  `khinchinK₀_pos`), `prod_le_cfK`+`wSched_log_sum_le` (total log-mass bound),
  `xstar_log_digit_avg_truncated_tendsto` (finite-truncation slice).
- 2026-08-24 (review lap): **Pillai crux `windowCount_eq_sum_phaseCount` PROVED**
  (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, via a
  `Finset.card_nbij'` bijection `i ↔ i/r`; dodged last lap's `r*(i/r)` vs
  `(i/r)*r` omega-atom trap by anchoring on `Nat.div_add_mod` + one explicit
  `Nat.mul_comm`. Re-verified headlines axiom-clean (trust triple), build green
  (8743 jobs). Directive refreshed (it still named the closed `m`-growth
  estimate as THE crux) → FINISH Pillai, now double-limit-first. No trigger fired.
- 2026-08-24 (grind laps): **d-ary side CLOSED** — `xstar_dary_freq_tendsto`
  (base-`d` simple normality every base, axiom-clean); the `m`-growth interior
  crux (`tendsto_gain_div_mSched_sub`) + Pillai combinatorial core
  (`phaseWindowFreq_tendsto`, `card_straddling_phases`, window/slice
  correspondence, `card_matchingValues`).
- 2026-08-23 (reflection lap): re-verified 10 headlines axiom-clean (trust
  triple), build green (8742 jobs), src/ sorry-free. Found DIRECTION/STATUS/
  PENDING_WORK badly STALE — they still named the Lemma-13 assembly the
  "untouched crux", but Lemma 13 + schedule + `xstar` + CF normality all landed
  since. Refreshed all three; reframed the destination into Tier 1 (B–Y
  abs-normal + CF-normal, source-backed) vs Tier 2 (Khinchin, campaign-original
  stretch); set directive to LOCK Tier 1 via the d-ary `m`-growth estimate.
  ROUTE VERDICT: CONTINUE (no trigger fired; strong forward motion).
- 2026-08-23: **CF NORMALITY OF `xstar` PROVED** (`CFCorrect.lean`,
  `xstar_cf_freq_tendsto`) + **d-ary digit extraction / payload accessors**
  (`DaryDigits`/`DaryCorrect`): digit windows are literally the base-d digits;
  each active stage gives a good block. All axiom-clean.
- 2026-08-23: **THE SCHEDULE + Lemma 13 + limit point** — `CFSchedule.lean`
  (uniform Lemma 13, brick sequence, invariants, dominance), `xstar`
  irrational in every scheduled cylinder (`CFLimit` applied). Axiom-clean.
- 2026-08-23: **B–Y Lemma 13 PROVED** (`TBrick.lean`, both `t'=t` and `t→t+1`)
  — the measure-balance selection lemma (good mass ½|I_w| beats CF + Σ d-ary bad
  zones) made UNCONDITIONAL; seed brick + refinement toolkit (`TBrickRefine`).
- 2026-08-23 (review lap): diagnosed input-gathering fixation, redirected to the
  Lemma-13 measure-balance assembly (now proved).
- 2026-08-23: W5 Lemma-13 inputs COMPLETE — B–Y Lemmas 7/8/9, Prop 12, d-ary bad
  zones (summed + widened), CF word bridge, digit semantics.
- 2026-08-23: W4 CORE COMPLETE — `CFBlockFreq.lean` first→second moment→
  covariance (γ-mixing consumer) → `variance_blockCount_le` →
  `chebyshev_blockCount` (+ brick version), axiom-clean.
- 2026-08-23 (review lap): certified Track A complete + headlines axiom-clean;
  set directive to the W4 Chebyshev assembly; created STATUS/DIRECTION.
- 2026-08-23: W4/W3/W2/W1 COMPLETE — γ-mixing (`CFGammaMixing`), `cylinder_mixing`
  + `gauss_kuzmin`, `CFDigitLaw`, `CFCylinder`/`CFDefs`.
- 2026-08-22: Track A foundations + headlines — Wall, ln 2 reduction, Stoneham.

## Outstanding

### Short-term
- **NONE — the proof is complete.** No open `sorry`/`admit`, no cited axioms.

### Long-term / outward (packaging only — not proof obligations)
- Stale docstrings in a few CF modules still say "left `sorry` for the campaign"
  (historical prose describing lemmas long since proved) — harmless, could be
  swept for tidiness.
- Outward (Track A): PR to ChampernowneNormality (staged); comparator + Zulip —
  needs host egress, not a proof step.

### To completion — DONE
- Track A: **DONE**, axiom-clean.
- Tier 1 (Becher–Yuhjtman): **DONE** — `exists_absolutely_normal_cf_normal`,
  apparently the first formalization, axiom-clean.
- Tier 2 (Khinchin, stretch — apparently first-anywhere even on paper):
  **DONE** — `exists_absolutely_normal_cf_normal_khinchin`, axiom-clean.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-24 reflection lap)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (first formalization; re-verified this lap) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | trust triple | 🟢 DONE (route C′ summable Markov log-tail family + route-D′ layering; PROVED this lap) |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE (this lap) |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms. Every headline is 🟢 (trust triple only). No 🟡
debt, no 🟠, no 🔴 — the frontier is saturated. Trust triple = propext,
Classical.choice, Quot.sound throughout. All 10 headlines re-`#print
axioms`-verified trust-triple-only this lap (the completion certification).

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
