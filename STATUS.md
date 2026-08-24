# STATUS — normal-numbers 📊

**Two classical harvests of one Birkhoff-on-[0,1] machine: base-b normality (Track A, DONE) + CF/Khinchin metric theory (Track B — Tier 1 LOCKED, Tier 2 Khinchin in progress).** · **Build**: 🟢 green (8735 jobs) · **Updated**: review lap · 2026-08-24 · `fc801ba`+

## Where it stands

Track A **complete and axiom-clean** (Wall, ln 2 reduction, Stoneham,
trust-triple only). **Tier 1 — the Becher–Yuhjtman theorem — is LOCKED**:
`exists_absolutely_normal_cf_normal` (`Headline.lean:109`) is proved and
axiom-clean (trust triple), apparently the first formalization in any prover.
Everything under it (Pillai, the d-ary chain, CF normality, the measure-balance
selection / Lemma 13, the schedule, `xstar`) is DONE and axiom-clean.

**Tier 2 — the expedition headline `exists_absolutely_normal_cf_normal_khinchin`
(`Headline.lean:134`, `sorry`)** — is the sole remaining obligation:
additionally Khinchin-typical. Via `khinchinTypical_iff_log_tendsto` (proved) it
reduces to the one crux `xstar_log_digit_avg_tendsto` (`Khinchin.lean`, `sorry`):
`(1/n)·Σ_{i<n} log aᵢ → log K₀`. **The route is now settled** (this review lap):
frequencies + the `goodC` total-mass bound provably do NOT suffice (the
`44fb8bb` "goodC suffices" insight is REFUTED); the ergodic-theorem route is a
forbidden import; the only viable route is the original `KHINCHIN.md` W6 plan —
a Khinchin log-concentration **bad zone** added *additively* to the schedule's
union-bound selection, its measure small by a Chebyshev/variance bound under the
existing γ-mixing machinery. The `DIRECTION.md` fence was relaxed accordingly
(additive-only; Tier-1 stays byte-identical/axiom-clean). The moment seed for
the variance bound, `summable_gaussKuzmin_logsq` (`E[(log a₁)²]<∞`), is proved
this lap. Prior "operator-gated, stop" conclusion overturned — it was a false
stop on an autonomous run.

## What's happened (newest first)

- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence relaxed, moment
  seed proved.** Broke the 3-lap "operator-gated" stall (fc801ba/17dc2c9/7d6740f
  were pure route-analysis ending in a false "need operator" stop). Confirmed the
  only route is the additive W6 log-concentration bad zone; relaxed the
  `DIRECTION.md` "don't touch the schedule" fence to additive-only with a
  Tier-1-axiom invariant. Proved `summable_gaussKuzmin_logsq` (moment condition
  `E[(log a₁)²]<∞`, axiom-clean) — the analytic seed of the Chebyshev bad-zone
  bound. Re-verified Tier 1 axiom-clean (trust triple), build green (8735 jobs).
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

### Short-term (mirror PENDING_WORK top) — BUILD the Khinchin concentration zone (DIRECTIVE target)
- **(1) Moment condition** `E[(log a₁)²] = Σₐ γ([a])·(log a)² < ∞` —
  `summable_gaussKuzmin_logsq` (`Khinchin.lean`) — **DONE this lap, axiom-clean.**
- **(2) Variance bound** `Var(Σ_{i<n} log aᵢ) ≤ C·n` under the existing γ-mixing
  machinery (`CFGammaMixing`/`CFBlockFreq`) with observable `log a₁` — mirror
  `cfBadZone`'s Chebyshev treatment for an unbounded L² observable. NEW file,
  no TBrick edit yet.
- **(3) `logBadZone` + measure bound** `≤ C/(η²n)` (Chebyshev), then thread it
  **additively** through the union bound (new `exists_good_avoiding_bad_khinchin`
  /`exists_refinement_uniform_khinchin`, coeff budget re-balanced to 3 zones).
- **(4) Elementary reduction** (parallel, in `Khinchin.lean`): the 3ε assembly of
  `xstar_log_digit_avg_truncated_tendsto` + tail control + value-count identity
  into `xstar_log_digit_avg_tendsto`; then `khinchinTypical_iff_log_tendsto`
  closes `Headline.lean:134`.

### Long-term
- Tier-2 witness: either a schedule parameterized by the bad-zone family, or a
  fresh witness through the extended refinement (still abs-normal ∧ CF-normal —
  it avoids a superset of zones). Additive only; Tier-1 axioms invariant.

### To completion
- Tier 1 (source-backed): **DONE** — `exists_absolutely_normal_cf_normal`, first
  formalization of the Becher–Yuhjtman witness, axiom-clean.
- Tier 2 (stretch): + Khinchin-typical — apparently first-anywhere even on paper;
  the sole open obligation.
- Outward (Track A): PR to ChampernowneNormality (staged); comparator + Zulip.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-24)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (locked, first formalization) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | `sorryAx` (open) | 🟡 in progress — crux `xstar_log_digit_avg_tendsto`; route = additive W6 concentration zone |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE (this lap) |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms; the only non-green item is the Tier-2 headline
itself, still `sorry` (route settled, in progress — 🟡). No 🔴 anywhere. Trust
triple = propext, Classical.choice, Quot.sound throughout. Tier 1's `#print
axioms` re-verified trust-triple-only this lap; the invariant for all W6 work is
that it STAYS trust-triple (any change = locked machinery was modified).

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
