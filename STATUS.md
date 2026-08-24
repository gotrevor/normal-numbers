# STATUS — normal-numbers 📊

**Two classical harvests of one Birkhoff-on-[0,1] machine: base-b normality (Track A, DONE) + CF/Khinchin metric theory (Track B, active B5′ expedition).** · **Build**: 🟢 green (8743 jobs) · **Updated**: review lap · 2026-08-24 · `eaa3b38`+

## Where it stands

Track A is **complete and axiom-clean**: Wall's theorem, the ln 2 normality
reduction, and Stoneham's constant (unconditional) — trust-triple only.

Track B's B5′ expedition has **cleared W1–W4 AND the W5 crux**. Since the last
review lap the campaign proved, all axiom-clean: **B–Y Lemma 13** (the main
refinement lemma, `TBrick.exists_refinement`/`_uniform`), **THE SCHEDULE**
(`CFSchedule.lean` — brick sequence, promotion rule, dominance `t·n(t) ≤ L`,
levels → ∞), **the limit point `xstar`** (irrational, in every scheduled
cylinder), and **CF normality of `xstar`** (`xstar_cf_freq_tendsto`: for every
genuine pattern `v`, window frequency → γ(I_v)). The measure-balance selection
lemma that the 2026-08-24 directive called the "route-decisive test" is
**proved and consumed** — the route CLOSED.

The d-ary side is now **DONE and axiom-clean**: `xstar_dary_freq_tendsto` —
base-`d` simple normality of `xstar` for every `d ≥ 2` simultaneously — is
proved, the `m`-growth crux and the full d-ary HasDiscLt chain closed. The sole
remaining math obligation is **Pillai's theorem** (`Pillai.lean`; simple
normality to all `b^k` ⇒ full normality to `b`, NOT in mathlib/repo). Its
combinatorial core is now built out and axiom-clean: `phaseWindowFreq_tendsto`
(phase-`s` window frequency → `b^{-L}` from simple normality at `b^r`),
`card_straddling_phases` (`L−1` of `r` phases straddle a boundary, density →0),
and — **this review lap** — `windowCount_eq_sum_phaseCount`, the exact
combinatorial identity converting the `Q`-scale phase counts into `N`-scale real
digit-position counts (the `i ↔ (i/r, i%r)` bijection). **The immediate crux is
now the double-limit assembly** (`N→∞` per phase, then `r→∞`); after it the
Pillai theorem statement + the headline conjunction (`Headline.lean:93,100`)
close Tier 1. **Khinchin-typical (W6) is a stretch beyond the source paper, not
a prerequisite** — see Reflection.

## What's happened (newest first)

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
- 2026-08-23: W4 groundwork — `CFGammaMixing.lean` γ-mixing (geometric, the
  KPW Lemma-6 substitute); W3 COMPLETE — `cylinder_mixing` + `gauss_kuzmin`.
- 2026-08-23: W2 COMPLETE (`CFDigitLaw.lean`, 10 statements) + W1 COMPLETE
  (`CFCylinder.lean`/`CFDefs.lean`, 12 statements).
- 2026-08-22: Track A foundations + headlines — Wall, ln 2 reduction, Stoneham.

## Outstanding

### Short-term (mirror PENDING_WORK top) — FINISH Pillai (DIRECTIVE target)
- **(1) THE crux — the double-limit assembly** (`Pillai.lean`): divide
  `windowCount_eq_sum_phaseCount` by `N`, apply `phaseWindowFreq_tendsto` per
  non-straddling phase as `N→∞` (`phaseOccCount r L s N / N → 1/r`), bound the
  `L−1` straddling phases via `card_straddling_phases`, sum the finite phase
  limits, then `r→∞` (ε-managed, simpler than `xstar_dary_freq_tendsto`'s metric
  proof — arithmetic-progression decomposition, no schedule machinery).
- **(2) State + prove Pillai's theorem**: `∀ r≥1, SimplyNormalAt (b^r) y ⇒
  IsNormalSequence b (digitOf b y)`; short bridge from `countOccurrences` to the
  filter-based window count.
- **(3) Headline conjunction** (`Headline.lean:93,100`): wire Pillai +
  `xstar_dary_freq_tendsto` (abs-normal) and `xstar_cf_freq_tendsto` (CF).

### Long-term
- **W6 Khinchin graft** (Tier-2 stretch): digit caps `D_t` in Def 11, uniform
  integrability, K₀ as tprod. Original even on paper (~90%); revisits the
  construction, so do it AFTER Tier 1 is locked.

### To completion
- Tier 1 (source-backed): `xstar` = absolutely normal ∧ CF-normal — first
  formalization of the Becher–Yuhjtman witness.
- Tier 2 (stretch): + Khinchin-typical — apparently first-anywhere even on paper.
- Outward (Track A): PR to ChampernowneNormality (staged); comparator + Zulip.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-24)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `cylinder_mixing` (W3) | uncond | trust triple | 🟢 DONE |
| `gauss_kuzmin` (B4) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_cylinder_mixing` (W4 γ-mixing) | uncond | trust triple | 🟢 DONE |
| `chebyshev_blockCount` (W4 Chebyshev) | uncond | trust triple | 🟢 DONE |
| `xstar_irrational` (W5 limit point) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (**CF normality of x\***) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (**d-ary simple normality, every base**) | uncond | trust triple | 🟢 DONE |
| `windowCount_eq_sum_phaseCount` (Pillai count identity) | uncond | trust triple | 🟢 DONE (this lap) |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0**. No 🔴 in any unconditional headline. Trust triple = propext,
Classical.choice, Quot.sound throughout. The Tier-1 headline conjunction
(abs-normal ∧ CF-normal for `xstar`) is **not yet stated** — it is the d-ary +
Pillai destination; when stated it must be trust-triple-only (both of B–Y's
deep imports are already discharged into proved elementary lemmas, and the CF
leg is already proved axiom-clean).

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF-2026-08-26-0100.md ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
