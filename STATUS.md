# STATUS — normal-numbers 📊

**Two classical harvests of one Birkhoff-on-[0,1] machine: base-b normality (Track A, DONE) + CF/Khinchin metric theory (Track B, active B5′ expedition).** · **Build**: 🟢 green (8729 jobs) · **Updated**: review lap · 2026-08-23 · `30267a4`

## Where it stands

Track A is **complete and axiom-clean**: Wall's theorem, the ln 2 normality
reduction, and Stoneham's constant (unconditional) are all proved with only the
trust-base triple. Track B's B5′ expedition (the combined absolutely-normal +
CF-normal + Khinchin-typical witness) has cleared its crux: W1/W2/W3 done and
the W4 γ-mixing engine (`gaussMeasure_cylinder_mixing`) proved with a *geometric*
rate — so the efficiency-free (Markov + Chebyshev, no CLT/KPW/Birkhoff) route is
de-risked. `src/` is currently sorry-free. Next frontier: W4 block-frequency
variance/Chebyshev assembly (`CFBlockFreq.lean`), the concrete consumer of the
mixing engine, feeding W5 (construction) and W6 (Khinchin graft).

## What's happened (newest first)

- 2026-08-23 (review lap): certified Track A complete + all 7 headlines
  axiom-clean via `#print axioms`; found ROADMAP stale (Stoneham was 🔨, is
  actually proved as `isNormal_two_stoneham23`); set DIRECTION CURRENT DIRECTIVE
  to the W4 block-frequency Chebyshev assembly; created STATUS/DIRECTION.
- 2026-08-23: W4 groundwork — `CFGammaMixing.lean`: γ-mixing for cylinders
  `|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)γ(A)| ≤ (9/10)^g·4|A|·γ(I_v)` (the KPW
  Lemma-6 substitute, geometric = stronger than planned summable-only).
- 2026-08-23: W3 COMPLETE — `cylinder_mixing` (C = 8 log 2, ρ = 9/10) +
  `gauss_kuzmin` (B4 flag), via CFDensity/CFRecursion/CFInvariance/CFPin.
- 2026-08-23: W3 laps — mean pin (`CFPin`), geometric Lipschitz decay of Gₖ,
  Gauss invariance (`CFInvariance`, B1 flag), transfer-operator recursion,
  conditional density identity, `stepOp_lipschitz` contraction crux.
- 2026-08-23: W2 COMPLETE — `CFDigitLaw.lean`, all 10 statements (digit law,
  partition tsum, Gauss/Lebesgue comparison, Markov E[log qₙ]≤Cn, Fibonacci).
- 2026-08-23: W1 COMPLETE — `CFCylinder.lean`/`CFDefs.lean`, all 12 (continuant
  algebra, distortion Lemma 3, `volume_cfCylinder`, Prop 12).
- 2026-08-22: Track A foundations + headlines — Wall's theorem, ln 2 reduction
  (Bailey–Crandall), Stoneham constant (hot-spot route, HotSpot/Stoneham).

## Outstanding

### Short-term (mirror PENDING_WORK top)
- W4 `CFBlockFreq.lean`: first moment → pair invariance → second moment →
  variance bound (from γ-mixing) → Chebyshev block-frequency bound.
- W4 b-ary side: B–Y Lemmas 8/9 (check Counting.lean/Visits.lean overlap).
- Judge: ratify W4 frozen statement shapes (drafts pending).

### Long-term
- W5: t-bricks, main refinement lemma, schedule, limit x, three correctness
  proofs, Pillai powers-equivalence for "absolutely normal".
- W6: Khinchin graft (digit caps D_t, uniform integrability, K₀ as tprod).

### To completion
- B5′ headline: one explicit witness = absolutely normal + CF-normal +
  Khinchin-typical (apparently first-anywhere even on paper).
- Outward (Track A): PR to ChampernowneNormality (staged, Trevor opens);
  comparator harness + Zulip; normality defs → mathlib.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-23)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `isNormal_log_two_of_equidistributed` | cond (on orbit equidistribution) | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `measurePreserving_gaussMap` (B1) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `cylinder_mixing` (W3 core) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `gauss_kuzmin` (B4) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `gaussMeasure_cylinder_mixing` (W4 γ-mixing) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0**. No 🔴 in any unconditional headline. The ln 2 headline's conditionality
is a hypothesis on the theorem itself (paper-faithful), not a cited axiom.

## Pointers
ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) · JUDGE.md (statement governance) ·
newest HANDOFF-2026-08-23-*.md · PENDING_WORK.md · papers/becher-yuhjtman-*.md
