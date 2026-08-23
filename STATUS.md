# STATUS — normal-numbers 📊

**Two classical harvests of one Birkhoff-on-[0,1] machine: base-b normality (Track A, DONE) + CF/Khinchin metric theory (Track B, active B5′ expedition).** · **Build**: 🟢 green (8735 jobs) · **Updated**: review lap · 2026-08-24 · `60a058b`

## Where it stands

Track A is **complete and axiom-clean**: Wall's theorem, the ln 2 normality
reduction, and Stoneham's constant (unconditional) are all proved with only the
trust-base triple. Track B's B5′ expedition has cleared W1–W4 AND every input to
the main refinement lemma: the γ-mixing engine, the block-frequency Chebyshev
bound (`chebyshev_blockCount`/`_brick`, the KPW-Lemma-6 substitute), B–Y Lemmas
7/8/9, Prop 12, the d-ary bad zones (+ summed/widened), the CF word bridge and
digit semantics. **Both of B–Y's deep imports are now discharged into proved
elementary machinery.** `src/` is sorry-free. The remaining crux is the
**assembly of B–Y Lemma 13** (W5, `TBrick*.lean`): the route-decisive step is the
measure-balance selection lemma — good mass (≥ ½|I_w|) beats CF + Σ_{d≤t} d-ary
bad zones for n large, under the repo's non-uniform-length Lemma-5 substitute
(per-J m_d route, unverified). Everything downstream (schedule, limit x,
correctness, Khinchin graft) is bookkeeping on top of Lemma 13.

## What's happened (newest first)

- 2026-08-24 (review lap): re-verified 8 headlines axiom-clean (trust triple),
  build green (8735 jobs), src/ sorry-free. Diagnosed input-gathering fixation —
  Lemma 13's inputs all proved over ~10 laps but the ASSEMBLY untouched; reset
  DIRECTION CURRENT DIRECTIVE from "prove W4/inputs" to "attack the Lemma 13
  measure-balance selection lemma" (the route-decisive test).
- 2026-08-24: W5 Lemma-13 inputs COMPLETE — B–Y Lemmas 7 (`CFConcat`) / 8
  (`BaryBlockCount`) / 9 (`BaryConcat`), Prop 12 + d-ary bad zones (summed +
  widened, `TBrickDefs`), CF word bridge (`CFWordBridge`), digit semantics. Key
  route decision: per-J m_d selection (brick ratio 1/(2d)) replaces B–Y's
  uniform 16e^{4c} bookkeeping (incompatible with the repo's Lemma-5 substitute).
- 2026-08-24: W4 CORE COMPLETE — `CFBlockFreq.lean` first moment → pair shift →
  second moment → covariance (γ-mixing consumer) → `variance_blockCount_le` →
  `chebyshev_blockCount` (+ brick-conditioned version), all axiom-clean.
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
- **W5 Lemma 13 assembly (THE crux, DIRECTIVE target)**: (1) t-brick structure +
  ε-refinement predicate (Defs 10–11, ratio 1/(2d)); (2) the measure-balance
  selection lemma — good mass ½|I_w| > CF bad + Σ_{d≤t} d-ary bad for n large
  (route-decisive); (3) Lemma 13 proper + t→t+1 via Prop 12.
- Judge: ratify W4/W5 frozen statement shapes when the assembly settles them.

### Long-term
- W5: t-bricks, main refinement lemma, schedule, limit x, three correctness
  proofs, Pillai powers-equivalence for "absolutely normal".
- W6: Khinchin graft (digit caps D_t, uniform integrability, K₀ as tprod).

### To completion
- B5′ headline: one explicit witness = absolutely normal + CF-normal +
  Khinchin-typical (apparently first-anywhere even on paper).
- Outward (Track A): PR to ChampernowneNormality (staged, Trevor opens);
  comparator harness + Zulip; normality defs → mathlib.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-24)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `isNormal_log_two_of_equidistributed` | cond (on orbit equidistribution) | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `measurePreserving_gaussMap` (B1) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `cylinder_mixing` (W3 core) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `gauss_kuzmin` (B4) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `gaussMeasure_cylinder_mixing` (W4 γ-mixing) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |
| `chebyshev_blockCount` (W4 Chebyshev) | uncond | propext, Classical.choice, Quot.sound | 🟢 trust-base only — DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0**. No 🔴 in any unconditional headline. The ln 2 headline's conditionality
is a hypothesis on the theorem itself (paper-faithful), not a cited axiom. The
B5′ headline (abs-normal + CF-normal + Khinchin) is not yet stated — it is the
W5/W6 destination, gated on Lemma 13; when stated it must be trust-triple-only
(both deep imports are already discharged into proved elementary lemmas).

## Pointers
ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) · JUDGE.md (statement governance) ·
newest HANDOFF-2026-08-23-*.md · PENDING_WORK.md · papers/becher-yuhjtman-*.md
