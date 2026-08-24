# B6 expedition brief — DRAFT (not launched, statements not frozen)

*Drafted 2026-08-24.  Spec: KHINCHIN.md §B6.  Analysis:
`papers/vandehey-2017-open-problem-attack-map.md`.  This is Ren's proposal
for the attended freeze session; nothing here is ratified.*

## Headline statements (proposed shapes — freeze attended)

Parametrize by the map family once, specialize for the φ headline:

```
-- Tier 2 (general): qr : ℕ → ℝ × ℝ, hq : ∀ i, (qr i).1 ≠ 0
theorem exists_absolutely_normal_cf_normal_khinchin_affine
    (qr : ℕ → ℝ × ℝ) (hq : ∀ i, (qr i).1 ≠ 0) :
    ∃ x : ℝ, AbsolutelyNormal x ∧ CFNormal x ∧ KhinchinTypical x ∧
      ∀ i, CFNormal ((qr i).1 * x + (qr i).2)

-- Tier 1 (the φ corollary, the outward-facing one):
theorem exists_cf_normal_golden_images :
    ∃ x : ℝ, CFNormal x ∧ CFNormal (goldenRatio * x) ∧ CFNormal (x + goldenRatio)
```

Tier 1 is derived from Tier 2 with the 2-element family; `goldenRatio` from
`Mathlib.Algebra.GoldenRatio` (⚠️ verify import name at scaffold time).
Predicate names above are placeholders for whatever B5′ actually exports —
align at freeze, do not invent parallel definitions.

## Design rule: ADDITIVE ONLY 🧊

Landed B5′ files (`TBrick`, `TBrickRefine`, `CFSchedule`, `CFLogTail`, …)
are frozen artifacts backing ratified theorems.  B6 creates new modules
alongside (working names: `CFIntervalGood.lean` for L1+L2, `CFAffine.lean`
for L3, `CFScheduleA.lean` for the extended schedule); where L4 needs the
refinement machinery reshaped, copy-and-extend rather than edit in place.
The existing `exists_absolutely_normal_cf_normal_khinchin` must still build
character-identical at every lap.

## Lap plan (est. 3–6 opus/low + judge gates; breaker rec --max-laps 8)

1. **Lap 1**: L1 (interval→cylinder covering) + L2 (good-block density on
   arbitrary intervals).  Self-contained, consumes `CFCylinder` +
   `cylinder_mixing`-culture bounds.  Gate: kernel axiom sweep.
2. **Lap 2**: L3 affine transport (image intervals, |ψ(A)| = |q||A|,
   integer-part drift via tail-shift invariance).  Gate.
3. **Laps 3–5**: L4 extended schedule (per-stage budget re-split across
   bases + image systems, map count m(s) growing with the B–Y (log s)^{1/5}
   discipline) + L5 per-map correctness assembly.  Gate: both headline
   statements + full sweep.

Escape valves (judge-governed): (a) if the countable-family budget
bookkeeping balloons, Tier 2 drops to a FINITE family (Tier 1 unaffected);
(b) if the greedy stretch (image Khinchin-typicality) resists, it detaches —
it is not in the headline statements.

## Verification bar

Same as B5′: statements character-frozen after the attended session; kernel
`#print axioms` = standard triple on both headlines at close-out; re-run the
novelty lit sweep before anything goes outward (a spec-day null is not a
close-out null).
