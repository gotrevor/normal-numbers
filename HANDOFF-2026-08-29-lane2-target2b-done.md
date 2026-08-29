# Handoff: lane-2 batch-2 target 2 done — π² signed-kick machine landed, run self-stopped

**Date**: 2026-08-29 · **Branch**: master · **HEAD**: abd91b0

## ✅ State

- **Target 2 DONE** (commit abd91b0): `src/NormalNumbers/PiSqBBP.lean` complete,
  sorry-free, full `lake build` green (8786 jobs, observed). `#print axioms` on
  both headlines `piSq_boundary_of_zeroRun` / `piSq_boundary_of_maxRun` =
  `[propext, Classical.choice, Quot.sound]` (observed). Scoped target met,
  `box done` issued, host halting.
- Brief v2 `## Progress` updated (same commit). Working tree clean apart from
  this handoff.

## 🧠 Context to carry forward

- **Signed layer** lives in `PiSqBBP.lean` (KickedOrbit-style):
  `kicked_tail_abs_le`, `boundary_of_fract_lt/_ge`,
  `boundary_of_zeroRun_kickedAbs` / `boundary_of_maxRun_kickedAbs` — reusable
  for any signed BBP constant.
- **Key restatement**: draft surrogate `kickedPartial 16 piSqKick n` missed the
  j=0 block (only positive one, ≈9.88); fixed with shifted kick
  `piSqShiftKick m = 16·piSqKick (m−1)` so the kicked series is exactly π².
- Gotchas: `linarith` treats `16/X` and `48/X` as unrelated atoms — pre-state
  comparisons as `c·(1/X)`. `gcongr` auto-closes side goals from context
  hypotheses (leftover `linarith` then errors "no goals").
- Node `PiSqBBP` (Formula 29) stays frozen CITED; its lane-2 discharge is owed
  (like `PiBBP` was — likely route: polylog/arctan-squared identities at
  1/√2-type arguments, or term-by-term from the original BBP integral).

## 🎬 Next actions

1. **Target 3** of `HANDOFF-2026-08-29-lane2-brief-v2.md`: sharpen β = 26 in
   `LnTwoExpSepProof.lean` via NEW theorem `lnTwoExpSep_sharp` (lossy spots in
   that file's docstring: coefficient height 8^ℓ → ~5.83^ℓ Legendre value;
   zero-case remainder (1/6)(1/12)^ℓ → sharper kernel estimate). Multi-lap.
2. Discharge of node `PiSqBBP` itself (lane-2 owed).

---
**→ Next session: pick up at target 3; batch-2 targets 1 and 2 are DONE, do not
reopen.**
