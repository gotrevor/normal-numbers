# Handoff: after-the-extraction lap 131 — W done (withdrawn form); override stop condition met

**Date**: 2026-09-15 · **Branch**: `wip/g4-entropy` · `lake build` 🟢 9038 jobs · tree clean after this commit

## What this lap did
* **W** (DIRECTION: withdrawn to one paragraph, no `docs/` essay): the module docstrings of
  `G4EntropyWStatement` and `G4EntropyWSqueeze` now state what `fullRealW` is
  (`realOfDigits 2 (fullDigW G₄)`, digits read at `fullPosW`), that the read set has density zero
  in `G₄`'s digit string (`Sched.density_coeff_le`, coefficient `< 10^(−10^1665000)` at scale 0),
  that positions lie above `wLo i` (`wLo_le_fnthW`), and that nothing is claimed about normality
  of `G₄` itself.
* Re-verified in kernel this lap: `deformation_coeff_le`, `deformation_union_le`,
  `density_coeff_le`, `offset_rigidity`, `isNormal_two_of_schedule_read` →
  `[propext, Classical.choice, Quot.sound]`; `recentring_anchor` → no axioms.

## State
L1 ✅ (`G4ResidualConfinement`), L2 ✅ (`G4OffsetRigidity`), F ✅ design + kernel verdict
(`DESIGN-2026-09-15-deformation.md`, `G4TensorRigidity`, `G4DeformationVerdict`: proved
limitation of the deformation T(K′)), W ✅.  `src/` carries only the two pre-expedition off-path
`sorry`s (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).

## Next (needs an attended decision, not a grind lap)
The override says stop here.  The open question F left (design §4): does row-balanced,
non-coordinatewise cancellation on `D_s^{⊗K}` force "ignores a coordinate"?  True for `K = 1`;
open in general.  That is the only route not closed by L1/L2/F.

## ⛔ Stuck-bail (strike 1) — verify fast, then `box stuck` again if you agree
* **Blocked**: nothing on the override's path.  L1, L2, F, W are all done and re-verified in
  kernel (see above).  DIRECTION's ACTIVE override: "Stop when F has its verdict … with L1, L2 done."
* **Why operator-gated**: the only `src/` obligations are `PrimeLambertOscillation.phaseOscillation`
  and `MahlerDriftOne.exists_drift_one_background`, both pre-expedition, off-path, on DIRECTION's
  forbidden-drift list (DIRECTION.md lines 217–218, 283–284).  The repo-wide gate declines
  `box done` because of them; touching them violates DIRECTION.
* **The exact ask**: an attended decision on the next frontier — either (a) authorize the
  row-balanced cancellation question from `DESIGN-2026-09-15-deformation.md` §4 as a new campaign,
  or (b) close the run.  Verification for the fresh lap: `lake build` (9038 jobs) and
  `#print axioms` on `Sched.deformation_union_le`, `Sched.density_coeff_le`, `Rigidity.offset_rigidity`.
