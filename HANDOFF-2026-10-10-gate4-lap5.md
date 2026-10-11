# HANDOFF 2026-10-10 — operator gate 4, lap 5: `coherentTwoThree449` PROVED

Branch `proof/uniformbad-threshold`, HEAD 47a22d47 (green). Uncommitted: only scripts/cstar_models/__pycache__ (ignore).

- `cleanCertificate449` and the frozen `coherentTwoThree449` are theorems (no sorry in
  `src/NormalNumbers/UniformBadCoherent.lean`).  `#print axioms coherentTwoThree449`: propext,
  Classical.choice, Quot.sound + native_decide certificates (W data facts, edge facts, SFT reach,
  root sum, 8 bin-range checks).
- New lib `CertData` (lakefile; precompileModules, no Mathlib): `CertData/Gate4.lean` = frozen
  weights W (exact3.c output) + computable checker (`wstep/windows/kidF/chF/go/bb/checkBin`);
  `CertData/Gate4Check0..7.lean` = `checkRange a b = true` by native_decide (~1-3 min each).
- Soundness chain (in UniformBadCoherent): windows_sound, child_zone0/1, kid_unres, kid_res,
  chF_sound, go_sound, bb_sound, inv_of_good, grow_good, rootSum_le, cleanCertificate449_of_data.
- Bug found and fixed on the way: the Lean edges array first held all 25 C edges (bins off by one).
- Earlier this lap: operator blocker (h) fixed; exact3.c exact certificate; acc2_of_sftRun.

## Next
Gate 4 target met.  The scoped objective (UniformBadCoherent sorry-free) is complete.
Possible follow-up (operator's call): the base >= 5 engine with weight-aware tail charges
(module doc "Measure first"), a neutral note docs/notes/, or c = 4.49 -> the downstream headline.
