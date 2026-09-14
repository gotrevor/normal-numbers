# HANDOFF 2026-09-14 — prime Lambert irrationality (bounded campaign, lap 1 checkpoint 1)

Brief: `~/personal/claude/knowledge/core/projects/normal-numbers-prime-lambert-lean-brief-2026-09-14.md`.
Footprint: `src/NormalNumbers/PrimeLambert*.lean`, `docs/prime-lambert-irrationality.md`, this file.
Root module / lakefile untouched (host-owned).

## Landed (green, targeted build `lake build NormalNumbers.PrimeLambertOscillation`, 8708 jobs)

- `PrimeLambertDefs`: constant, tail identity `tailT_eq`, `rational_tail_int`, exact transport
  `omega_mul_eq` / `dilatedTail_eq`, exact periodicity `transportCorr_congr`.
- `PrimeLambertConfig`: `TConfig`, `CancelsAt`, `phaseSum`, `phaseSum_eq`, **Theorem A**
  `phaseSum_sub_int`.
- `PrimeLambertOscillation`: `PhaseOscillation` (draft eq. (5)), `norm_phaseAverage_eq_one`,
  `irrational_of_phaseOscillation` (all `[propext, Classical.choice, Quot.sound]`).
  `phaseOscillation` = the one disclosed `sorry`; `irrational_primeLambert` depends on it.

- `PrimeLambertGeometry` (checkpoint 2): hexagon/tensor cancellation in `ℤ[ℤ×ℤ]`, six-atom
  form, dilation, coprime transform to `TConfig`, `exists_tconfig_cancelling`.  Axiom-clean.

- `PrimeLambertHexagonCounterexample` (checkpoint 3, addendum): `not_meanRetention_seven`,
  axiom-clean, full complex inequality with `c = 2cos(2π/7)` identified.

## Open

The analytic chain (draft §5) is entirely open; `PhaseOscillation` is its endpoint Prop.
Next: geometry module (hexagon tensor, transform), then split §5 into exact sub-Props.
