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

- `PrimeLambertAnalytic` (checkpoint 4): exact prime-by-prime split of the finite tail, the
  four analytic Props, proved wiring `ChainExists → PhaseOscillation → Irrational primeLambert`.

## Open

`ChainExists` = `TailTruncation ∧ LargePrimeNegligible ∧ BadPrimeFrozen ∧ SmallPrimeDecay` for
every `q ≠ 0`.  The single `sorry` remains `phaseOscillation` in `PrimeLambertOscillation`.
Next attack, in order of exactness: (1) `BadPrimeFrozen` from a residue-freezing hypothesis
on the sample (exact: `p ∣ n + r ↔ p ∣ n' + r` when `p ∣ n − n'`); (2) `TailTruncation` from
`ω(m) ≤ log₂ m` and the geometric tail; (3) `LargePrimeNegligible` from the count of prime
factors above `R`; (4) decompose `SmallPrimeDecay` into independent-model decay, CRT moment
comparison, and even-moment transfer Props.  Geometry still lacking: distinct first
coordinates for `B ≥ 7`, the mass `6^{K/3}`, surviving squared mass at `K+1`.
