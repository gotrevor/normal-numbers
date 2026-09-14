# HANDOFF 2026-09-14 — G4 disjunctivity, lap 5 (A and C input-complete on one concrete object)

Branch `wip/g4-disjunctivity`, HEAD `08b79bf`.  Working tree clean apart from the host's
untracked `CHECK-g4-route-deviations.md` (not swept in).  Not pushed.
Commits this lap: `80fc127` (G4Grid), `7689787` (G4SmallPrimeVector), `3a7f32e` (G4Mertens),
`043f0fd` (G4Transport), `08b79bf` (G4Progression).  All new files sorry-free; every headline
prints `[propext, Classical.choice, Quot.sound]`.  `DIRECTION.md` unchanged (grind lap).
`PENDING_WORK.md` §"GRIND 2026-09-14 (G4 lap 5)" carries the mathematics and the map.

Build: `lake build NormalNumbers.G4Grid NormalNumbers.G4SmallPrimeVector NormalNumbers.G4Mertens
NormalNumbers.G4Transport NormalNumbers.G4Progression` green.

**Resume here**: build the wiring `Frame` from `GridParams` (reindex atoms `≃ Fin H`, rows
`Fin K → Fin s ≃ Fin r`, `S := Sval` composed with the reindexing, `θ := transportTheta 0`,
`P := apSample X P₀ b₀`) and discharge `Frame.PropA` outright via `propA_of_progression` +
`exists_mult_mul`.  Then `PropC` via `norm_sampleAvg_torusChar_Sval_le` with
`sm = {p ≤ R prime : p ∤ P₀}`, `goodPrime_of_not_dvd_P₀`, `two_mul_card_le_of_not_dvd`, and the
harmonic mass from `G4Mertens`; C4 numerics (`M = 10⁴·|Idx|·L`, `λ = λ' = 8`) against
`Λ = (2D+1)^r` via `schedule_budget`.

## Proved this lap (declaration names)

* `G4Grid`: `balanced_digits_eq_zero`, `sum_kronPow_diffZ_mul_eq_zero` (first `K` layers cancel),
  `proj_injective`, `gridU_injective`, `coprime_mult`, `shiftG_injective` (global distinctness),
  `add_shiftG_eq`.
* `G4SmallPrimeVector`: `Sval`, `torusChar_Sval` (concrete character = phase sum),
  `sum_sq_distZ_coeff_ge` (`θ₀ = 4^{−4}8^{−K}` on the box), `goodPrime_of_not_dvd`,
  `shiftAL_injective`, **`norm_sampleAvg_torusChar_Sval_le`** (§4C for the concrete vector).
* `G4Mertens`: `log_log_le_sum_inv_primesBelow` (lower Mertens, not in mathlib),
  `sum_inv_le_log_card_add_one` (excluded primes cost `log ω(P₀) + 1`).
* `G4Transport`: `tailB_eq`, `dilatedTailB_eq` (fixed-base §1 identity, any `b ≥ 2` — trigger
  G-T2's identity is PROVED), `corrB_congr`, `coe_tailB_four`, **`Frame.propA_of_progression`**.
* `G4Progression`: `GridParams`, `b₀`, `freezeQ`, `P₀`, **`exists_mult_mul`**,
  **`goodPrime_of_not_dvd_P₀`**, `two_mul_card_le_of_not_dvd`.

## Dependency map

E proved.  A: input-complete (`propA_of_progression` + `exists_mult_mul`), needs Frame plumbing.
C: input-complete, needs the same plumbing + C4 numerics.  B: inputs proved, assembly open
(lap-2 handoff steps).  D, Jackson, §5 schedule (incl. `log P₀ = o(L)`, upper Mertens for the
far tail): open.  Nothing refuted.
