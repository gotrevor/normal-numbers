# HANDOFF: prove `rieszEnergyTail` (branch `wip/riesz-energy`)

**Objective.**  Make `src/NormalNumbers/CoefmassRieszEnergy.lean` sorry-free by proving
`theorem rieszEnergyTail : RieszEnergyTail`.

**Rules:**
- Do NOT change the statement of `RieszEnergyTail`, or the definitions `psiP`, `periodMean`,
  `muP`, `rieszCentered`.  They are under referee review in
  `docs/notes/coefmass-bv-ledger-2026-10-11.md`.  If the statement is false, stop and say so with a
  counterexample (`box stuck`); do not weaken it.
- Helper lemmas may go in the same file.
- No axioms, no `native_decide`.

**Proof plan.**  It is in the module docstring, steps 1–6.  The arithmetic core is step 1, the CRT
product average.  Everything else is finite algebra over `Finset.powerset`.

Suggested order:
1. Prove step 5 (the scalar inequality) first.  It is self-contained.
2. Then steps 2 and 1 (periodicity, CRT average).
3. Then steps 3, 4 and 6.

**Done means:**
1. `lake build NormalNumbers.CoefmassRieszEnergy` is green with no `sorry` warning.
2. `#print axioms NormalNumbers.PrimeModel.SiteFactor.rieszEnergyTail` shows only `propext`,
   `Classical.choice` and `Quot.sound`.
3. As the last step, add `import NormalNumbers.CoefmassRieszEnergy` to `src/NormalNumbers.lean`,
   and confirm the full `lake build` is green (~17 min).
4. Commit on `wip/riesz-energy`.

**Numerical control** (exact, out of tree): J=3, P={7,11,13,17}.  The energy equals the
orthogonal sum `Σ_T (1−w_T)² ∏|μ|² ∏V` to all printed digits:
- K = log 200, k = 1: 0.186636 ≤ 0.298677
- K = log 40, k = 5: 0.516344 ≤ 2.14494

## Status

Lap log goes here.
