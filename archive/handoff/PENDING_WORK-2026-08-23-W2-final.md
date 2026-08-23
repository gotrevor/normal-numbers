# PENDING WORK — B5′ / W2 campaign: COMPLETE (2026-08-23)

**Campaign result**: all 10 frozen statements in
`src/NormalNumbers/CFDigitLaw.lean` proved in three laps, one session.
`src/` is sorry-free; `#print axioms` on all 10 = exactly
`propext`/`Classical.choice`/`Quot.sound` (observed).  The 4 kernel-checked
anchors still pass.  No frozen statement was touched; two W1 `private`
lemmas (`one_le_cfK`, `irrational_gaussMap`) were lifted public
(permitted shared-scaffold lift per the campaign brief).

**Per-lemma record**:
- Lap 1 (`0f512a4`): `cfK_le_prod`, `volume_digit_cylinder`,
  `cfCylinder_disjoint`, `volume_append_mul_fib_le`,
  `gaussMeasure_le_volume`, `volume_le_gaussMeasure`, `gaussMeasure_univ`.
- Lap 2 (`9933e57`): `volume_eq_tsum_extensions` (the partition crux) —
  via outright measurability of `gaussMap`/`cfDigit`/`cfCylinder`
  (which W1 had avoided; ~20 lines) + `measure_biUnion` + countable-null
  rational junk.
- Lap 3 (`fdc51a6` + final): `tsum_mul_log_cfK_le` by **first-digit-peeling
  induction** (not the brief's positional marginals): `K(k::s) ≤ (k+1)K(s)`,
  order-1/order-n partition identities, distortion, digit law;
  `C = 2S+1`, `S = Σ log(j+2)/((j+1)(j+2))` summable via `log x ≤ 2√x` vs
  the 3/2-p-series.  Then `half_mass_long_extensions` = Markov with
  threshold `e^{2C₀n}`, ENNReal cancellation via
  `ENNReal.mul_le_mul_iff_left` and `add_le_add_iff_right` (cylinder
  measure finite).

**Next campaign**: W3 (mixing/Chebyshev) per `KHINCHIN.md` — statement
shapes to be frozen with kernel-checked anchors, planted-scaffold doctrine.
Inputs now available: the full W1 toolkit, the W2 digit-law/partition
calculus, `tailDensity_mem_Icc`, and the Gauss/Lebesgue comparison pair.
