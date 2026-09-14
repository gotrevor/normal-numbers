# HANDOFF — entropy expedition, session wrap (2026-09-14, Opus, laps 16–22)

**Branch** `wip/g4-entropy`.  **HEAD** `6f9858b` (this doc commits on top).  Working tree clean.
`lake build` green, **8961 jobs**.  Every module added this session is sorry-free and
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  No pre-expedition file was
edited; `DIRECTION.md`, `STATUS.md` and the brief were not touched (grind laps).  Preserved
declarations re-verified clean each lap: `G4.isDisjunctive_four`, `G4.isDisjunctive_two`,
`G4.isDisjunctive_base`, `PrimeLambert.primeSumAtBase_eq_primeLambertAtBase`.

Per-lap detail: `HANDOFF-2026-09-14-entropy-lap16.md` … `-lap22.md`.

## The arc

The session arrived with brief §6 answered negatively but as a *bound*: lap 9's barrier said a
digit-local hypothesis forces normality only if it reads density `≥ 1/2`, and laps 10–14 showed
every admissible repair reads far less.  Seven laps turned that into a complete structural
theory, in seven green commits.

**Lap 16 — `G4EntropyDensityOne.lean`.**  The factor `1/2` was an artifact of using one filling
of the unread positions.  Comparing the zero filling with the *parity* filling (a `1` at every
even-indexed position of `Sᶜ`, which keeps the expansion proper) forces both ones-densities to
be exactly `1/2`, so `Sᶜ` has density `0`: **`tendsto_density_compl_zero`**,
`tendsto_density_one_of_forces_normal`, `exists_nonnormal_of_digitLocal_of_lt_one` (refutes at
any `c < 1`), `Sched.not_T_E_of_density_lt_one`.

**Lap 17 — `G4EntropyStable.lean`.**  Density one is attained:
`isNormal_congr_of_density_zero` (normality is invariant under density-zero digit changes, by a
window count with the injection `i ↦ (least j<ℓ with D(i+j), i+j)`), hence
`isNormal_local_of_density_one` and the characterization
`exists_digitLocal_forces_normal_iff`.

**Lap 18.**  The characterization made unconditional: the repo's `isNormal_two_stoneham23`
supplies a normal number in `[0,1)` (`exists_isNormal_mem_Ico`), giving
**`forces_normal_iff_density_one`**.

**Lap 19 — `G4EntropyShift.lean`.**  `isNormalSequence_shift_iff` (normality is shift-invariant)
and `isNormal_orbit_iff`, hence **`exists_orbitLocal_forces_normal`**: a *single unquantized*
orbit value `{2^i x}` carries a satisfiable hypothesis that forces normality.  **The obstruction
is the quantizer, not the sparsity of the times.**

**Lap 20 — `G4EntropyDiagonal.lean`.**  `digitOf_congr_of_blockVal` (a window value determines
its digits — converse of `blockVal_congr`, via `blockVal_succ`) makes "sample values" and
"digits on the read set" interchangeable, giving **`qForces_normal_iff_density_one`**: for an
arbitrary family of times and quantization levels, a satisfiable hypothesis about
`⌊2^{mᵢ}{2^{rᵢ}x}⌋` forces normality iff `⋃ᵢ[rᵢ, rᵢ+mᵢ)` has density one.  The schedule is
exhibited as an instance (`schedW`, `qRead_schedW_iff`, `not_qForces_normal`).

**Lap 21 — `G4EntropyPrecision.lean`.**  `exists_qVal_eq_orbit_ne`: a sampler of density `< 1`
determines **no** orbit value — flip one unread digit.  So the route failed not by having too
weak a hypothesis but by discarding the exact datum that would have sufficed.

**Lap 22 — `G4EntropyLevels.lean`.**  The last freedom: keep the times, widen the windows.
`LevelBudget`, `card_isSampledAt_le` (density still `≤ 1/4`), `not_qForces_normal_of_levels`,
and `levelBudget_of_le_pow` — the budget admits every level up to `B^K ≥ K^{3K}` against the
schedule's `K/4`.  Exported `two_mul_succ_le_gridB`, `pow_sq_gridB_mul_le`.

## Status against the brief

| item | status |
|---|---|
| §2, §3A/B/C, §4 | closed earlier (`entropy_E0`, `entropy_E1`, unconditional, clean) |
| §5 | answered lap 15 |
| §6 `T_E`, `T_S`, `T_mix` | refuted (laps 8–9) |
| §6 positive branch | **closed as a characterization**: forces normality ⟺ reads density one (16–18, 20), attained only by normality itself (17), unreachable by any quantized sampler on this schedule at any level (22) |
| what would suffice | one unquantized orbit value (19) — and the sample never determines one (21) |

The brief's §8 outcome condition was already met before this session; laps 16–22 replace the
negative answer with a complete structural account of *why*, with no side conditions.

## What is NOT claimed

Nothing about the normality of `G₄`.  Nothing outside the `GridParams` interface.  Lap 21 is
about *exact* determination of an orbit value (the witnesses differ by `2^{-(j+1)}`); lap 20 is
what closes the approximation route.

## Next session

1. **Altitude lap first.**  `DIRECTION.md`'s CURRENT DIRECTIVE and `STATUS.md` still describe
   `T_E` as the open objective and are now seven laps behind; they should record the table
   above.  Grind laps must not edit them — this session did not.
2. **If more mathematics is wanted**: the only room is a datum that is not a finite-precision
   reading of the orbit.  The repo's `G4Jackson` / `G4SeparatingTest` bounded-Lipschitz layer is
   exactly such a functional, and lap 19 says such data *can* force normality; the question is
   whether the expedition's exponential-sum control survives without the quantizer.  That is a
   new attended objective, not a lap.
3. Unrelated open `sorry`s elsewhere in `src/` (`MahlerDriftOne.exists_prime_nonresidue`,
   `PrimeLambertOscillation.phaseOscillation`) are not this campaign's and are on the
   forbidden-drift list; untouched.
