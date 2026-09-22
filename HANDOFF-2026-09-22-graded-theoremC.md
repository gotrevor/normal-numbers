# HANDOFF 2026-09-22 — G4–G5c: Theorem C′ stated, wired, and reduced to numeric leaves

Branch `wip/g5-prime-subset`, HEAD `cd75026`.  Working tree clean, `lake build` 🟢 **9160 jobs**.
Running `KICKOFF-2026-09-22-multicutoff-lean.md` under the 2026-09-22 17:12 EDT override, on the
route set by `DIRECTION.md` → CURRENT DIRECTIVE (the graded joint state).  Laps 0–6 + G1–G3 were
already landed; this lap did G4, G4′, G5a, G5b, G5c and G5c-a.

## Landed this lap (all `lake build` green, all headlines `[propext, Classical.choice, Quot.sound]`)

| leaf | commit | file | headline |
|---|---|---|---|
| G4 | `5c3fadc` | `PrimeModelTheoremAGraded.lean` | `KMT.window_bound_gradedG` |
| G4′ | `acf77ee` | `PrimeModelTheoremAGradedM.lean` | `KMT.window_bound_gradedGM` |
| G5a | `d24f947` | `PrimeModelGradedTiers.lean` | `BlockSieve.empLawG_lower_atom_bands` |
| G5b | `c86e532` | `PrimeModelWindowSchedule.lean` | `KMT.window_bound_schedule` |
| G5c | `a4a64ea` | `PrimeModelFamilyGraded.lean` | `windowMean_le_terms`, `kmt_along_graded`, **Theorem C′** |
| G5c-a | `cd75026` | `PrimeModelFamilyGraded.lean` | `recipSumIoc_sqrt_le`, `epsG_tendsto`, **`uG_tendsto`** |

* **G4** — Theorem A on the graded law (`empLawG`, `jointModelG`) at the band-dependent class
  count.  `statePhaseG_truncState` is the empirical transfer (a prime assigned to a shift it
  cannot reach carries `zSee = 1`); `sum_jointModelG_testFG_eq` is the model transfer off
  `radical_phase_productG_eq`, so leg E5 is reused verbatim.  E4 runs at the sharp per-site
  exponent `1/(2 log y_j)` — **wall 2 of the review lap closed inside Theorem A**.
* **G4′** — the same at the split `m ≥ k`.  Needed because the sieve wants `2 d_q ≤ q` with
  `d_q ≤ k`, i.e. `q > 2k` (the paper's `Q = primorial (2k)`), while `window_bound_gradedG`'s
  state primes only satisfy `q > k`.  `hdp` is therefore required only on the state primes,
  which is what lets the caller clip `d_q = 0` below `2k`.
* **G5a** — the tier family from the schedule alone: band `b` is `stateU ∩ (lo b, y b]`,
  dimension `b+1`, cutoff `y b`.  `family_cover` (telescoping) and the exact class count on a
  band discharge `hcover`/`hdpj`; the degenerate-atom lemmas make the bound hold for **every**
  joint state, as `hlower` demands.  **Wall 1 closed**: tier dimensions are `b+1`, not `k`.
* **G5b** — `window_bound_schedule`: Theorem A with no model or sieve hypothesis left.  The
  support level is visibly graded, `log R = ∑_b (128(b+1) + 4u_b + 14) log y_b`.
* **G5c** — the Astra §8/§11 schedule, the five named terms, the pointwise bound
  `windowMean_le_terms` (PROVED), `kmt_along_graded` (PROVED from the five limits) and
  **`isNormal_subsetLambert_of_sqrtFreshMassZero`** (Theorem C′), wired through
  `isNormal_subsetLambert_of_KMT_along`.
* **G5c-a** — `uG_tendsto` (`u_N → ∞`), the shared prerequisite of four of the five limits,
  plus the whole `epsG` (sup of the square-root fresh mass) layer.

## Two schedule choices that are NOT in the paper, and why they are forced

1. **Graded tier weights `u_b = u_N + b`.**  With a constant `u` the sieve defect is `J e^{−u}`,
   and `TailOK` pins `J ≍ L₃N`, so `ρ_N → 0` alone cannot kill it.  Graded gives
   `∑_b e^{−u_b} ≤ 1.6 e^{−u_N}`, no `J` factor; the extra level cost `∑_b 4b 2^{−b} log y_b`
   is `O(a log N)`, absorbed in the same constant.
2. **`yBotG` built from `J₁` and the minimal admissible `a = 1/L₃N`**, not from `J_N` or `a_N`.
   This breaks the circularity `J_N ← S_P(y_{J_N−1})` and gives a uniform `Z` for the root chain
   and a uniform lower end for the E5 contraction (every actual cutoff dominates `yBotG`).

Nothing in the paper is refuted this lap.

## Open leaves, all in `src/NormalNumbers/PrimeModelFamilyGraded.lean` (this IS the crux decomposition)

`PENDING_WORK.md` top section carries the paper estimate for each.

1. **`yBotG_tendsto`** (not yet declared — add it) : `Tendsto yBotG atTop atTop`.  Needed by
   `epsG_tendsto`/`uG_tendsto`, which currently take it as a hypothesis.  Estimate:
   `log yBotG ≥ (aMinG)(log N) ≥ log N/(2 L₂N L₃N) → ∞`, using
   `2^{J₁N} ≤ 2·2^{L₃N} = 2(L₂N)^{log 2} ≤ 2 L₂N`.  Then `log t/(log t · log log t)` via
   `tendsto_log_div_rpow` at `r = 1/4` (log t ≤ t^{1/4} eventually).  **Do this first** — it
   unblocks everything else, and it is pure schedule analysis.
2. **`termE4b_tendsto`** : `2(0.3)∑_b e^{−(u_N+b)} ≤ 0.96 e^{−u_N} → 0`.  Immediate from
   `uG_tendsto` + a geometric sum.  Cheapest leaf after (1).
3. **`termE4a_tendsto`** : `log T_j/(2 log y_j) = 2^{j/2} u_N²/32`, so the sum is
   `2e^{20}∑_j exp(−2^{j/2}u_N²/32) ≤ 4 e^{20} exp(−u_N²/32) → 0`.
4. **`termE1_tendsto`** : root chain `SqrtFresh.recipSumIoc_le_rootChain` with `Z = yBotG N`,
   `ρ = epsG P N` (`recipSumIoc_le_epsG` is the input, already proved) gives
   `S_P(y_j,N) ≤ ε_N(j + 2log₂u_N + 1)`; sum against `4^{−j−1}` and use
   `ε_N log u_N ≤ ε_N log(1/ε_N)/2 → 0` (this is exactly what `u_N ≤ ε_N^{−1/2}` is for).
5. **`termE4c_tendsto`** : `log R ≤ (540+8u_N)/u_N² · log N` (from `∑_b (b+1)2^{−b} = 4`),
   `(2J)# ≤ 4^{2J}`, `∏_j ⌊T_j⌋ ≤ N^{0.22}`; product `N^{−1+o(1)}`.
6. **`termE5_tendsto`** : `8J ≤ S_P(yBotG)` and `S_P(2J) = O(log log J)` give exponent `≥ 5J`.
7. **`schedule_admissible`** : the eleven pointwise clauses.  Watch `hcutlo` (needs `L ≥ 2`:
   `⌊t²⌋^{1/4} ≤ ⌊t⌋` for `t ≥ 2`, hence `LG = max 2 …`) and `hcut2`
   (`2^{−L} log yBotG ∈ [log 2, 2 log 2]`).
8. **`tailOK_graded`**, **`JG_tendsto`** : verbatim ports of `tail_fresh` / `JI_tendsto` with
   `yBotG` for `yI` and `JG` for `JI`.

Suggested order: 1 → 2 → 3 → 8 → 6 → 4 → 5 → 7.

`src/` also still holds the two pre-existing off-campaign `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`).
