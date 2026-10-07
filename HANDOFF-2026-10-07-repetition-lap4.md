# HANDOFF 2026-10-07: repetition lap 4 (review lap) end (branch proof/cantor-repetition, HEAD 1ac823b3)

Supersedes repetition-lap3.  Operator kickoff: KICKOFF-2026-10-06-repetition.md.  Tree clean.
**Read DIRECTION.md CURRENT DIRECTIVE first** (set this lap): prove the assembly
`repPairArith_of_inputs`; no redesigns, no head-on attack on `TOrbitCyclicDecay`.

## State (src/NormalNumbers/CantorRepetition.lean, 3 sorries)
- `repPairArith_of_three_dvd` (crux; needs walls + Baker, open research).
- `repPairArith_of_inputs` (assembly, 60%) — the directive target.
- `card_cycProd_ge_le` (off-path leaf, 90%, English proof in docstring; elementary digit-change
  counting; in the scoped file, so prove it once the assembly is done).

## Done this lap
- Review: route analysis (copies forced for any Liouville point of K; short/random periods also
  need open arithmetic).  Nodes `card_cycProd_ge_le`, `SuperPolyOrderPeriods`.  STATUS/DIRECTION/
  PENDING_WORK updated ("repetition review lap 3" section in PENDING_WORK has the class list).
- PROVED `isFresh` (free ∨ odd run), `src_of_fresh`, `isFresh_eq_false`, `repReal_eq_fresh`,
  `charFun_repReal_fresh`; `repBound none` now = `Bf isFresh M ξ`.
- PROVED `pair_classify_rep` (+ `NearCopyBdry`, `deep_or_fresh`, `run_unique`, `run_index_ge`,
  `runStart_add_two`, `runEnd_le_runStart`): positions v (low end of ξ), y (top of Y=h bᵐ), u (low
  end of h bⁿ), T (top of ξ) → six classes or a boundary band.

## Next (in order)
1. Per-class Riesz bounds, pair `ξ = h(bⁿ − bᵐ)`, `b = 3ˢt`, `e = v₃ h`:
   - low window lemma: fresh `[w+1, w+W)` and `ξ = 3^w X + Z`, `|Z| ≤ 3^w ε` ⇒
     `Bf isFresh M ξ ≤ Hf true 0 W X + π ε` (classes 1: w=v, Z=0; 3: w=u, Z=−Y); reuse
     `bf_le_hf_true`, `abs_prod_sub_prod_le`.
   - top windows: class 2 `bf_le_topProd_of_dvd` (Ξ=ξ, Y=h bᵐ, needs y ≤ u), class 4 `bf_le_topProd`.
   - copy lemma: `ξ = 3^a η₀ + Z` ⇒ `repBound M (some k) ξ ≤ cycProd a η₀ + π(|Z|/3^a + |ξ|/3^{(k+2)a})`
     (classes 5: η₀ = 3^{sm−a}h tᵐ(b^d−1); 6: η₀ = 3^{sn−a}h tⁿ, Z = −Y).
2. Analytic facts feeding `pair_classify_rep`: v ≤ y ≤ ρv, u ≤ T ≤ ρu, u < y+K ⇒ T ≤ ρv for
   m ≥ m₀ (ρ from log₃ b/s, h); T ∈ {T(n)−1, T(n)}.
3. Sums: κ := argmin of repBound over options; per-class sums via `sum_hf_true_le`,
   `sum_topProd_le`, `copyRun_sum_le`/`copyZoneDecayH_of`, `TOrbitCyclicDecay` (c = h); band and
   small-m counts; W, K ≍ ε log N; then summability via `summable_sched_rpow`.
4. Conditional headline `liouvilleCantorFullProfile_of` (Baker + walls).
