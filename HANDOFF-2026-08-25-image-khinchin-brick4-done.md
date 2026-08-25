# HANDOFF — 2026-08-25 · image-Khinchin: brick 4 (variance MCT) DONE

Branch `master`, HEAD `a9e7914`, build 🟢 8760, tree clean.

## Landed this lap (all in `CFAeKhinchin.lean`, axiom-clean [propext, Classical.choice, Quot.sound])
**`variance_logBirkhoffSum_le K n`** : `|∫(logBirkhoffSum K n)² − (n·μ)²| ≤ n·logVarConst K`,
`μ = logTailC1 K`.  The genuine variance bound for the UNBOUNDED log-tail Birkhoff sum,
obtained by pushing the uniform-in-M `variance_truncated_le` to `M→∞` via MCT. Supporting bricks:
- `partialTail K M y = Σ_{a<M} log(K+1+a)·1_{[K+1+a]}(y)`; `_nonneg`, `_mono` (in M),
  `partialTail_tendsto` (eventually-constant ⇒ `→ logTailFn K y` for `y∈(0,1)`).
- `logBirkhoffTrunc_eq_sum_partialTail` (= Birkhoff sum of partialTail), `_nonneg`, `_mono`,
  `measurable_logBirkhoffTrunc`, `logBirkhoffTrunc_tendsto` (full-orbit x ⇒ `→ logBirkhoffSum K n x`).
- `integrable_logBirkhoffTrunc_sq`; `logTruncMean_tendsto` (→ logTailC1 K).
- **`logTailC1_eq_integral`** : `logTailC1 K = ∫ logTailFn K dγ` (μ is the true mean).
- Integrability of `(logBirkhoffSum K n)²` via `lintegral_iSup` + the uniform bound;
  `integral_tendsto_of_tendsto_of_monotone` for `∫(trunc)²→∫(sum)²`; `le_of_tendsto` to pass the bound.

## The ONE open obligation remains: `ae_tail_average_tendsto K` (`CFAeKhinchin.lean:971`, sole live sorry)
feeding `ae_khinchinTypical` (`+sorryAx`) ⇒ image-Khinchin headline.

## NEXT (hardest-first) — brick 5 + graft
5. **`chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto`**: TRANSCRIBE `chebyshev_blockCount`
   (`CFBlockFreq.lean`, Markov on `(S−nμ)²`) using the new `variance_logBirkhoffSum_le`, then the
   FULL L²→a.e. skeleton `ae_orbit_freq` (`CFAeNormal.lean:81`): bad sets `E m k` on `p=(k+1)²`,
   per-`m` summability via Chebyshev, Borel–Cantelli `ae_eventually_notMem`, subsequence limit,
   monotone gap-squeeze. Substitutions: `blockCount A p ↦ logBirkhoffSum K p`, `γv ↦ logTailC1 K`
   (= `∫ logTailFn K` via `logTailC1_eq_integral`), variance const `(8|v|+80)γv ↦ logVarConst K`.
   Monotone gap-squeeze available: `logBirkhoffSum K n` ↑ in n (`logTailFn K ≥ 0`) +
   `logBirkhoffSum_nonneg` (both `CFLogTail`).
6. **Graft**: `ae_khinchinTypical` becomes axiom-clean; intersect its co-null set into
   `exists_cfNormal_and_affine_family_cfNormal'` ⇒ image-Khinchin headline. Re-`#print axioms` clean.

The two other `src/` sorries (`CFScheduleA.lean:4400`, `:5774`) are DEAD/REFUTED schedule code —
directive-FORBIDDEN, leave untouched.
